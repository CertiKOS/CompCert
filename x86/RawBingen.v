Require Import Coqlib Integers Floats AST Maps.
Require Import Errors.
Require Import SegAsm FlatProgram FlatBinary RawBinary.
Require Import Hex ElfLayout Memdata String.
Import ListNotations.
Import Hex.

Local Open Scope hex_scope.
Local Open Scope error_monad_scope.

(** * Generation of raw binary from FlatBinary programs *)

(** Collect the instruction bytes *)  
Fixpoint accum_instrs (defs: list (ident * option FlatBinary.gdef)) :=
  match defs with
  | nil => []
  | (id, def) :: defs' =>
    let code := 
        match def with
        | Some (Gfun (Internal f)) => (fn_code f)
        | _ => []
        end in
    code ++ (accum_instrs defs')
  end.

(** Create staring stub code with nops filled in *)
Definition gen_nops (n:nat) : list byte :=
  List.map (fun _ => HB["90"]) (seq 1 n).

Definition create_start_stub' (main_ofs: ptrofs) :=
  let size_nops := (alignw startstub_size) - startstub_size in
  let nops_bytes := gen_nops (Z.to_nat size_nops) in
  (create_start_stub (Ptrofs.unsigned main_ofs)) ++ nops_bytes.

(** Generate the complete instruction bytes by appending starting stub code
    to instructions *)
Definition gen_instrs (p:FlatBinary.program) : res (list byte) :=
  let code_sz := FlatProgram.prog_code_size p in
  let main_rofs := 
      Ptrofs.sub (FlatProgram.prog_main_ofs p) 
                 (Ptrofs.add (FlatProgram.prog_code_size p) (Ptrofs.repr call_size)) in
  let ssbytes := create_start_stub' main_rofs in
  let isbytes := accum_instrs (prog_defs p) in
  OK (isbytes ++ ssbytes).

  (* if zeq (Ptrofs.unsigned code_sz) (Z.of_nat (List.length isbytes)) then *)
  (*   OK (isbytes ++ ssbytes) *)
  (* else *)
  (*   let code_sz := Z_to_hex_string 32 (Ptrofs.unsigned code_sz) in *)
  (*   let instr_sz := Z_to_hex_string 32 (Z.of_nat (List.length isbytes)) in *)
  (*   Error (msg ("The size of generated instruction (" ++ instr_sz ++ *)
  (*               ") does not match the size of the code segment (" ++ code_sz ++ ").")). *)


(** Generation of data bytes *)
Definition n_zeros (n:nat) : list byte :=
  List.map (fun _ => Byte.zero) (seq 1 n).

Definition transl_init_data (idata: AST.init_data) : res (list byte) :=
  match idata with
  | Init_int8 i => OK [Byte.repr (Int.unsigned i)]
  | Init_int16 i => OK (encode_int 2 (Int.unsigned i))
  | Init_int32 i => OK (encode_int 4 (Int.unsigned i))
  | Init_int64 i => OK (encode_int 8 (Int64.unsigned i))
  | Init_float32 f => OK (encode_int 4 (Int64.unsigned (Float.to_bits (Float.of_single f))))
  | Init_float64 f => OK (encode_int 4 (Int64.unsigned (Float.to_bits f)))
  | Init_space n => OK (n_zeros (nat_of_Z n))
  | Init_addrof id ofs => Error (msg "Pointers in init data is not supported for now.")
  end.

Fixpoint transl_init_data_list (data: list AST.init_data) :=
  match data with
  | nil => OK nil
  | d :: data' => 
    do dbytes <- transl_init_data d;
    do dlbytes <- transl_init_data_list data';
    OK (dbytes ++ dlbytes)
  end.

(** Translate the initial data and fill in blank areas with 0s *)
Definition transl_init_data' (actual_size: ptrofs) (data: list AST.init_data) :=
  do bytes <- transl_init_data_list data;
    let sz := (Ptrofs.unsigned actual_size) - (AST.init_data_list_size data) in
    OK (bytes ++ (n_zeros (Z.to_nat sz))).


Fixpoint accum_init_data (defs: list (ident * option FlatBinary.gdef)) : res (list byte) :=
  match defs with
  | nil => OK []
  | (id, def) :: defs' =>
    do data <- 
       match def with
       | Some (Gvar v) => 
         transl_init_data' (data_actual_size (AST.gvar_info v)) (AST.gvar_init v)
       | _ => OK []
       end;
    do data' <- accum_init_data defs';
    OK (data ++ data')
  end.

(** Translation of a program *)
Definition transf_program (p:FlatBinary.program) : res program := 
  do prog_code <- gen_instrs p;
  do prog_data <- accum_init_data (FlatProgram.prog_defs p);
  OK ({|
         prog_code := prog_code;
         prog_data := prog_data;
         prog_entry := Ptrofs.add (FlatProgram.prog_code_addr p)
                                  (FlatProgram.prog_code_size p);
         prog_data_addr := (FlatProgram.prog_data_addr p);
         prog_data_size := (FlatProgram.prog_data_size p);
         prog_code_addr := (FlatProgram.prog_code_addr p);
         prog_code_size := (Ptrofs.repr (text_seg_size 
                                         (Ptrofs.unsigned (FlatProgram.prog_code_size p))));
       |}).
