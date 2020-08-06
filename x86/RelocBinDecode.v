                                                                                    




(* *******************  *)
(* Author: Xiangzhe Xu  *)
(* Date:    Oct 1, 2019 *)
(* *******************  *)






Require Import Coqlib Integers AST Maps.
Require Import Asm.
Require Import Errors.
Require Import Memtype.
(* Require Import FlatProgram FlatAsm FlatBinary. *)
Require Import Hex Bits Memdata.
Import ListNotations.
Import Hex Bits.
Require Import RelocBingen RelocProgram SeqTable Encode.
Require Import Reloctablesgen.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.


(** To be implemented and proved by Xu XiangZhe *)
(* Parameter fmc_instr_decode : FlatBinary.instruction -> res FlatAsm.instruction. *)

Section PRESERVATION.


  Variable rtbl_ofs_map: reloc_ofs_map_type.

  
  (* Variable relocTable : reloctable_map. *)

  (* Variable symtbl : symbtable. *)

  Definition find_ofs_in_rtbl (ofs:Z): option (relocentry)
    := ZTree.get ofs rtbl_ofs_map.

  (* Definition get_nth_symbol (n:N)
    := SymbTable.get n symtbl. *)

  
      
  (* Variable allCode : list byte. *)

(* Hypothesis RELOC_TABLE: *)
(*   (PTree.get sec_code_id relocTables) = Some textRelocTable. *)



(* Fixpoint find_ofs_in_reloct_aux (table :list relocentry) (ofs:Z): option (relocentry) := *)
(*   match table with *)
(*   |nil => None *)
(*   |h::tail => if Z.eq_dec (reloc_offset h)  ofs then *)
(*                 Some h *)
(*               else *)
(*                 find_ofs_in_reloct_aux tail ofs *)
(*   end. *)


(* Definition find_ofs_in_RelocTable (ofs:Z) := *)
(*   find_ofs_in_reloct_aux textRelocTable ofs. *)

(* Definition get_current_ofs (mc: list byte) := *)
(*   Z.of_nat (length (allCode) - length (mc)). *)

  
(* utils *)


Fixpoint sublist {X:Type} (lst: list X) (n: nat){struct n}: res (list X) :=
  match lst with
  |nil => match n with
          |O => OK nil
          |S n' => Error(msg"Sublist error")
          end
  |h::t => match n with
           |O => OK nil
           |S n' =>
            do tail <- sublist t n';
            OK (h::tail)
           end
  end.

Fixpoint remove_first_n  {X:Type} (lst: list X) (n: nat) {struct n} : res(list X) :=
  match n with
  | O => OK lst
  | S n' =>
    match lst with
    | nil => Error(msg"remove first error") 
    | h :: t => remove_first_n t n'
    end
  end.

Fixpoint get_n {X:Type} (lst: list X) (n: nat): res X :=
  match lst with
  |nil => Error (msg "list index out of bound")
  |h::t => match n with
           |O => OK(h)
           | S n' => get_n lst n'
           end
  end.

Definition decode_int_n (lst: list byte)(n: nat): res Z :=
  do int_bytes <- (sublist lst n);
    OK(decode_int int_bytes).

Compute (decode_int_n [HB["00"];HB["00"];HB["00"];HB["80"]] 2).

(* parse the reg *)
Definition addrmode_parse_reg(reg: byte): res(ireg) :=
  if Byte.eq_dec reg (Byte.repr 0) then OK(RAX)
  else if Byte.eq_dec reg (Byte.repr   1) then OK(RCX)
  else if Byte.eq_dec reg (Byte.repr   2) then OK(RDX)
  else if Byte.eq_dec reg (Byte.repr   3) then OK(RBX)
  else if Byte.eq_dec reg (Byte.repr   4) then OK(RSP)
  else if Byte.eq_dec reg (Byte.repr   5) then OK(RBP)
  else if Byte.eq_dec reg (Byte.repr   6) then OK(RSI)
  else if Byte.eq_dec reg (Byte.repr   7) then OK(RDI)
  else Error(msg "reg not found").

Compute (addrmode_parse_reg (Byte.repr 2)).

(* parse SIB *)

(* parse the scale *)
Definition addrmode_SIB_parse_scale(ss: byte): res(Z) :=
  if Byte.eq_dec ss (Byte.repr 0) then OK(1)
  else if Byte.eq_dec ss (Byte.repr 1) then OK(2)
       else if Byte.eq_dec ss (Byte.repr 2) then OK(4)
            else if Byte.eq_dec ss (Byte.repr 3) then OK(8)
                 else Error(msg "Scale not found").

Compute (addrmode_SIB_parse_scale (Byte.repr 2)).

(* parse index utility *)

Definition addrmode_SIB_parse_index (idx: byte)(index: ireg) (s: Z): option (ireg * Z):=
  if Byte.eq_dec idx HB["4"] then
    None
  else
    Some (index, s).

(* parse base utility *)

Definition addrmode_SIB_parse_base (mode_b: byte)(base: ireg)(bs : byte)(mc:list byte) : res ((option ireg) * ptrofs) :=
  if Byte.eq_dec bs HB["5"] then
    if Byte.eq_dec mode_b HB["0"] then
      do ofs <- decode_int_n mc 4;
        (* no base, offset 32 *)
        OK(None, Ptrofs.repr ofs)
    else
      if Byte.eq_dec mode_b HB["1"] then
        do ofs <- decode_int_n mc 1;
          (* offset 8 *)
          OK(Some base, Ptrofs.repr ofs)
      else
        if Byte.eq_dec mode_b HB["2"] then
          do ofs <- decode_int_n mc 4;
            (* offset 32 *)
            OK(Some base, Ptrofs.repr ofs)
        else
          (* error *)
          Error(msg "error in parse sib base")
  else
    if Byte.eq_dec mode_b HB["0"] then
      (* no offset *)
      OK(Some base, Ptrofs.repr 0)
    else
      if Byte.eq_dec mode_b HB["1"] then
        do ofs <- decode_int_n mc 1;
          (* offset 8 *)
          OK(Some base, Ptrofs.repr ofs)
      else
        if Byte.eq_dec mode_b HB["2"] then
          do ofs <- decode_int_n mc 4;
            (* offset 32 *)
            OK(Some base, Ptrofs.repr ofs)
        else
          (* error *)
          Error(msg "error in parse sib base").
                         

(* parse the size of the addrmode from modrm, disp not inlcuded*)
Definition decode_addrmode_size (mc: list byte): res (Z) :=
   match mc with
   |nil => Error(msg "Addr mode is null")
   |h::t=> let MOD := Byte.shru h (Byte.repr 6) in
           let REG := Byte.shru (Byte.and h (Byte.repr 56)) (Byte.repr 3) in
           let RM := Byte.and h (Byte.repr 7) in

           if Byte.eq_dec MOD (Byte.repr 3) then
             OK 1
           else
             if Byte.eq_dec RM (Byte.repr 4) then
               OK 2
             else
               OK 1
   end.
(* parse the sib *)
(* rofs is the offset of disp *)
Definition addrmode_parse_SIB (rofs: Z)(sib: byte)(mod_b: byte)(mc:list byte): res(addrmode * (list byte)) :=
  let idx := ( Byte.shru (Byte.and sib (Byte.repr 56)) (Byte.repr 3)) in
  let ss :=  (Byte.shru sib (Byte.repr 6)) in
  let bs := (Byte.and sib (Byte.repr 7)) in  
  do index <- addrmode_parse_reg idx;
    do scale <- addrmode_SIB_parse_scale ss;
    do base <- addrmode_parse_reg bs;
    do base_offset <- addrmode_SIB_parse_base mod_b base bs mc;
    let index_s := addrmode_SIB_parse_index idx index scale in
    let optionalRelEntry := find_ofs_in_rtbl (rofs) in
    match optionalRelEntry with
    |None =>
     if Byte.eq_dec mod_b HB["0"]  then
       if Byte.eq_dec bs HB["5"] then
         do remains <- (remove_first_n mc 4);
         OK(Addrmode (fst base_offset) (index_s) (inl (Ptrofs.unsigned (snd base_offset))),remains)
       else
         OK(Addrmode (fst base_offset) (index_s) (inl (Ptrofs.unsigned (snd base_offset))),mc)
     else
       OK(Addrmode (fst base_offset) (index_s) (inl (Ptrofs.unsigned (snd base_offset))),mc)
    |Some relEntry =>
     if Byte.eq_dec mod_b HB["0"]  then
       if Byte.eq_dec bs HB["5"] then
         do remains <- (remove_first_n mc 4);
           OK(Addrmode (fst base_offset) (index_s) (inr (xH, (snd base_offset))),remains)
       else
         OK(Addrmode (fst base_offset) (index_s) (inr (xH, (snd base_offset))),mc)
     else
       OK(Addrmode (fst base_offset) (index_s) (inr (xH, (snd base_offset) )),mc)
    end.


(* decode addr mode *)
(* rofs is the offset of the disp  *)
Definition decode_addrmode (rofs:Z) (mc:list byte): res(ireg * addrmode * (list byte)):=
  match mc with
  |nil => Error(msg "Addr mode is null")
  |h::t=> let MOD := Byte.shru h (Byte.repr 6) in
          let REG := Byte.shru (Byte.and h (Byte.repr 56)) (Byte.repr 3) in
          let RM := Byte.and h (Byte.repr 7) in
          do reg <-addrmode_parse_reg REG;
            if Byte.eq_dec MOD HB["0"] then
              do ea_reg <- addrmode_parse_reg RM;
                if Byte.eq_dec RM HB["4"] then
                  do sib <- get_n t 0;
                    (* modrm + sib *)
                    do rm_modrm <- (remove_first_n t 1);
                    do result <- addrmode_parse_SIB (rofs) sib MOD rm_modrm;
                    OK(reg, fst result, snd result)
                else if Byte.eq_dec RM HB["5"] then
                       do ofs <- decode_int_n t 4;
                       (* modrm + disp32 *)
                       let optRelocEntry := find_ofs_in_rtbl (rofs) in
                       match optRelocEntry with
                       |None =>
                        do remains <- remove_first_n t 4;
                        OK(reg, Addrmode None None (inl ofs),remains)
                       |Some relocEntry =>
                        do remains <- remove_first_n t 4;
                          OK(reg, Addrmode None None (inr (xH , Ptrofs.repr ofs )), remains)                         
                       end
                     else
                       OK(reg, Addrmode (Some ea_reg) None (inl 0), t)
            else if Byte.eq_dec MOD HB["1"] then
                   do ea_reg <- addrmode_parse_reg RM;
                     if Byte.eq_dec RM HB["4"] then
                       do sib <- get_n t 0;
                         (* modrm+sib *)
                         do rm_modrm <- (remove_first_n t 1);
                         do result <- addrmode_parse_SIB (rofs) sib MOD rm_modrm;
                         do remains <- remove_first_n (snd result) 1;
                            OK(reg, fst result, remains)
                     else
                       do ofs <- decode_int_n t 1;
                     (* only one byte of offset, could not be addend for relocation *)
                     do remains <- remove_first_n t 1;
                       OK(reg, Addrmode (Some ea_reg) None (inl ofs), remains )
                 else if Byte.eq_dec MOD HB["2"] then
                        do ea_reg <- addrmode_parse_reg RM;
                          if Byte.eq_dec RM HB["4"] then
                            do sib<- get_n t 0;                                                 (* modrm + sib *)
                              do rm_modrm <- (remove_first_n t 1);
                              do result <- addrmode_parse_SIB (rofs) sib MOD rm_modrm;
                              do remains <- remove_first_n (snd result) 4;
                                 OK(reg, fst result, remains)
                          else
                            (* modrm + disp32 *)
                            do ofs <- decode_int_n t 4;
                            let optRelocEntry := find_ofs_in_rtbl (rofs) in
                            match optRelocEntry with
                            |None =>
                             do remains <- remove_first_n t 4;
                               OK(reg, Addrmode (Some ea_reg) None (inl ofs), remains)
                            |Some relocEntry =>
                             do remains <- remove_first_n t 4;
                               OK(reg, Addrmode (Some ea_reg) None (inr (xH, Ptrofs.repr ofs)), remains)        
                            end                            
                      else
                        Error( msg "unknown address mode")
  end.


(* parse instructions *)


(* common routines *)

Definition decode_rr_operand (modrm: byte): res(ireg * ireg) :=
   do rd <- addrmode_parse_reg (Byte.shru (Byte.and modrm HB["38"]) HB["3"]);
     do rs <- addrmode_parse_reg (Byte.and modrm HB["7"]);
     OK(rd,rs).

(* decode instructions *)

Definition decode_jmp_l_rel (mc: list byte) : res (instruction * list byte):=
  do ofs <- decode_int_n mc 4;
    do remains <- remove_first_n mc 4;
    OK(Pjmp_l_rel ofs, remains).



Definition decode_jcc_rel (mc: list byte) : res (instruction * list byte):=
  do rm_opcode <- (remove_first_n mc 1);
    do ofs <- (decode_int_n rm_opcode 4);
    do cond <- get_n mc 0;
    do remains <- remove_first_n mc 5;
  if Byte.eq_dec cond HB["84"] then OK(Pjcc_rel Cond_e ofs, remains)
  else if Byte.eq_dec cond HB["85"] then OK(Pjcc_rel Cond_ne ofs, remains)
  else if Byte.eq_dec cond HB["82"] then OK(Pjcc_rel Cond_b ofs, remains)
  else if Byte.eq_dec cond HB["86"] then OK(Pjcc_rel Cond_be ofs, remains)
  else if Byte.eq_dec cond HB["83"] then OK(Pjcc_rel Cond_ae ofs, remains)
  else if Byte.eq_dec cond HB["87"] then OK(Pjcc_rel Cond_a ofs, remains)
  else if Byte.eq_dec cond HB["8C"] then OK(Pjcc_rel Cond_l ofs, remains)
  else if Byte.eq_dec cond HB["8E"] then OK(Pjcc_rel Cond_le ofs, remains)
  else if Byte.eq_dec cond HB["8D"] then OK(Pjcc_rel Cond_ge ofs, remains)
  else if Byte.eq_dec cond HB["8F"] then OK(Pjcc_rel Cond_g ofs, remains)
  else if Byte.eq_dec cond HB["8A"] then OK(Pjcc_rel Cond_p ofs, remains)
  else if Byte.eq_dec cond HB["8B"] then OK(Pjcc_rel Cond_np ofs, remains)
       else Error (msg "Unknown jcc condition").

Compute (decode_rr_operand HB["D8"]).

Definition decode_imull_rr (mc: list byte) : res (instruction * list byte):=
  do modrm <- get_n mc 0;
    do rds <- decode_rr_operand modrm;
    do remains <- remove_first_n mc 1;
    OK(Pimull_rr (fst rds) (snd rds), remains).

Definition decode_imull_ri (mc: list byte) : res (instruction * list byte):=
  do modrm <- get_n mc 0;
    do rd <- addrmode_parse_reg (Byte.and modrm HB["7"]);
    do rm_modrm <- (remove_first_n mc 1);
    do n <- decode_int_n rm_modrm 4;
    do remains <- remove_first_n mc 5;
      OK(Pimull_ri rd (Int.repr n), remains).
    

Definition decode_0f (mc: list byte): res(instruction * list byte):=
  do code <- get_n mc 0;
    if Byte.eq_dec  code HB["AF"] then
      do remains <- (remove_first_n mc 1);
    decode_imull_rr remains
  else
    decode_jcc_rel mc.

Definition decode_call (rofs:Z) (mc: list byte): res(instruction * list byte):=
  do ofs <- (decode_int_n mc 4);
  match find_ofs_in_rtbl (rofs + 1) with
  |None => Error (msg"Call target not found")
  |Some relocEntry =>
   do remains <- remove_first_n mc 4;
     OK(Pcall (inr xH) (mksignature [] None (mkcallconv false false false)),remains )
  end.

Definition decode_leal (rofs:Z) (mc: list byte): res(instruction * list byte):=
  do a_size <- decode_addrmode_size mc;
  do addrs <- decode_addrmode (rofs+a_size+1) mc;
    OK(Pleal (fst (fst addrs)) (snd (fst addrs)), (snd addrs)).


Definition decode_xorl_r (mc: list byte): res(instruction * list byte):=
  do modrm <- get_n mc 0;
    do rd <- addrmode_parse_reg (Byte.and modrm HB["7"]);
    do remains <- remove_first_n mc 1;
       OK(Pxorl_r rd, remains).

(* test_xor begins here *)
(* test_xor ends here *)

Definition decode_addl_ri  (mc: list byte): res(instruction * list byte):=
  do modrm <- get_n mc 0;
    do rd <- addrmode_parse_reg (Byte.and modrm HB["7"]);
    do rm_modrm <- (remove_first_n mc 1);
    do n <- decode_int_n rm_modrm 4;
    do remains <- remove_first_n mc 5;
      OK(Paddl_ri rd (Int.repr n), remains).

(* test add ri begins here *)
(* add eax, 0 *)
Compute (decode_addl_ri  [HB["C0"];HB["00"];HB["00"];HB["00"];HB["00"];HB["AA"];HB["BB"]]).

(* test add ri ends here *)

Definition decode_subl_ri (mc: list byte): res(instruction * list byte):=
  do modrm <- get_n mc 0;
    do rd <- addrmode_parse_reg (Byte.and modrm HB["7"]);
    do rm_modrm <- (remove_first_n mc 1);
    do n <- decode_int_n rm_modrm 4;
    do remains <- remove_first_n mc 5;
    OK(Psubl_ri rd (Int.repr n), remains).

Definition decode_cmpl_ri (mc: list byte): res(instruction * list byte):=
  do modrm <- get_n mc 0;
    do rd <- addrmode_parse_reg (Byte.and modrm HB["7"]);
    do rm_modrm <- (remove_first_n mc 1);
    do n <- decode_int_n rm_modrm 4;
    do remains <- remove_first_n mc 5;
    OK(Pcmpl_ri rd (Int.repr n), remains).
  
Definition decode_81  (mc: list byte): res(instruction * list byte):=
  do modrm <- get_n mc 0;
    let opcode := Byte.shru (Byte.and modrm HB["38"]) HB["3"] in
    if Byte.eq_dec opcode HB["7"] then decode_cmpl_ri mc
    else if Byte.eq_dec opcode HB["0"] then decode_addl_ri mc
         else if Byte.eq_dec opcode HB["5"] then decode_subl_ri mc
              else Error(msg" instruction begins with 81 cannot be found").
    
Definition decode_subl_rr (mc: list byte): res(instruction * list byte):=
  do modrm <- get_n mc 0;
    do rd <- addrmode_parse_reg (Byte.shru (Byte.and modrm HB["38"]) HB["3"]);
    do rs <- addrmode_parse_reg (Byte.and modrm HB["7"]);
    do remains <- remove_first_n mc 1;
    OK(Psubl_rr rd rs, remains).

(* note that the opcode of movl begins with 0xB, so we can use this info to dispatch this instruction*)
Definition decode_movl_ri  (mc: list byte): res(instruction * list byte):=
  do opcode <- get_n mc 0;
    do rd <- addrmode_parse_reg (Byte.and opcode HB["7"]);
    do rm_opcode <- (remove_first_n mc 1);
    do n <- decode_int_n rm_opcode 4;
    do remains <- remove_first_n mc 5;
    OK(Pmovl_ri rd (Int.repr n), remains).

Definition decode_mov_rr  (mc: list byte): res(instruction * list byte):=
   do modrm <- get_n mc 0;
     do rds <- decode_rr_operand modrm;
     do remains <- remove_first_n mc 1;
    OK(Pmov_rr (fst rds) (snd rds), remains).

Definition decode_movl_rm (rofs:Z) (mc: list byte): res(instruction * list byte):=
  do a_size <- decode_addrmode_size mc;
  do addrs <- decode_addrmode (rofs+a_size+1) mc;
    OK(Pmovl_rm (fst (fst addrs)) (snd (fst addrs)), (snd addrs)).

Definition decode_movl_mr (rofs:Z) (mc: list byte): res(instruction * list byte):=
  do a_size <- decode_addrmode_size mc;
  do addrs <- decode_addrmode (rofs+a_size+1) mc;
    OK(Pmovl_mr  (snd (fst addrs)) (fst (fst addrs)), (snd addrs)).

Definition decode_movl_rm_a (rofs:Z) (mc: list byte): res(instruction * list byte):=
  do a_size <- decode_addrmode_size mc;
  do addrs <- decode_addrmode (rofs+a_size+1) mc;
    OK(Pmov_rm_a (fst (fst addrs)) (snd (fst addrs)), (snd addrs)).

Definition decode_movl_mr_a (rofs:Z) (mc: list byte): res(instruction * list byte):=
  do a_size <- decode_addrmode_size mc;
  do addrs <- decode_addrmode (rofs+a_size+1) mc;
    OK(Pmov_mr_a  (snd (fst addrs)) (fst (fst addrs)), (snd addrs)).

Definition decode_testl_rr  (mc: list byte): res(instruction * list byte):=
  do modrm <- get_n mc 0;
    do rds <- decode_rr_operand modrm;
    do remains <- remove_first_n mc 1;
    OK(Ptestl_rr (fst rds) (snd rds), remains).

Definition decode_cmpl_rr   (mc: list byte): res(instruction * list byte):=
  do modrm <- get_n mc 0;
    do rds <- decode_rr_operand modrm;
    do remains <- remove_first_n mc 1;
    OK(Pcmpl_rr (snd rds) (fst rds), remains).

Definition decode_idivl  (mc: list byte): res(instruction * list byte):=
  do modrm <- get_n mc 0;
    do rd <- addrmode_parse_reg (Byte.and modrm HB["7"]);
    do remains <- remove_first_n mc 1;
    OK(Pidivl rd, remains).

Definition decode_sall_ri (mc: list byte): res(instruction * list byte):=
  do modrm <- get_n mc 0;
    do rd <- addrmode_parse_reg (Byte.and modrm HB["7"]);
    do rm_modrm <- (remove_first_n mc 1);
    do n <- decode_int_n rm_modrm 1;
    do remains <- remove_first_n mc 2;
    OK(Psall_ri rd (Int.repr n), remains).

Definition decode_8b (rofs:Z) (mc: list byte): res(instruction * list byte):=
  do modrm <- get_n mc 0;
    if Byte.eq_dec (Byte.and modrm HB["C0"]) HB["C0"] then
      decode_mov_rr mc
    else
      decode_movl_rm rofs mc.

(*Parameter fmc_instr_decode: list byte -> res (FlatAsm.instruction * list byte).*)

Definition fmc_instr_decode (rofs:Z) (mc: list byte) : res (instruction * list byte):=
    match mc with
    | nil => Error(msg "Nothing to decode")
    | h::t => if Byte.eq_dec h HB["90"] then OK(Pnop,t)
              else if Byte.eq_dec h HB["E9"] then decode_jmp_l_rel t
              else if Byte.eq_dec h HB["0F"] then decode_0f t
              else if Byte.eq_dec h HB["E8"] then decode_call rofs t
              else if Byte.eq_dec h HB["8D"] then decode_leal rofs t
              else if Byte.eq_dec h HB["31"] then decode_xorl_r t
              else if Byte.eq_dec h HB["81"] then decode_81 t
              else if Byte.eq_dec h HB["2B"] then decode_subl_rr t
              else if Byte.eq_dec (Byte.and h HB["F0"]) HB["B0"] then decode_movl_ri mc
              else if Byte.eq_dec h HB["8B"] then decode_8b rofs t
              else if Byte.eq_dec h HB["89"] then decode_movl_mr rofs t
              else if Byte.eq_dec h HB["85"] then decode_testl_rr t
              else if Byte.eq_dec h HB["C3"] then OK(Pret,t)
              else if Byte.eq_dec h HB["69"] then decode_imull_ri t
              else if Byte.eq_dec h HB["39"] then decode_cmpl_rr t
              else if Byte.eq_dec h HB["99"] then OK(Pcltd,t)
              else if Byte.eq_dec h HB["F7"] then decode_idivl t
              else if Byte.eq_dec h HB["C1"] then decode_sall_ri t
                   (* else decode_testl_rr mc *)
                   else Error(msg "Unknown opcode!")
    end.






Definition instr_eq (ins1 ins2: instruction): Prop :=
  match ins1 with
(*  |Fjmp_l ofs => match ins2 with
                 |Fjmp_l ofs2 => ofs = ofs2
                 |_ => False
                 end
  |Fjcc c ofs => match ins2 with
                 |Fjcc c2 ofs2 => c=c2 /\ ofs = ofs2
                 |_ => False
                 end                                          *)
  |Pcall ofs _ => match ins2 with
                       |Pcall ofs2 _ => ofs = ofs2
                       |_ => False
                       end

  |Pmov_rm_a rd a => match ins2 with
                     |Pmovl_rm rd2 a2 => rd2=rd /\ a=a2
                     |_ => False
                     end
  |Pmov_mr_a a rs => match ins2 with
                     |Pmovl_mr a2 rs2 => rs=rs2 /\ a=a2
                     |_ => False
                     end
  |Ptestl_rr r1 r2=> match ins2 with
                     |Ptestl_rr r3 r4 => (r1=r3/\r2=r4)\/(r1=r4/\r2=r3)
                     |_ => False
                     end
  |Psall_ri rd n => match ins2 with
                    |Psall_ri rd2 n2 => rd2=rd /\ (Int.repr (Int.unsigned n mod Byte.modulus)) = n2
                    |_ => False
                    end
  |Plabel _ => match ins2 with
               |Plabel _ => True
               |Pnop => True
               |_ => False
               end
  |Pnop => match ins2 with
           |Plabel _ => True
           |Pnop => True
           |_ => False
           end
  |Pmov_rs rd id => (Pmovl_rm rd (Addrmode None None (inr (id,Ptrofs.zero)))) = ins2                    
  |_ => ins1 = ins2
  end.



Lemma remove_first_prefix: forall {A} (l1:list A) l2 n,
    List.length l1 = n -> remove_first_n (l1 ++ l2) n = OK l2.
Proof.
  induction l1; simpl; subst.
  - intros. subst. simpl. auto.
  - intros. subst. simpl. auto.
Qed.


Lemma encode_int32_size : forall ofs, List.length (encode_int32 (Ptrofs.unsigned ofs)) = 4%nat.
Proof.
  intros. unfold encode_int32.
  rewrite encode_int_length. auto.
Qed.

Lemma encode_int32_size_Z :forall n, List.length (encode_int32 n) = 4%nat.
Proof.
  intros. unfold encode_int32. rewrite encode_int_length. auto.
Qed.


Lemma remove_prefix_byte: forall l ofs,
    remove_first_n (encode_int32 (Ptrofs.unsigned ofs) ++l) 4 = OK l.
Proof.
  intros.
  generalize (encode_int32_size ofs). intro ECSize.
  apply remove_first_prefix. auto.
Qed.

Lemma zero_length_list: forall {X} (l:list X),
    List.length l = 0%nat -> l = nil.
Proof.
  intros. subst. destruct l eqn:EQ.
  - auto.
  - inversion H.
Qed.

(* Lemma sublist_prefix: forall {X} n (l1:list X) l2, *)
(*     List.length l1 = n -> sublist (l1++l2) n = l1. *)
(* Proof. *)
(*   induction n; intros. *)
(*   - rewrite zero_length_list; auto. *)
(*     simpl. destruct (l1 ++ l2); auto. *)
(*   - destruct l1; simpl in *. congruence. *)
(*     inversion H; subst. f_equal. auto. *)
(* Qed. *)


Lemma sublist_prefix: forall {X} (l1:list X) l2,
    sublist (l1++l2) (length l1) = OK l1.
Proof.
  induction l1; intros.
  - simpl in *. subst. simpl. destruct l2; auto. 
  - simpl in *.
    unfold bind.
    rewrite (IHl1 l2). auto.
Qed.

(* Lemma sublist_prefix: forall {X} (l1:list X) n l2, *)
(*     List.length l1 = n -> sublist (l1++l2) n = l1. *)
(* Proof. *)
(*   induction l1; intros. *)
(*   - simpl in *. subst. simpl. destruct l2; auto.  *)
(*   - simpl in *. subst. simpl. f_equal. auto. *)
(* Qed. *)

Lemma sublist_id: forall {X} (l: list X),
    sublist l (length l) = OK l.
Proof.
  induction l.
  - simpl. auto.
  - unfold sublist.
    simpl. unfold sublist in IHl. rewrite IHl.
    auto.
Qed.

Lemma decode_prefix: forall n l1 l2,
    List.length l1 = n -> decode_int_n (l1++l2) n = decode_int_n l1 n.
Proof.
  intros. subst. unfold decode_int_n. rewrite  (sublist_prefix l1 l2).
  rewrite sublist_id. auto.
Qed.

(* Lemma encode_decode_int32_int2Z : forall x, *)
(*     Int.repr decode_int(encode_int 4 x) = Int.repr x. *)
(* Proof. *)
(*   intros.  rewrite <- decode_encode_int_4. f_equal. *)
(*   f_equal. f_equal. rewrite (Int.unsigned_repr_eq x). unfold Int.modulus. *)
(*   unfold Int.wordsize. unfold Wordsize_32.wordsize. *)
(*   unfold two_power_nat. *)

Check Int.unsigned.
Check Int.repr.
Print Z.

Definition valid_int32 (i:Z) := 0 <= i < two_power_pos 32.
           
Lemma encode_decode_int32_int2Z : forall x,
  valid_int32 x -> decode_int(encode_int 4 x) = x.
Proof.
  intros. rewrite decode_encode_int.
  simpl.
  apply Zmod_small; auto.
  
Qed.
  
Lemma encode_decode_int32_same: forall n,
    valid_int32 n -> decode_int_n (encode_int32 n) 4 = OK n.
Proof.
  intros. subst. unfold decode_int_n. rewrite sublist_id.
  unfold encode_int32.
  simpl.
  f_equal.
  apply encode_decode_int32_int2Z. apply H.
Qed.

Lemma encode_decode_int32_same_prefix : forall n l,
    valid_int32 n -> (decode_int_n ((encode_int32 n) ++ l) 4) = OK n.
Proof.
  intros. rewrite <- (encode_int32_size_Z n).
  rewrite decode_prefix.
  - rewrite encode_int32_size_Z. rewrite (encode_decode_int32_same n);auto.
  - auto.
Qed.
         
(* Lemma encode_decode_same : forall i bytes, *)
(*     fmc_instr_encode i = OK bytes *)
(*     -> forall l, exists i', fmc_instr_decode (bytes ++ l) = OK (i', l) /\ instr_eq i i'. *)

Lemma byte_eq_true: forall (A : Type) (x : byte) (a b : A),
    (if Byte.eq_dec x x then a else b) = a.
Proof.
  intros. destruct (Byte.eq_dec x x) eqn:EQ.
  - auto.
  - inversion EQ. elim n. auto.
Qed.

Lemma byte_eq_false: forall (A : Type) (x y : byte) (a b : A),
    x <> y -> (if Byte.eq_dec x y then a else b) = b.
Proof.
  intros. destruct (Byte.eq_dec x y) eqn:EQ.
  - rewrite e in H. elim H. auto.
  - auto.
Qed.


Ltac prove_byte_neq :=
  let EQ := fresh "EQ" in (
    match goal with
    | [ |- Byte.repr ?a <> Byte.repr ?b ] =>
      now (intro EQ; inversion EQ)
    end).

Ltac branch_byte_eq :=
    match goal with
    | [ |- (if Byte.eq_dec _ _ then _ else _) = OK _] =>
      repeat (rewrite byte_eq_false; [ idtac | prove_byte_neq ]);
      rewrite byte_eq_true
    end.

Ltac prove_byte_and_neq :=
  now (unfold Byte.and;
       repeat (rewrite Byte.unsigned_repr; [ |unfold Byte.max_unsigned; simpl; omega]);
       simpl;
       prove_byte_neq).

Ltac prove_opcode_neq :=
  match goal with
  | [ EQ: encode_ireg ?rd = OK _ |- _ ] =>
    now (case rd eqn:EQR; unfold encode_ireg in EQ; inversion EQ; simpl; unfold not; intros H; inversion H)
  end.

Ltac branch_byte_eq' :=
  match goal with
  | |- (if Byte.eq_dec (Byte.and _ _) (Byte.repr _) then _ else _) = OK _ =>
    rewrite byte_eq_false; [ branch_byte_eq' | prove_byte_and_neq ]    
  | |- (if Byte.eq_dec _ _ then _ else _) = OK _ =>
    rewrite byte_eq_false; [ branch_byte_eq' | try prove_byte_neq; prove_opcode_neq ]
  | |- (if Byte.eq_dec ?a ?a then _ else _) = OK _ =>
    rewrite byte_eq_true
  | _ => idtac
  end.


Lemma encode_decode_ireg_refl: forall reg l,
    encode_ireg reg = OK l ->
    exists reg1,  addrmode_parse_reg bB[l] = OK reg1 /\ reg1 = reg.
Proof.
  intros. subst. unfold encode_ireg in H.
  case reg eqn:EQR.
  - intros. inversion H. unfold addrmode_parse_reg. exists RAX. split; auto; branch_byte_eq; auto.
  - intros. inversion H. unfold addrmode_parse_reg. exists RBX. split; auto; branch_byte_eq; auto.
  - intros. inversion H. unfold addrmode_parse_reg. exists RCX. split; auto; branch_byte_eq; auto.
  - intros. inversion H. unfold addrmode_parse_reg. exists RDX. split; auto; branch_byte_eq; auto.
  - intros. inversion H. unfold addrmode_parse_reg. exists RSI. split; auto; branch_byte_eq; auto.
  - intros. inversion H. unfold addrmode_parse_reg. exists RDI. split; auto; branch_byte_eq; auto.
  - intros. inversion H. unfold addrmode_parse_reg. exists RBP. split; auto; branch_byte_eq; auto.
  - intros. inversion H. unfold addrmode_parse_reg. exists RSP. split; auto; branch_byte_eq; auto.
  - intros. inversion H. - intros. inversion H. - intros. inversion H. - intros. inversion H.
  - intros. inversion H. - intros. inversion H. - intros. inversion H. - intros. inversion H.
Qed.
 
Lemma ex_encode_ireg: forall x r,
    encode_ireg r = OK x -> exists b, x = b /\ List.length b = 3%nat.
Proof.
  intros. unfold encode_ireg in H.
  case r eqn:EQR; inversion EQR; inversion H.
  - exists b["000"]. split.
    + inversion H. simpl. auto. + auto.
  - exists b["011"]. split.
    + inversion H. simpl. auto. + auto.
  - exists b["001"]. split.
    + inversion H. simpl. auto. + auto.
  - exists b["010"]. split.
    + inversion H. simpl. auto. + auto.
  - exists b["110"]. split.
    + inversion H. simpl. auto. + auto.
  - exists b["111"]. split.
    + inversion H. simpl. auto. + auto.
  - exists b["101"]. split.
    + inversion H. simpl. auto. + auto.
  - exists b["100"]. split.
    + inversion H. simpl. auto. + auto.
Qed.


Lemma non_zero_len_not_nil : forall (A:Type) (l: list A),
    (length l > 0)%nat -> (l <> nil).
Proof.
  destruct l; simpl.
  - intros. omega.
  - intros H. intro EQ. discriminate.
Qed.


Lemma bits_to_Z_last: forall l a acc,
        bits_to_Z_acc acc (l ++ [a]) = 2 * bits_to_Z_acc acc l  + bool_to_Z a.
Proof.
  induction l; intros.
  - simpl. auto.
  - simpl. apply IHl.
Qed.

Lemma app_cons_comm: forall (A:Type) (l1:list A) a l2,
    (l1 ++ [a]) ++ l2 = l1 ++ a :: l2.
Proof.
  induction l1; intros. 
  - simpl. auto.
  - simpl. f_equal. apply IHl1.
Qed.

Lemma bits_to_Z_app : forall l2 l1 acc,
    bits_to_Z_acc acc (l1++l2) = bits_to_Z_acc (bits_to_Z_acc acc l1) l2.
Proof.
  induction l2; intros.
  - rewrite app_nil_r. simpl. auto.
  - replace (l1 ++ a :: l2) with ((l1 ++ [a]) ++ l2).
    simpl.
    setoid_rewrite <- bits_to_Z_last.
    apply IHl2.
    apply app_cons_comm.
Qed.

Lemma bits_to_Z_prefix: forall bits b,
    bits_to_Z (bits ++ [b]) = 2 * (bits_to_Z bits) + bool_to_Z b.
Proof.
  unfold bits_to_Z. intros.
  rewrite bits_to_Z_app. simpl. auto.
Qed.


Lemma list_len_gt1: forall (A:Type) (l:list A) n,
    length l = S n -> exists l' (t:A), l = l' ++ [t].
Proof.
  intros A0 l n H.
  destruct l.
  + simpl in H. omega.
  + exists (removelast (a::l)).
    exists (last (a::l) a).
    rewrite <- (app_removelast_last a).
    ++ auto.
    ++ apply non_zero_len_not_nil. omega.
Qed.

Lemma encode_decode_int_little_refl: forall i l,
    valid_int32 i -> decode_int_n ((encode_int_little 4 i)++l) 4 = OK i.
Proof.
  intros i l HV.
  unfold encode_int_little.
  unfold decode_int_n.
  rewrite sublist_prefix.
  generalize(decode_encode_int_4 (Int.repr i)).
  intros H.
  unfold encode_int in H.
  rewrite Int.unsigned_repr in H.
  unfold decode_int.
  unfold rev_if_be.
  destruct Archi.big_endian eqn:EQ. inversion EQ.
  cbn [bind]. f_equal.
  rewrite (int_of_bytes_of_int).
  rewrite Z.mod_small. auto.
  unfold valid_int32 in  HV. simpl.
  unfold two_power_pos in HV. simpl in HV. unfold two_power_pos. simpl.
  omega.
  unfold Int.max_unsigned.
  simpl.
  unfold valid_int32 in HV. unfold two_power_pos in HV. simpl in HV. omega.
Qed.

Lemma encode_parse_reg_refl: forall rd x,
    encode_ireg rd = OK x
    ->addrmode_parse_reg bB[x] = OK rd.
Proof.
  intros rd x H.
  case rd eqn:EQR;
  inversion H;
  unfold addrmode_parse_reg;
  branch_byte_eq; auto.
Qed.
  


Lemma encode_parse_scale_refl: forall s b,
    encode_scale s = OK b->
    addrmode_SIB_parse_scale bB[b] = OK s.
Proof.
  intros s.
  intros b HENC.
  unfold encode_scale in HENC.
  case s eqn:EQS;inversion HENC.
  repeat (destruct p; inversion HENC);
  unfold addrmode_SIB_parse_scale; branch_byte_eq; auto.
Qed.


Lemma encode_scale_length: forall s b,
    encode_scale s = OK b ->
    length(b) = 2%nat.
Proof.
  intros s b HENC.
  unfold encode_scale in HENC.
  case s eqn:EQS;inversion HENC.
  repeat (destruct p; inversion HENC);simpl; auto.
Qed.

Lemma encode_reg_length: forall r x,
    encode_ireg r = OK x -> length(x) = 3%nat.
Proof.
   intros. unfold encode_ireg in H.
   case r eqn:EQR; inversion EQR; inversion H;
   simpl;auto.
Qed.


Lemma byte_shru_zero: forall x,
    Byte.shru x (Byte.repr 0) = x.
Proof.
  intros x.
  unfold Byte.shru.
  rewrite Byte.unsigned_repr.
  + unfold Z.shiftr. unfold Z.shiftl. simpl. rewrite Byte.repr_unsigned. auto.
  + unfold Byte.max_unsigned.
    unfold Byte.modulus.
    unfold Byte.wordsize.
    unfold Wordsize_8.wordsize.
    unfold two_power_nat.
    unfold shift_nat. simpl. omega.
Qed.

Lemma bool_to_Z_range: forall t, 0 <= bool_to_Z t <=1.
Proof.
  unfold bool_to_Z.
  destruct t;omega.
Qed.

Lemma bits_to_Z_range: forall n l,
    length l = n -> 0<= bits_to_Z l < two_power_nat (length l).
Proof.
  induction n.
  + intros l.
    intros H.
    rewrite (zero_length_list l).
    split.
    ++ cbn. omega.
    ++ cbn. unfold two_power_nat. simpl.
       omega.
    ++ apply H.
  + split.
    ++ generalize (list_len_gt1 _ l n H).
       intros (l' & t & H10).
       rewrite H10.
       rewrite (bits_to_Z_prefix).
       rewrite H10 in H.
       rewrite app_length in H.
       simpl in H.
       assert(0<= bits_to_Z l' < two_power_nat (length l' ) ) as l'Range. {
         apply( IHn l').
         omega.
       }
       assert(bool_to_Z t >=0) as tRange. {
         unfold bool_to_Z.
         destruct t;omega.
       }
       omega.
    ++ generalize (list_len_gt1 _ l n H).
       intros (l' & t & H10).
       rewrite H10.
       rewrite app_length.
       simpl.
       rewrite bits_to_Z_prefix.
       rewrite H10 in H.
       rewrite app_length in H.
       simpl in H.
       assert(0<= bits_to_Z l' <= two_power_nat (length l' )-1 ) as l'Range. {
         assert(0<= bits_to_Z l' < two_power_nat (length l' ) ) as l'Range. {
           apply (IHn l'). omega.
         }
         omega.
       }
       assert (plus (length l') 1%nat = S (length l')) as Hadd. {
         omega.
       }
       rewrite Hadd.
       rewrite two_power_nat_S.
       generalize (bool_to_Z_range t).
       omega.
Qed.

     

  
Lemma two_power_mono: forall n2 n1,
    ge n1  n2 -> (two_power_nat n1) >= (two_power_nat n2).
Proof.
  induction n2.
  + intros n0 H. unfold two_power_nat. simpl.
    induction n0.
    ++ simpl. omega.
    ++ setoid_rewrite (two_power_nat_S).
       assert(two_power_nat n0 >=1) as basic. {
         assert((n0>=0)%nat) as n0Range. {
           omega.
         }
         unfold two_power_nat.
         apply(IHn0 n0Range).
       }
       omega.
  + intros n1 H.
    induction n1.
    ++ inversion H.
    ++ assert(two_power_nat n1 >= two_power_nat n2) as basic. {
         assert((n1>=n2)%nat) as n1n2. {
           inversion H;omega.
         }
         apply(IHn2 n1 n1n2).
       }
       repeat rewrite two_power_nat_S.
       omega.
Qed.


Lemma div2_discard: forall n b,
    Z.div2 (2*n + bool_to_Z b) = Z.div2 (2*n).
Proof.
  intros. 
  repeat rewrite Zdiv2_div. 
  rewrite (Zdiv_unique _ 2 n (bool_to_Z b)).
  rewrite (Zdiv_unique _ 2 n 0); try omega.
  omega.
  generalize (bool_to_Z_range b).
  omega.
Qed.       
       


Lemma div2_id: forall n,
    Z.div2 (2*n) = n.
Proof.
  intros.
  rewrite Zdiv2_div.
  rewrite (Zdiv_unique _ 2 n 0); omega.
Qed.



Lemma div2_shiftr_eq: forall n l1 b,
    n = length l1 -> Z.div2 ( 2 * bits_to_Z l1 + bool_to_Z b) =  (bits_to_Z l1).
Proof.
  induction n.
  + intros l1 b H.
    rewrite (zero_length_list l1);auto.
    cbn.
    rewrite Zdiv2_div.
    rewrite (Zdiv_unique _ 2 0 (bool_to_Z b));try omega.
    generalize (bool_to_Z_range b).
    omega.
  + intros l1 b H.
    symmetry in H.
    generalize (list_len_gt1 _ l1 n H).
    intros (l' & t & H10).
    rewrite H10.
    rewrite bits_to_Z_prefix.

    generalize(div2_discard  (2 * bits_to_Z l' + bool_to_Z t) b).
    intros H11.
    rewrite H11.
    apply div2_id.
Qed.


Lemma shru_bits: forall n l1 l2,
    le (length(l1++l2)) 8%nat ->
    eq (length(l2)) n ->
    Byte.shru (bB[l1++l2]) (Byte.repr (Z.of_nat n)) = bB[l1].
Proof.
  induction n as [|n']; simpl.
  - intros l1 l2 LE EQ.
    generalize (zero_length_list _ EQ). intro. subst.
    rewrite app_nil_r in *.
    apply byte_shru_zero.

  - intros l1 l2 LE EQ.
    generalize (list_len_gt1 _ _ _ EQ).
    intros (l2' & b & L2). subst.
    rewrite app_assoc.
    unfold Byte.shru.
    (* f_equal. *)
    unfold Z.shiftr.
    unfold Z.shiftl.
    rewrite Byte.unsigned_repr.
    + simpl.
      destruct n' eqn:EQN'.
      ++ simpl.
         assert(l2'=[]) as l2N. {
           rewrite app_length in EQ.
           simpl in EQ.
           destruct (length l2') eqn: EQL.
           + rewrite <- (zero_length_list l2').
             auto. apply EQL.
           + inversion EQ. simpl in H10. omega.
         }
         rewrite l2N. rewrite <- app_assoc. simpl.
         rewrite Byte.unsigned_repr_eq.
         rewrite bits_to_Z_prefix.
         assert( (2 * bits_to_Z l1 + bool_to_Z b) mod Byte.modulus =  (2 * bits_to_Z l1 + bool_to_Z b)) as range. {
           apply Zmod_small.
           rewrite l2N in LE.
           simpl in LE.           
           assert(0<= bits_to_Z l1 < 128) as l1Range. {
             assert (le (length l1) 7%nat) as l1Len. {
               rewrite app_length in LE.
               simpl in LE.
               omega.
             }
             generalize (bits_to_Z_range (length l1) l1).
             intros H.
             destruct H.
             - auto.
             - split.
               -- omega.
               -- induction (length l1).
                  --- unfold two_power_nat in H10. simpl in H10. omega.
                  --- assert(bits_to_Z l1 < two_power_nat 7%nat) as ub. {
                        assert(two_power_nat (S n) <= two_power_nat 7) as ub1. {
                          generalize (two_power_mono (S n) 7).
                          omega.
                        }
                        omega.
                      }
                      unfold two_power_nat in ub.
                      simpl in ub.
                      auto.               
           }
           assert(0<=bool_to_Z b < 2 ) as bRange. {
             unfold bool_to_Z.
             destruct b; omega.
           }
           destruct l1Range.
           destruct bRange.
           split.
           - omega.
           - assert(Byte.modulus = 256) as modu. {
               unfold Byte.modulus.
               unfold Byte.wordsize.
               unfold Wordsize_8.wordsize.
               unfold two_power_nat.
               simpl.
               auto.
             }
             rewrite modu.
             omega.
         }
         rewrite range.
         
        
         rewrite (div2_shiftr_eq (length l1) _);auto.
      ++ simpl.
         rewrite Pplus_one_succ_r.
         rewrite Pos.iter_add.
         simpl.
         assert(Z.div2 (Byte.unsigned bB[ (l1 ++ l2') ++ [b]])=(Byte.unsigned bB[(l1++l2')]))as div_prefix. {
           rewrite bits_to_Z_prefix.
           rewrite Byte.unsigned_repr.
           + rewrite (div2_shiftr_eq (length(l1++l2')));auto.
             rewrite Byte.unsigned_repr.
             auto.
             assert(length(l1++l2') = length(l1++l2')) as lenRefl. {
               auto.
             }
             generalize (bits_to_Z_range (length(l1++l2')) (l1++l2') lenRefl).
             intros H.
             assert((length (l1++l2')<=7)%nat) as lenRange. {
               rewrite app_length in LE.
               rewrite app_length in LE.
               simpl in LE.
               rewrite plus_assoc in LE.
               rewrite <- app_length in LE.               
               omega.
             }
             unfold Byte.max_unsigned.
             unfold Byte.modulus.
             assert(two_power_nat (length (l1 ++ l2')) <= two_power_nat 7) as tpnRange. {
               generalize (two_power_mono (length(l1++l2')) 7 lenRange).
               omega.
             }
             unfold Byte.wordsize.
             unfold Wordsize_8.wordsize.
             assert(two_power_nat 7 < two_power_nat 8 -1) as tpnRange1. {
               unfold two_power_nat.
               simpl.
               omega.
             }
             omega.
           + generalize (bool_to_Z_range b).
             intros H.
             assert((length (l1++l2')<=7)%nat) as lenRange. {
               rewrite app_length in LE.
               rewrite app_length in LE.
               simpl in LE.
               rewrite plus_assoc in LE.
               rewrite <- app_length in LE.               
               omega.
             }
             assert(two_power_nat (length (l1 ++ l2')) <= two_power_nat 7) as tpnRange. {
               generalize (two_power_mono (length(l1++l2')) 7 lenRange).
               omega.
             }
             assert(two_power_nat 7 = 128) as tpn7. {
               unfold two_power_nat.
               simpl.
               omega.
             }
             rewrite tpn7 in tpnRange.
              assert(length(l1++l2') = length(l1++l2')) as lenRefl. {
               auto.
             }
              generalize (bits_to_Z_range (length(l1++l2')) (l1++l2') lenRefl).
              intros H10.
              unfold Byte.max_unsigned.
              assert(Byte.modulus = 256) as modo. {
                unfold Byte.modulus.
                unfold two_power_nat.
                simpl.
                auto.
              }
              rewrite modo.              
              omega.
         }              
         rewrite div_prefix.
         assert(le (length(l1++l2')) 8%nat) as len. {
           rewrite app_length in LE.
           rewrite app_length in LE.
           simpl in LE.
           rewrite plus_assoc in LE.
           rewrite <- app_length in LE.
           omega.
         }
         assert(eq (length(l2')) (S n)) as lenl2. {
           rewrite app_length in EQ.
           simpl in EQ.
           omega.
         }
         generalize (IHn' l1 l2' len lenl2).
         intros H.
         unfold Byte.shru in H.
         unfold Z.shiftr in H. unfold Z.shiftl in H.
         rewrite Byte.unsigned_repr in H.
         +++ simpl in H. apply H.
         +++
           rewrite app_length in EQ. simpl in EQ.
           repeat rewrite app_length in LE.
           simpl in LE.
           assert(Byte.max_unsigned = 255) as byteMax. {
             unfold Byte.max_unsigned. simpl. auto.
           }
           assert(Z.of_nat (S n)<=8) as nRange. {             
             assert(Z.of_nat (S n) = Z.of_nat n +1 ) as pls. {
               rewrite Nat2Z.inj_succ.
               simpl.
               omega.
             }
             rewrite pls.
             omega.             
           }
           rewrite byteMax.
           omega.
           
    +  rewrite app_length in EQ. simpl in EQ.
       repeat rewrite app_length in LE.
       simpl in LE.
       unfold Byte.max_unsigned. simpl.
       rewrite Zpos_P_of_succ_nat.
       omega.
Qed.

Lemma bits_to_Z_suffix: forall n l1 a,
    (n= length l1)%nat ->
    bits_to_Z (a::l1) = (bool_to_Z a) * (two_power_nat (length l1)) + bits_to_Z l1.
Proof.
  induction n.
  + intros l1 a H.
    symmetry in H.
    generalize (zero_length_list l1 H).
    intros H10.
    rewrite H10.
    cbn.
    rewrite two_power_nat_O.
    omega.


  + intros l1 a H.
    symmetry in H.
    generalize (list_len_gt1 bool l1 n H).
    intros (l' & t & H1).
    rewrite H.
    rewrite H1.
    setoid_rewrite (bits_to_Z_prefix (a::l') t).
    assert (length l' = n) as lenL'. {
      rewrite H1 in H.
      rewrite app_length in H.
      simpl in H.
      omega.
    }
    setoid_rewrite (IHn l' a).
    ++ rewrite lenL'.
       setoid_rewrite (bits_to_Z_prefix l' t).
       rewrite two_power_nat_S.
       repeat rewrite Zmult_assoc.
       repeat rewrite Z.mul_add_distr_l.
       repeat rewrite Zmult_assoc.
       repeat rewrite Zplus_assoc.
       replace ( 2 * bool_to_Z a * two_power_nat n) with ( bool_to_Z a * 2 * two_power_nat n).
       +++ omega.
       +++
         rewrite Zmult_assoc_reverse.
         rewrite (Z.mul_shuffle3 (bool_to_Z a) 2 (two_power_nat n)).
         rewrite Zmult_assoc.
         auto.
    ++ symmetry in  lenL'.
       auto.
Qed.


Lemma bits_to_Z_cons_eq : forall a l1 l2,
    bits_to_Z ((a::l1) ++ l2) = (bool_to_Z a)*(two_power_nat (length (l1++l2))) +
                                bits_to_Z (l1 ++ l2).
Proof.  
  intros a l1 l2.
  setoid_rewrite <- (app_comm_cons l1 l2 a).
  rewrite (bits_to_Z_suffix (length(l1++l2))  (l1++l2) a).
  auto. auto.
Qed.

Lemma bits_to_Z_cat: forall l1 l2,
    bits_to_Z (l1 ++ l2) = Z.shiftl (bits_to_Z l1) (Z.of_nat (length l2)) + bits_to_Z l2.
Proof.
  induction l1.
  + intros l2.
    simpl.
    rewrite Z.shiftl_mul_pow2.
    simpl. auto.
    generalize (Zle_0_nat (length l2)).
    omega.
  + intros l2.
    rewrite bits_to_Z_cons_eq.
    rewrite Z.shiftl_mul_pow2.
    rewrite IHl1.
    rewrite Z.shiftl_mul_pow2.
    rewrite (bits_to_Z_suffix (length l1) l1 a).
    rewrite app_length.
    repeat rewrite two_power_nat_equiv.
    rewrite Nat2Z.inj_add.
    setoid_rewrite (Z.pow_add_r 2 (Z.of_nat (length l1)) (Z.of_nat (length l2))).
    rewrite Z.mul_add_distr_r.
    rewrite Z.mul_assoc.
    rewrite Z.add_assoc.
    omega.
    generalize (Zle_0_nat (length l1)).
    omega.
    generalize (Zle_0_nat (length l2)).
    omega.
    omega.
    generalize (Zle_0_nat (length l2)).
    omega.
    generalize (Zle_0_nat (length l2)).
    omega.
Qed.



Lemma bits_to_Z_mod : forall l1 l2,
    bits_to_Z (l1 ++ l2) mod (2 ^ (Z.of_nat (length l2))) = bits_to_Z l2.
Proof.
  induction l1.
  - intros l2. simpl.
    apply Zdiv.Zmod_small.
    rewrite <- two_power_nat_equiv.
    eapply bits_to_Z_range; eauto.
  - intros l2.
    rewrite bits_to_Z_cons_eq.
    rewrite app_length. rewrite two_power_nat_equiv.
    rewrite Nat2Z.inj_add.
    rewrite Z.pow_add_r; try omega.
    rewrite Z.mul_assoc. rewrite Z.add_comm.
    rewrite Z.mod_add.
    apply IHl1.
    apply Z.pow_nonzero; try omega.
Qed.

Lemma Z_and7: forall l1 l2,
    (length (l1++l2) <=8)%nat ->
    (length l2 = 3)%nat->
    Z.land (bits_to_Z (l1 ++ l2)) 7 = bits_to_Z l2.
Proof.
  intros l1 l2 LENBND L2.
  assert (7 = Z.ones 3) as OEQ. {
    rewrite Z.ones_equiv. simpl. auto.
  }
  rewrite OEQ, Z.land_ones; try omega.
  replace 3 with (Z.of_nat (length l2)).
  apply bits_to_Z_mod.
  rewrite L2.
  auto.
Qed.

  
Lemma and7: forall l1 l2,
    (length (l1++l2) <=8)%nat ->
    (length l2 = 3)%nat->
    Byte.and bB[l1++l2] (Byte.repr 7) = bB[l2].
Proof.
  intros. unfold Byte.and.
  f_equal.
  repeat rewrite Byte.unsigned_repr.
  apply Z_and7; auto.
  + unfold Byte.max_unsigned. unfold Byte.modulus. unfold two_power_nat. simpl.
    omega.
  + assert(length(l1++l2) = length(l1++l2)) as len by auto.
    generalize (bits_to_Z_range (length(l1++l2)) (l1++l2) len).
    intros H11.
    assert(two_power_nat (length (l1++l2)) <= two_power_nat 8) as ub. {
      generalize (two_power_mono (length(l1++l2)) 8 H).
      intros H12.
      omega.
    }
    assert (Byte.max_unsigned = 255) as maxByte. {
      unfold Byte.max_unsigned. unfold Byte.modulus. simpl. auto.
    }
    assert (two_power_nat 8 = 256) as tp. {
      unfold two_power_nat. simpl. auto.
    }
    rewrite tp in ub.
    rewrite maxByte.
    omega.
Qed.
      

Lemma Znneg_bits_inj: forall a b,
    (forall n, n >= 0 -> (Z.testbit a n) = (Z.testbit b n)) -> a = b.
Proof.
  intros. apply Z.bits_inj.
  red. intros.
  destruct n.
  - apply H; omega.
  - apply H. generalize (Zgt_pos_0 p). omega.
  - simpl. auto.
Qed.

Lemma Z_add_is_or: forall x y,
    Z.land x y = 0 -> x + y = Z.lor x y.
Proof.
  intros x y AND.
  apply Znneg_bits_inj.
  intros n GE0.
  rewrite Z.lor_spec.
  apply Int.Z_add_is_or. omega.
  intros j JRNG.
  rewrite <- Z.land_spec, AND.
  apply Z.bits_0.
Qed.

  

Lemma and_short: forall l n,
    Z.land (bits_to_Z l) (Z.shiftl n (Z.of_nat (length l))) = 0.
Proof.
  intros l n.
  assert(bits_to_Z l = Z.land (bits_to_Z l) (Z.ones (Z.of_nat (length l)))) as insert. {
    rewrite Z.land_ones.
    replace (bits_to_Z l) with (bits_to_Z l + 0).
    rewrite (Zmod_unique (bits_to_Z l + 0) (2^Z.of_nat (length l)) 0 (bits_to_Z l)).
    omega.
    omega.
    assert(length l = length l) by auto.
    generalize (bits_to_Z_range (length l) l H).
    intros H10.
    set (X:=length l) in *.
    assert(0<=Z.of_nat X). {
      generalize (Zle_0_nat X).
      intros H11.
      omega.
    }
    rewrite two_power_nat_equiv in H10.
    omega.
    omega.
    generalize (Zle_0_nat (length l)).
    intros H11.
    omega.
  }
  rewrite insert.
  rewrite Z.land_comm.
  replace  (Z.land (bits_to_Z l) (Z.ones (Z.of_nat (length l)))) with  (Z.land (Z.ones (Z.of_nat (length l)))  (bits_to_Z l) ).
  + rewrite Z.land_assoc.
    set (X:= length l).
    rewrite Z.land_ones.
    rewrite Z.shiftl_mul_pow2.
    rewrite(Zmod_unique (n*2^Z.of_nat X) (2^Z.of_nat X) n 0).
    rewrite Z.land_0_l.
    auto.
    omega.
    assert(0<2) by omega.
    assert(0<=Z.of_nat X). {
      generalize (Zle_0_nat X).
      intros H10.
      omega.
    }
    generalize (Z.pow_pos_nonneg 2 (Z.of_nat X) H H10).
    intros H11.
    omega.
    omega.
    omega.
  + rewrite Z.land_comm.
    auto.
Qed.


Lemma bits_to_Z_or: forall l1 l2,
    bits_to_Z (l1++l2) = Z.lor (Z.shiftl (bits_to_Z l1) (Z.of_nat (length l2))) (bits_to_Z l2).
Proof.
  intros. 
  erewrite <- Z_add_is_or.
  rewrite bits_to_Z_cat.
  auto.
  rewrite Z.land_comm.
  rewrite and_short.
  auto.
Qed.

Lemma andf0_Z:forall l1 l2,
    (length(l1++l2) <= 8)%nat ->
    (length l2 = 4)%nat ->
    Z.land (bits_to_Z (l1++l2)) 240 = bits_to_Z (l1++b["0000"]).
Proof.
  intros l1 l2 H H10.
  assert(bits_to_Z (l1++l2) = Z.lor (Z.shiftl (bits_to_Z l1) 4) (bits_to_Z l2)) as des. {
    rewrite bits_to_Z_or.
    rewrite H10.
    auto.
  }
  rewrite des.
  assert(240 = Z.shiftl 15 4) as desc by auto.
  rewrite desc.
  rewrite Z.land_lor_distr_l.
  rewrite <- Z.shiftl_land.
  assert(Z.land (bits_to_Z l1) 15 = bits_to_Z l1). {
    replace 15 with (Z.ones 4).
    rewrite Z.land_ones.
    rewrite (Zmod_unique (bits_to_Z l1) (2^4) 0 (bits_to_Z l1)).
    auto.
    auto.
    generalize (bits_to_Z_range (length l1) l1 eq_refl).
    intros H11.
    rewrite two_power_nat_equiv in H11.
    assert ((length l1 <= 4)%nat). {
      rewrite app_length in *.
      rewrite H10 in H.
      omega.
    }
    assert(two_power_nat (length l1) <= two_power_nat 4). {
      generalize(two_power_mono (length l1) 4). omega.
    }
    repeat rewrite two_power_nat_equiv in H13.
    repeat rewrite <- Zpower_nat_Z in *.
    simpl. unfold Z.pow_pos. simpl.
    unfold Zpower_nat in H13.
    simpl in H13.
    unfold Zpower_nat in H11.    
    omega.
    omega.
    unfold Z.ones.
    simpl.
    omega.
  }
  rewrite H11.
  assert(Z.land (bits_to_Z l2) (Z.shiftl 15 4) = 0). {
    generalize (and_short l2 15).
    intros H12.
    rewrite H10 in H12.
    auto.
  }

  rewrite H12.
  rewrite Z.lor_0_r.
  assert( Z.shiftl (bits_to_Z l1) 4 = bits_to_Z (l1 ++ b[ "0000"])). {
    rewrite bits_to_Z_or.
    replace (bits_to_Z b["0000"]) with 0.
    rewrite Z.lor_0_r.
    auto.
    simpl.
    auto.
  }
  auto.
Qed.

Lemma andf0:forall l1 l2,
    (length(l1++l2) <= 8)%nat ->
    (length l2 = 4)%nat ->
    Byte.and bB[l1++l2] HB["F0"] = bB[l1++b["0000"]].
Proof.
  intros l1 l2 H H10.
  unfold Byte.and.
  f_equal.
  repeat rewrite Byte.unsigned_repr.
  rewrite andf0_Z. auto.
  auto.
  auto.
  unfold Byte.max_unsigned. simpl. omega.
  assert(length(l1++l2) = length(l1++l2)) by auto.
  generalize (bits_to_Z_range (length(l1++l2)) (l1++l2) H11).
  intros H12.
  assert(two_power_nat (length (l1++l2)) <= two_power_nat 8) as ub. {
    generalize (two_power_mono (length(l1++l2)) 8 H).    
    omega.
  }
  replace (two_power_nat 8 ) with 256 in ub.
  unfold Byte.max_unsigned. simpl.
  omega.
  unfold two_power_nat. simpl. omega.
Qed.
Lemma Z_shru_bits: forall n l1 l2,
    (length l2 = n)%nat ->
    Z.shiftr (bits_to_Z (l1++l2)) (Z.of_nat n) = bits_to_Z l1.

Proof.
  induction n.
  + intros l1 l2 H.
    simpl. rewrite Z.shiftr_0_r.
    rewrite (zero_length_list l2).
    f_equal. apply app_nil_r.
    auto.
    
  + intros l1 l2 H.
    rewrite Z.shiftr_div_pow2.
    ++ rewrite bits_to_Z_cat.
       rewrite Z.shiftl_mul_pow2.
       rewrite H.
       rewrite <- (Zdiv.Zdiv_unique (bits_to_Z l1 * 2 ^ Z.of_nat (S n) + bits_to_Z l2) (2 ^ Z.of_nat (S n)) (bits_to_Z l1) (bits_to_Z l2)).
       auto.
       generalize (bits_to_Z_range (S n) l2 H).
       intros Hrange.
       rewrite two_power_nat_equiv in Hrange.
       rewrite H in Hrange.
       omega.
       rewrite Z.mul_comm. auto.
       omega.
    ++ omega.
       
Qed.


Lemma remove_first_S_n: forall n i {A:Type} (l:list A),
    (length l = n)%nat ->
    (S i <= n)%nat ->
    exists remove_one_step, ((remove_first_n l 1) = OK remove_one_step /\
    (remove_first_n l (S i)) = (remove_first_n remove_one_step i)).
Proof.
  induction n.
  + intros i A0 l H H10.
    inversion H10.
  + intros i A0 l H H10.
    destruct l. inversion H.
    unfold remove_first_n.
    exists l.
    auto.
Qed.


Lemma remove_first_length: forall n i {A:Type} (l:list A),
    (length l = n )%nat ->
    (i<=n)%nat ->
    exists remains,  ((remove_first_n l i) = OK remains /\
    (length remains = n-i)%nat).
Proof.
  induction n.
  + intros i A0 l H H10.
    inversion H10.
    simpl. eauto.

  + induction i.
    ++ intros A0 l H H10.
       inversion H10. inversion H12.
       simpl. rewrite <- H13 in H. auto.
       eauto. 
       rewrite <- H14 in H.
       simpl.
       eauto.

    ++ intros A0 l H H10.
       
       generalize (remove_first_S_n (S n) i l H H10).
       intros (one_step & HRemove_one & HRemoveFirst).
       rewrite HRemoveFirst.
       simpl.
       destruct l; simpl in HRemove_one; inversion HRemove_one.
       rewrite <- H12.
       cut (length l = n).
       intros HLengthL.
       cut ((i <= n)%nat).
       intros HILTN.
       generalize (IHn i _ l HLengthL HILTN).
       auto.
       omega.
       simpl in H.
       inversion H. auto.
Qed.



Lemma sublist_Sn: forall n i {A:Type} (l l':list A) (a:A),
    (length l = n )%nat ->
    (S i<=n)%nat ->
    (l = a::l') ->
    exists subl', (sublist l' i = OK subl' /\
                  sublist l (S i) = OK (a::subl')).
Proof.
  induction n.
  + intros i A0 l l' a H H10 H11. inversion H10.
  + intros i A0 l l' a H H10 H11.
    destruct i.
    ++ simpl. exists [].
       destruct l'. rewrite H11. simpl. auto.
       rewrite H11. simpl. auto.
    ++ cut((S i <= n)%nat). intros HILTN.
       cut(length l' = n). intros HL'.
       destruct l'. simpl in HL'.
       rewrite <- HL' in HILTN.
       inversion HILTN.
       generalize (IHn i _ (a0::l') l' a0 HL' HILTN eq_refl).
       intros(subl' & HSubl' & HSSubl').
       simpl.
       rewrite HSubl'.
       simpl. exists(a0::subl').
       split. auto.
       rewrite H11.
       rewrite HSubl'. simpl. auto.
       rewrite H11 in H.
       simpl in H.
       omega.
       omega.       
Qed.


Lemma sublist_length: forall n i {A:Type} (l:list A),
    (length l = n )%nat ->
    (i<=n)%nat ->
    exists sub, ((sublist l i) = OK sub /\(length sub = i)).
Proof.
  induction n.
  + intros i A0 l H H10.
    inversion H10.
    simpl. rewrite (zero_length_list l). exists []. auto. auto.
  + intros i A0 l H H10.
    destruct l. inversion H.
    induction i.
    ++  simpl. exists []. auto.
    ++ generalize (sublist_Sn (S n) i (a::l) l a H H10 eq_refl).
       intros (subl' & HSubl & HSSubl).
       cut(length l = n). intros HL.
       cut((i <= n)%nat). intros HILTN.
       generalize(IHn i _ l HL HILTN).
       intros(sub & HSub & HLSub).
       rewrite HSub in HSubl.
       inversion HSubl.
       rewrite <- H12 in HSSubl.
       simpl. rewrite HSub.
       simpl. exists(a::sub).
       split. auto.
       simpl.
       f_equal. auto.
       omega.
       simpl in H.
       omega.
Qed.


Lemma sublist_remove_first_cat: forall n i {A: Type} (l:list A),
    length l = n ->
    (i <= n)%nat ->
    exists prefix suffix,(
        sublist l i = OK prefix
        /\ remove_first_n l i = OK suffix
        /\ l = prefix ++ suffix).
Proof.
  induction n.
  + intros i A0 l H H10.
    inversion H10.
    simpl.
    destruct l.
    exists [], [].
    auto.
    exists [], (a::l).
    auto.
  + induction i.
    ++ intros A0 l H H10.
       simpl.
       destruct l.
       exists [],[]. auto.
       exists [], (a::l).
       auto.
    ++ intros A0 l H H10.
       destruct l. inversion H.
       simpl.
       (* generalize (sublist_Sn (S n) i (a::l) l a H H10 eq_refl). *)
       (* intros (subl & HSubl & HSSubl). *)
       (* simpl. rewrite HSubl. simpl. *)
       (* exists (a::subl). *)
       cut(length l = n). intros HL.
       cut((i<=n)%nat). intros HILTN.
       generalize(IHn i _ l HL HILTN).
       intros (prefix & suffix & HPre & HSuf & HAll).
       rewrite HPre.
       rewrite HSuf.
       exists(a::prefix), suffix.
       simpl.
       split. auto.
       split.
       auto.
       rewrite HAll. auto.
       omega.
       simpl in H.
       omega.       
Qed.

(* Lemma encode_decode_reg_refl: forall r x bits1 bits2, *)
(*     encode_ireg r = OK x *)
(*     -> List.length bits1 = 2%nat *)
(*     -> List.length bits2 = 11%nat *)
(*     -> exists b1 b2, *)
(*            b2 = Byte.repr (bits_to_Z (remove_first_n bits2 3)) *)
(*         /\ b1 = Byte.repr (bits_to_Z (bits1 ++ x ++ (sublist bits2 3))) *)
(*         /\ [b1;b2] = encode_int_big 2 (bits_to_Z (bits1++x++bits2)) *)
(*         /\ (addrmode_parse_reg (Byte.shru (Byte.and b1 (Byte.repr 56)) (Byte.repr 3))) = OK r. *)
(* Proof. *)
(*   intros r x bits1 bits2 H H10 H11. *)
(*   exists ( bB[ bits1 ++ x ++ sublist bits2 3]). *)
(*   exists(  bB[ remove_first_n bits2 3]). *)
(*   repeat split. *)
(*   + unfold encode_int_big. *)
(*     unfold bytes_of_int. *)
(*     unfold rev. *)
(*     replace 256 with (2^8). *)
(*     rewrite <- (Z.shiftr_div_pow2 (bits_to_Z (bits1 ++ x ++ bits2)) 8). *)
    
(*     replace (x++bits2) with (x++ sublist bits2 3++ remove_first_n bits2 3). *)
(*     replace (bits1 ++ x ++ sublist bits2 3 ++ remove_first_n bits2 3) with ((bits1 ++ x ++ sublist bits2 3) ++ remove_first_n bits2 3). *)
(*     setoid_rewrite (Z_shru_bits 8 (bits1++x++ sublist bits2 3) (remove_first_n bits2 3)). *)
(*     rewrite app_nil_l. *)
(*     assert ( bB[ remove_first_n bits2 3] = bB[ (bits1 ++ x ++ sublist bits2 3) ++ remove_first_n bits2 3]). { *)
(*       rewrite (bits_to_Z_cat (bits1 ++ x ++ sublist bits2 3) (remove_first_n bits2 3)). *)
(*       assert(Byte.eqm (Z.shiftl (bits_to_Z (bits1 ++ x ++ sublist bits2 3)) (Z.of_nat (length (remove_first_n bits2 3))) + bits_to_Z (remove_first_n bits2 3)) (bits_to_Z ( remove_first_n bits2 3))). { *)
(*         unfold Byte.eqm. *)
(*         unfold Byte.eqmod. *)
(*         rewrite (remove_first_length 11 3 bits2); try omega; auto. *)
(*         rewrite (Z.shiftl_mul_pow2). *)
(*         exists(bits_to_Z (bits1 ++ x ++ sublist bits2 3)). *)
(*         simpl. auto. simpl. omega.                 *)
(*       } *)
(*       generalize (Byte.eqm_samerepr _ _ H12). *)
(*       auto.      *)
(*     } *)
(*     rewrite H12. *)
(*     auto. *)
  
(*     apply (remove_first_length 11 3 bits2). *)
(*     auto. omega. repeat rewrite <- app_assoc. auto. *)
(*     rewrite <- (sublist_remove_first_cat 11 3 bits2). auto. auto. omega. omega. *)
(*     unfold Z.pow. unfold Z.pow_pos. simpl. auto. *)
(*   + rewrite <- Byte.and_shru. *)
(*     rewrite app_assoc. *)
(*     setoid_rewrite (shru_bits 3 (bits1++x) (sublist bits2 3)). *)
(*     assert(Byte.shru (Byte.repr 56) (Byte.repr 3) = Byte.repr 7) as shru563. { *)
(*       unfold Byte.shru. f_equal. *)
(*     } *)
(*     rewrite shru563. *)
(*     rewrite and7. *)
(*     rewrite (encode_parse_reg_refl r);auto. *)
(*     rewrite app_length. *)
(*     rewrite H10. *)
(*     rewrite (encode_reg_length r);auto. *)
(*     rewrite (encode_reg_length r);auto. *)
(*     auto. *)
(*     repeat rewrite app_length. rewrite H10. rewrite ( sublist_length 11 3). *)
(*     rewrite (encode_reg_length r);auto. *)
(*     auto. *)
(*     omega. *)
(*     rewrite(sublist_length 11 3);auto. omega. *)
(* Qed. *)
    

Lemma shru563:
  Byte.shru (Byte.repr 56) (Byte.repr 3) = Byte.repr 7.
Proof.
  unfold Byte.shru.
  f_equal.
Qed.

Lemma byte_and_C0: forall l1 l2,
    (length l1 <= 2)%nat ->
    (length l2 = 6)%nat ->
    Byte.and bB[l1++l2] HB["C0"] = bB[l1++b["000000"]].
Proof.
  intros l1 l2 H H10.
  unfold Byte.and.
  repeat f_equal.
  repeat rewrite Byte.unsigned_repr.
  +
    rewrite bits_to_Z_cat.
    rewrite Z_add_is_or.
    ++ rewrite Z.land_lor_distr_l.
       assert (HZ["C0"] = Z.shiftl (Z.ones 2) 6) as Hc. {
         simpl.
         auto.
       } 
       assert ((Z.land (bits_to_Z l2) HZ[ "C0"])=0). {
         rewrite Hc.         
         replace 6 with (Z.of_nat (length l2)).
         rewrite (and_short l2 (Z.ones 2)).
         auto.
         rewrite H10.
         auto.
       }
       rewrite H11.
       rewrite Z.lor_0_r.
       rewrite Hc.
       rewrite H10.
       rewrite <- Z.shiftl_land.
       assert((Z.land (bits_to_Z l1) (Z.ones 2))= bits_to_Z l1) as and2. {
         rewrite Z.land_ones.
         rewrite Zmod_small.
         auto.
         simpl. unfold Z.pow_pos. simpl.
         generalize (bits_to_Z_range (length l1) l1 eq_refl).
         intros Hrange.
         assert(two_power_nat (length l1) <= two_power_nat 2). {
           generalize  (two_power_mono (length l1) 2 H).
           omega.
         }
         unfold two_power_nat in *.
         simpl in H12.
         omega.
         omega.
       }
         
       rewrite and2.
       rewrite bits_to_Z_cat.
       replace (length b[ "000000"]) with 6%nat.
       replace (bits_to_Z  b[ "000000"]) with 0.
       rewrite <- Zplus_0_r_reverse.
       auto. simpl. auto. auto.
    ++
      rewrite Z.land_comm.
      rewrite (and_short l2 (bits_to_Z l1)).
      auto.
  + unfold Byte.max_unsigned. simpl. omega.
  + unfold Byte.max_unsigned.
    simpl.
    generalize (bits_to_Z_range (length(l1++l2)) (l1++l2) eq_refl).
    intros Hrange.
    assert((length(l1++l2) <=8)%nat). {
      rewrite app_length.
      omega.
    }
    assert(two_power_nat (length (l1 ++ l2)) <= two_power_nat 8). {
      generalize (two_power_mono (length(l1++l2)) 8 H11).
      omega.
    }
    
    unfold two_power_nat in H12.
    simpl in H12.
    unfold two_power_nat in Hrange.
    omega.
Qed.

Lemma decode_encode_rr_operand_refl: forall l r1 r2 x x0,
    (length l = 2)%nat ->
    encode_ireg r1 = OK x ->
    encode_ireg r2 = OK x0 ->
    decode_rr_operand bB[l++x++x0] = OK(r1, r2).
Proof.
  intros l r1 r2 x x0 H H10 H11.
  unfold decode_rr_operand.
  rewrite <- Byte.and_shru.
  assert(Byte.shru HB["38"] HB["3"] = HB["7"]). {
    simpl. unfold Byte.shru. f_equal.
  }
  rewrite H12.
  rewrite app_assoc.
  setoid_rewrite (shru_bits 3 (l++x) x0).
  setoid_rewrite (and7 l x).
  rewrite (encode_parse_reg_refl r1).
  simpl.
  rewrite (and7 (l++x) x0).
  rewrite (encode_parse_reg_refl r2).
  simpl.
  auto.
  auto.
  repeat rewrite app_length.
  rewrite H.
  rewrite (encode_reg_length r1); auto.
  rewrite (encode_reg_length r2); auto.
  rewrite (encode_reg_length r2); auto.
  auto.
  repeat rewrite app_length.         
  rewrite H.
  rewrite (encode_reg_length r1); auto.
  rewrite (encode_reg_length r1); auto.
  repeat rewrite app_length.
  rewrite H.
  rewrite (encode_reg_length r1); auto.
  rewrite (encode_reg_length r2); auto.
  rewrite (encode_reg_length r2); auto.
Qed.

(* encode_int32 = 4bytes *)
Lemma encode_int32_4_exists: forall x l bytes,
    encode_int32 x++l = bytes
    ->exists b1 b2 b3 b4,
      bytes = b1::b2::b3::b4::l.
Proof.
  intros x l bytes H.
  unfold encode_int32 in H.
  unfold encode_int in H.
  unfold rev_if_be in H.
  destruct Archi.big_endian eqn:EQArch; inversion EQArch.
  simpl in H.
  exists  (Byte.repr x), (Byte.repr (x / 256)) ,(Byte.repr (x / 256 / 256)), (Byte.repr (x / 256 / 256 / 256)).
  auto.
Qed.

Ltac cal_byte_modulus :=
  match goal with
  |[ |- _ ] => unfold Byte.modulus;
               unfold Byte.wordsize;
               unfold Wordsize_8.wordsize;
               unfold two_power_nat; simpl
  |_ => auto
  end.

Ltac resolve_enc_dec_ireg_refl x0 :=
  match goal with
  | [ H: encode_ireg ?rd = OK x0 |- _ ] =>
    generalize(encode_decode_ireg_refl _ _ H);
    intros Hrd; destruct Hrd as (?x & ?Hrd);
    destruct Hrd as (?H10 & ?H11)
  |_ => idtac
  end.

Ltac resolve_reloc iofs sofs :=
  match goal with
  |[ H1: instr_reloc_offset ?i = OK iofs,
         H2: instr_reloc_offset ?i = OK ?x1,
             HEQ: get_instr_reloc_addend' _ _ = OK _
     |- _ ]=>
   rewrite H1 in H2; inversion H2;
   subst x1;
   unfold get_instr_reloc_addend' in HEQ;
   unfold get_reloc_addend in HEQ;
   unfold find_ofs_in_rtbl;
   destruct(ZTree.get (iofs+sofs) rtbl_ofs_map);
   inversion HEQ
  |_ => idtac
  end.


Lemma BbTruncate: forall l1 l2,
    (length l2 = 8)%nat
    -> bB[l1++l2] = bB[l2].
Proof.
  intros l1 l2 H.
  apply Byte.eqm_samerepr.
  unfold Byte.eqm.
  cal_byte_modulus.
  generalize(Byte.eqmod_mod 256 Byte.modulus_pos (bits_to_Z (l1++l2))).
  rewrite bits_to_Z_cat.
  rewrite H.
  rewrite Byte.Zshiftl_mul_two_p.
  simpl. unfold two_power_pos. simpl.
  rewrite (Zmod_unique  (bits_to_Z l1 * 256 + bits_to_Z l2) 256 (bits_to_Z l1) (bits_to_Z l2)).
  auto. auto. generalize (bits_to_Z_range 8 l2 H).
  rewrite H. unfold two_power_nat. simpl. omega. omega.
Qed.


Ltac resolve_reg_length x :=
                 match goal with
                 |[ H1:encode_ireg ?i = OK x|- _ ] =>
                  rewrite (encode_reg_length i x H1)
                 end.

Ltac resolve_scale_length x :=
  match goal with
  |[ H1:encode_scale ?i = OK x|- _ ] =>
   rewrite (encode_scale_length i x H1)
  end.

Ltac resolve_rsp x:=
  match goal with
  |[H: bB[x] = _, Hreg: encode_ireg ?i = OK x,
                        Hne: ?i<> RSP |- _] =>
   destruct i eqn:?EQI; simpl in Hreg; inversion Hreg;
   subst x; inversion H; congruence
  end.


Lemma encode_decode_addrmode_relf: forall a rd bytes rofs i iofs sofs,
    instr_reloc_offset i = OK iofs
    -> encode_addrmode rtbl_ofs_map sofs i a rd = OK bytes
    -> rofs = iofs + sofs
    -> forall l, decode_addrmode rofs (bytes++l) = OK (rd, a, l).
Proof.
  intros a rd bytes rofs i iofs sofs HRelocOfs  HEncode  HRofs  l.

  unfold encode_addrmode in HEncode.
  destruct a eqn:EQA.
  monadInv HEncode.
  destruct const eqn:EQC. 
  +
    unfold encode_addrmode_aux in EQ.
    destruct ofs eqn:EQOFS.
    
    ++ monadInv EQ.
       destruct p.
       destruct base eqn:EQB.
       +++ destruct (ireg_eq i0 RSP); monadInv EQ2.
           unfold decode_addrmode.
           simpl.
           assert(HEQX1: Byte.shru
                           (Byte.and
                              (Byte.repr
                                 (bits_to_Z
                                    (char_to_bool "1"
                                                  :: char_to_bool "0"
                                                  :: x1 ++
                                                  char_to_bool "1"
                                                  :: char_to_bool "0" :: char_to_bool "0" :: x2 ++ x3 ++ x4) / 256))(Byte.repr 56)) (Byte.repr 3) = bB[x1]). {             
             rewrite <- Byte.and_shru.
             rewrite shru563.
             replace 256 with (2^8).
             rewrite <- Z.shiftr_div_pow2.
             replace  (char_to_bool "1"
                 :: char_to_bool "0"
                    :: x1 ++
                       char_to_bool "1"
                       :: char_to_bool "0" :: char_to_bool "0" :: x2 ++ x3 ++ x4)
               with
                  (((char_to_bool "1"
                 :: char_to_bool "0"
                    :: x1) ++
                       (char_to_bool "1"
                       :: char_to_bool "0" :: [char_to_bool "0"])) ++ (x2 ++ x3 ++ x4)).
             
             setoid_rewrite (Z_shru_bits 8 ((char_to_bool "1"
                 :: char_to_bool "0"
                    :: x1) ++
                       (char_to_bool "1"
                       :: char_to_bool "0" :: [char_to_bool "0"]))  (x2 ++ x3 ++ x4)).
             rewrite (shru_bits 3 _ _).
             setoid_rewrite (and7 (char_to_bool "1" :: [char_to_bool "0"]) x1).
             auto.

             1,3,4: repeat rewrite app_length; simpl.
             1,2,4:rewrite (encode_reg_length rd x1); try omega.
             1-8: auto.
             repeat rewrite app_length. 
             rewrite (encode_scale_length z0).
             rewrite (encode_reg_length i0).
             rewrite (encode_reg_length i1).
             omega.
             all: auto.
             repeat rewrite <- app_assoc.
             auto.
             omega.
             }
             rewrite HEQX1.
             generalize (encode_decode_ireg_refl _ _  EQ0).
             intros HRx1.
             destruct HRx1. destruct H.
             rewrite H. simpl.
             assert(HEQ2: (Byte.shru
                             (Byte.repr
                                (bits_to_Z
                                   (char_to_bool "1"
                                                 :: char_to_bool "0"
                                                 :: x1 ++
                                                 char_to_bool "1"
                                                 :: char_to_bool "0" :: char_to_bool "0" :: x2 ++ x3 ++ x4) / 256)) (Byte.repr 6)) = Byte.repr 2). {
               replace 256 with (2^8).
               rewrite <- Z.shiftr_div_pow2.
               replace  (char_to_bool "1":: char_to_bool "0":: x1 ++char_to_bool "1"
                                      :: char_to_bool "0" :: char_to_bool "0" :: x2 ++ x3 ++ x4)
                 with
                   (((char_to_bool "1":: char_to_bool "0":: x1) ++(char_to_bool "1"
                                                        :: char_to_bool "0" :: [char_to_bool "0"])) ++ (x2 ++ x3 ++ x4)).
               
               setoid_rewrite (Z_shru_bits 8 ((char_to_bool "1"
                                                            :: char_to_bool "0"
                                                            :: x1) ++
                                                                   (char_to_bool "1"
                                                                                 :: char_to_bool "0" :: [char_to_bool "0"]))  (x2 ++ x3 ++ x4)).
               setoid_rewrite(shru_bits 6 b["10"] (x1++[char_to_bool "1"; char_to_bool "0"; char_to_bool "0"])).
               simpl. auto.
               1,2,3,4: repeat rewrite app_length.
               all:simpl. auto.
               1,2: rewrite (encode_reg_length rd x1); try omega; auto.
               rewrite (encode_scale_length z0).
               rewrite (encode_reg_length i0).
               rewrite (encode_reg_length i1).
               all: auto.
               simpl. repeat rewrite <- app_assoc. auto. omega.
             }
             rewrite HEQ2.
             branch_byte_eq.
             assert(HEQ4: (Byte.and
                             (Byte.repr
                                (bits_to_Z
                                   (char_to_bool "1"
                                                 :: char_to_bool "0"
                                                 :: x1 ++
                                                 char_to_bool "1"
                                                 :: char_to_bool "0" :: char_to_bool "0" :: x2 ++ x3 ++ x4) / 256)) (Byte.repr 7)) = Byte.repr 4). {
               replace 256 with (2^8).
               rewrite <- Z.shiftr_div_pow2.
               replace  (char_to_bool "1"
                                      :: char_to_bool "0"
                                      :: x1 ++
                                      char_to_bool "1"
                                      :: char_to_bool "0" :: char_to_bool "0" :: x2 ++ x3 ++ x4)
                 with
                   (((char_to_bool "1"
                                   :: char_to_bool "0"
                                   :: x1) ++
                                          (char_to_bool "1"
                                                        :: char_to_bool "0" :: [char_to_bool "0"])) ++ (x2 ++ x3 ++ x4)).
               
               setoid_rewrite (Z_shru_bits 8 ((char_to_bool "1"
                                                            :: char_to_bool "0"
                                                            :: x1) ++
                                                                   (char_to_bool "1"
                                                                                 :: char_to_bool "0" :: [char_to_bool "0"]))  (x2 ++ x3 ++ x4)).
               setoid_rewrite (and7 _ _).
               auto.
               1,3,4: repeat rewrite app_length; simpl.
               rewrite (encode_reg_length rd x1); try omega.
               1-8: auto.
               rewrite (encode_scale_length z0).
               rewrite (encode_reg_length i0).
               rewrite (encode_reg_length i1).
               all: try omega.
               all: auto.
               repeat rewrite <- app_assoc.
               auto.
             }
             rewrite HEQ4.
             assert(HEQRSP: addrmode_parse_reg (Byte.repr 4) = OK RSP). {
               unfold addrmode_parse_reg. branch_byte_eq. auto.
             }
             rewrite HEQRSP.
             simpl.
             rewrite byte_eq_true.
             unfold addrmode_parse_SIB.
             assert(HbBTruncate: bB[ char_to_bool "1"
                                                  :: char_to_bool "0"
                                                  :: x1 ++
                                                  char_to_bool "1"
                                                  :: char_to_bool "0" :: char_to_bool "0" :: x2 ++ x3 ++ x4] = bB[x2++x3++x4]). {
               replace ( char_to_bool "1"
                                                  :: char_to_bool "0"
                                                  :: x1 ++
                                                  char_to_bool "1"
                                                  :: char_to_bool "0" :: char_to_bool "0" :: x2 ++ x3 ++ x4) with
                   ((char_to_bool "1":: char_to_bool "0":: x1 ++char_to_bool "1":: char_to_bool "0" :: char_to_bool "0"::[])++ (x2 ++ x3 ++ x4)).
               apply BbTruncate.

               repeat rewrite app_length.
               
               resolve_scale_length x2.
               resolve_reg_length x3.
               resolve_reg_length x4.
               omega.
               repeat rewrite  app_comm_cons.
               rewrite <- app_assoc. auto.
               
             }
             rewrite HbBTruncate.
             assert (HEQX3:Byte.shru (Byte.and bB[ x2 ++ x3 ++ x4] (Byte.repr 56)) (Byte.repr 3) = bB[x3]). {
               rewrite <- Byte.and_shru.
               rewrite shru563.
               rewrite app_assoc.
               setoid_rewrite (shru_bits 3 (x2++x3) x4).
               rewrite (and7 x2 x3).
               all:repeat rewrite app_length.
               auto.
               1,3:resolve_scale_length x2.
               1,2,3: resolve_reg_length x3.
               2,4: resolve_reg_length x4.
               all:omega.
             }
             rewrite HEQX3.
             generalize (encode_decode_ireg_refl _ _  EQ2).
             intros HRi.
             destruct HRi. destruct H11.
             rewrite H11. rewrite H12. simpl.
             assert(HEQx2: (Byte.shru bB[ x2 ++ x3 ++ x4] (Byte.repr 6)) = bB[x2]). {
               setoid_rewrite (shru_bits 6 x2 (x3++x4)).
               auto.
               all:repeat rewrite app_length.
               all: try resolve_scale_length x2.
               all: try resolve_reg_length x3.
               all: try resolve_reg_length x4.
               all: omega.
             }
             rewrite HEQx2.
             rewrite (encode_parse_scale_refl _ _ EQ).
             simpl.
             assert(HEQx4: (Byte.and bB[ x2 ++ x3 ++ x4] (Byte.repr 7)) = bB[x4]). {
               rewrite app_assoc.
               rewrite (and7 (x2++x3) x4).
               auto.
               all:repeat rewrite app_length.
               all: try resolve_scale_length x2.
               all: try resolve_reg_length x3.
               all: try resolve_reg_length x4.
               all: omega.
             }
             rewrite HEQx4.
             generalize(encode_decode_ireg_refl _ _ EQ3).
             intros HRi0. destruct HRi0. destruct H13 as [H13 H14].
             rewrite  H13. rewrite H14. simpl.
             unfold addrmode_SIB_parse_base.
             destruct (Byte.eq_dec bB[ x4] HB[ "5"]) eqn:EQx4.
             +++++
               assert (Hvalid: valid_int32 x0). admit.
               rewrite byte_eq_false.
             rewrite byte_eq_false.
             rewrite byte_eq_true.
             simpl.
             rewrite HRelocOfs in EQ1.
             unfold get_instr_reloc_addend' in EQ1.
             unfold get_reloc_addend in EQ1.
             unfold find_ofs_in_rtbl.
             destruct ( ZTree.get (iofs + sofs) rtbl_ofs_map); inversion EQ1.
             rewrite (encode_decode_int32_same_prefix).
             simpl.
             2: auto.
             
             rewrite byte_eq_false.
             simpl.
             repeat f_equal.
             auto.
             unfold addrmode_SIB_parse_index.
             destruct (Byte.eq_dec bB[x3] HB["4"]).
             resolve_rsp x3.
             auto.
             generalize (encode_decode_int32_same_prefix _ l Hvalid).
             intros Hint.


             generalize (encode_int32_4_exists x0 l (encode_int32 x0 ++ l) eq_refl).
             intros (b1 & b2 & b3 & b4 & HEncInt).
             rewrite HEncInt.
             rewrite Ptrofs.unsigned_repr.
             simpl.
             auto.
             generalize (encode_parse_reg_refl _ _ EQ0).
             rewrite H.
             intros HRdEQ. inversion HRdEQ. auto.
             unfold valid_int32 in Hvalid.
             unfold two_power_pos in Hvalid.
             simpl in Hvalid.
             unfold Ptrofs.max_unsigned.
             unfold Ptrofs.modulus.
             unfold two_power_nat. unfold Ptrofs.wordsize.
             unfold Wordsize_Ptrofs.wordsize. destruct Archi.ptr64 eqn:EQAR;inversion EQAR.
             simpl. omega.
             1-3:intros HNot.
             1-3:inversion HNot.
             
             +++++
               assert (Hvalid: valid_int32 x0) by admit.
               rewrite byte_eq_false. rewrite byte_eq_false. rewrite byte_eq_true.
             simpl.
             rewrite HRelocOfs in EQ1.
             unfold get_instr_reloc_addend' in EQ1.
             unfold get_reloc_addend in EQ1.
             unfold find_ofs_in_rtbl.
             destruct ( ZTree.get (iofs + sofs) rtbl_ofs_map); inversion EQ1.
             rewrite encode_decode_int32_same_prefix.
             2: auto.
             simpl.
             rewrite byte_eq_false.
             simpl. repeat f_equal.
             auto.
             unfold addrmode_SIB_parse_index.             
             destruct(Byte.eq_dec bB[x3] HB["4"]).
             resolve_rsp x3.

             auto.

             generalize (encode_decode_int32_same_prefix _ l Hvalid).
             intros Hint.
             generalize (encode_int32_4_exists x0 l (encode_int32 x0 ++ l) eq_refl).
             intros (b1 & b2 & b3 & b4 & HEncInt).
             rewrite HEncInt.
             rewrite Ptrofs.unsigned_repr.
             auto.
             simpl.
             generalize (encode_parse_reg_refl _ _ EQ0).
             rewrite H.
             intros HRdEQ. inversion HRdEQ. auto.
             unfold valid_int32 in Hvalid.
             unfold two_power_pos in Hvalid.
             simpl in Hvalid.
             unfold Ptrofs.max_unsigned.
             unfold Ptrofs.modulus.
             unfold two_power_nat. unfold Ptrofs.wordsize.
             unfold Wordsize_Ptrofs.wordsize. destruct Archi.ptr64 eqn:EQAR;inversion EQAR.
             simpl. omega.
             1-3: intros HNot;inversion HNot.
             
       +++
         destruct (ireg_eq i0 RSP); monadInv EQ2.
             unfold decode_addrmode. simpl.
             assert(Hdiv256:  (bits_to_Z
                 (char_to_bool "0"
                  :: char_to_bool "0"
                     :: x1 ++
                        char_to_bool "1"
                        :: char_to_bool "0"
                           :: char_to_bool "0"
                              :: x2 ++
                                 x3 ++
                                 [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"]) /
               256) = bits_to_Z
                        (char_to_bool "0"
                                      :: char_to_bool "0"
                                      :: x1 ++
                                      char_to_bool "1"
                                      :: char_to_bool "0"
                                      :: char_to_bool "0"::[]) ). {
               replace 256 with (2^8).
               rewrite <- Z.shiftr_div_pow2.
               replace 
       (char_to_bool "0"
        :: char_to_bool "0"
           :: x1 ++
              char_to_bool "1"
              :: char_to_bool "0"
                 :: char_to_bool "0"
                    :: x2 ++
                       x3 ++
                       [char_to_bool "1"; char_to_bool "0";
                        char_to_bool "1"])
         with ((char_to_bool "0"
        :: char_to_bool "0"
           :: x1 ++
              char_to_bool "1"
              :: char_to_bool "0"
              :: char_to_bool "0"::[])++(x2++x3++[char_to_bool "1"; char_to_bool "0";char_to_bool "1"])).          
               setoid_rewrite (Z_shru_bits 8).
               auto.
               all: repeat rewrite app_length.
               all: try resolve_scale_length x2.
               all: try resolve_reg_length x3.
               all: try resolve_reg_length x4.
               all: simpl.
               omega.
               repeat rewrite<- app_assoc.
               auto.
               omega.
               unfold Z.pow_pos.
               simpl. auto.
             }
             rewrite Hdiv256.
             simpl.
             assert(HEQx1: Byte.shru
                             (Byte.and
                                bB[ char_to_bool "0"
                                                 :: char_to_bool "0"
                                                 :: x1 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "0"]](Byte.repr 56)) (Byte.repr 3) = bB[x1]). {
               rewrite <- Byte.and_shru.
               rewrite shru563.
               replace (char_to_bool "0":: char_to_bool "0":: x1 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "0"])
                 with
                   ((char_to_bool "0":: char_to_bool "0":: x1) ++ ([char_to_bool "1"; char_to_bool "0"; char_to_bool "0"])).
               rewrite (shru_bits 3 _ _ ).
               setoid_rewrite (and7 (char_to_bool "0" :: [char_to_bool "0"]) x1).
               auto.

               1,3,4: repeat rewrite app_length; simpl.
               all:try rewrite (encode_reg_length rd x1); try omega.
               all: auto.
             }
             rewrite HEQx1.
             generalize (encode_decode_ireg_refl _ _ EQ0).
             intros Hreg1. destruct Hreg1.
             destruct H. rewrite H. simpl.
             assert(Heq0: Byte.shru
                            bB[ char_to_bool "0"
                                             :: char_to_bool "0"
                                             :: x1 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "0"]](Byte.repr 6) = Byte.repr 0). {
               replace (bB[ char_to_bool "0"
                                             :: char_to_bool "0"
                                             :: x1 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "0"]])
                 with
                   (bB[ (char_to_bool "0"
                                             :: char_to_bool "0"::[])++x1 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "0"]]
                   ).
               setoid_rewrite (shru_bits 6).
               f_equal.
               all: repeat rewrite app_length;
                 try resolve_reg_length x1; simpl.
               1-2: omega.
               auto.
             }
             rewrite Heq0.
             rewrite byte_eq_true.
             assert(Heq4: Byte.and
                            bB[ char_to_bool "0"
                                             :: char_to_bool "0"
                                             :: x1 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "0"]](Byte.repr 7) = Byte.repr 4). {
               replace (char_to_bool "0"
        :: char_to_bool "0"
           :: x1 ++
              [char_to_bool "1"; char_to_bool "0";
               char_to_bool "0"]) with
                   ((char_to_bool "0"
        :: char_to_bool "0"
           :: x1) ++
              ([char_to_bool "1"; char_to_bool "0";
                char_to_bool "0"])).
               rewrite and7.
               f_equal.
                all: repeat rewrite app_length;
                  try resolve_reg_length x1; simpl.
                resolve_reg_length x1.
                1-2: omega.
                simpl. auto.
             }
             rewrite Heq4.
             unfold addrmode_parse_reg.
             do 4 (try (rewrite byte_eq_false)).
             rewrite byte_eq_true; auto.
             simpl.
             rewrite byte_eq_true; auto.
             assert(HTruncate:
                      bB[ char_to_bool "0"
                                       :: char_to_bool "0"
                                       :: x1 ++
                                       char_to_bool "1"
                                       :: char_to_bool "0"
                                       :: char_to_bool "0"
                                       :: x2 ++
                                       x3 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"]] = bB[x2 ++ x3 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"]]). {
               replace (char_to_bool "0"
                                       :: char_to_bool "0"
                                       :: x1 ++
                                       char_to_bool "1"
                                       :: char_to_bool "0"
                                       :: char_to_bool "0"
                                       :: x2 ++
                                       x3 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"])
                 with
                   ((char_to_bool "0"
                                       :: char_to_bool "0"
                                       :: x1 ++
                                       char_to_bool "1"
                                       :: char_to_bool "0"
                                       :: char_to_bool "0"::[])
                                       ++ (x2 ++
                                       x3 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"])).
               apply BbTruncate.
               repeat rewrite app_length.
               resolve_reg_length x3.
               resolve_scale_length x2.
               simpl. omega.
               simpl.
               repeat rewrite app_comm_cons.
               rewrite <- app_assoc.
               auto.
             }
             rewrite HTruncate.
             unfold addrmode_parse_SIB.
             assert(HEQx3: Byte.shru
                             (Byte.and
                                bB[ x2 ++ x3 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"]](Byte.repr 56)) (Byte.repr 3) = bB[x3]). {
               rewrite <- Byte.and_shru.
               rewrite shru563.
               
               replace  (x2 ++ x3 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"])
                 with
                   ((x2 ++ x3) ++ ([char_to_bool "1"; char_to_bool "0"; char_to_bool "1"])).
               
               rewrite (shru_bits 3 _ _).
               setoid_rewrite (and7 x2 x3).
               auto.

               1,3,4: repeat rewrite app_length; simpl.
               1,2,4:rewrite (encode_reg_length i0 x3); try omega.
               1,3: rewrite (encode_scale_length z0); try omega.
               all: auto.
               repeat rewrite <- app_assoc.
               auto.
             }
             rewrite HEQx3.
             generalize(encode_decode_ireg_refl _ _ EQ2).
             intros Hregi.
             destruct Hregi. destruct H11.
             rewrite H11.
             simpl.
             assert(HEQx2: Byte.shru bB[ x2 ++ x3 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"]](Byte.repr 6) = bB[x2]). {
               replace (x2 ++ x3 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"]) with
                   ((x2) ++( x3 ++
                                [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"])).
               rewrite (shru_bits 6).
               auto.
               1-2: repeat rewrite app_length.
               1-2: try resolve_scale_length x2;
                 try resolve_reg_length x3;
                 simpl;
                 omega.
               auto.
             }
             rewrite HEQx2.
             generalize (encode_parse_scale_refl _ _ EQ).
             intros Hscale. rewrite Hscale. simpl.
             assert(HEQ5: Byte.and bB[ x2 ++ x3 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"]](Byte.repr 7) = Byte.repr 5). {
               replace ( x2 ++ x3 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"]) with (( x2 ++ x3) ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"]).
               rewrite and7.
               f_equal.
               2: simpl.
               repeat rewrite app_length.
               resolve_scale_length x2.
               resolve_reg_length x3.
               simpl.
               1-2:omega.
               rewrite <- app_assoc.
               auto.
             }
             rewrite HEQ5.
             unfold addrmode_parse_reg.
             do 5 (try (rewrite byte_eq_false)).
             rewrite byte_eq_true; auto.
             simpl.
             unfold addrmode_SIB_parse_base.
             rewrite byte_eq_true; auto.
             rewrite byte_eq_true; auto.
             assert (Hvalid: valid_int32 x0) by admit.
             rewrite encode_decode_int32_same_prefix.
             2: auto.
             simpl.
             rewrite HRelocOfs in EQ1.
             unfold get_instr_reloc_addend' in EQ1.
             unfold get_reloc_addend in EQ1.
             unfold find_ofs_in_rtbl.
             destruct ( ZTree.get (iofs + sofs) rtbl_ofs_map); inversion EQ1.
           
             simpl.
             rewrite byte_eq_true; auto.
             rewrite byte_eq_true; auto.
             generalize (encode_int32_4_exists x0 l (encode_int32 x0 ++ l) eq_refl).
             intros (b1 & b2 & b3 & b4 & HEncInt).
             rewrite HEncInt.
             simpl.

             simpl. repeat f_equal.
             auto.
             unfold addrmode_SIB_parse_index.
             rewrite H12.
             rewrite byte_eq_false. auto.
             (* RSP *)
             intros HNot.
             resolve_rsp x3.
             rewrite Ptrofs.unsigned_repr.
             auto.
             unfold valid_int32 in Hvalid.
             unfold two_power_pos in Hvalid.
             simpl in Hvalid.
             unfold Ptrofs.max_unsigned.
             unfold Ptrofs.modulus.
             unfold two_power_nat. unfold Ptrofs.wordsize.
             unfold Wordsize_Ptrofs.wordsize. destruct Archi.ptr64 eqn:EQAR;inversion EQAR.
             generalize (encode_parse_reg_refl _ _ EQ0).
             rewrite H.
             intros HRdEQ. inversion HRdEQ. auto.
             simpl. omega.
             1-9: intros HNot; inversion HNot.             
    ++
      monadInv EQ.
      destruct base eqn:EQB.
      +++ monadInv EQ2.
          destruct(ireg_eq i0 RSP).
          ++++ monadInv EQ3.
               unfold decode_addrmode.
               simpl.
               assert(HTurncate:
                        (Byte.repr
                           (bits_to_Z
                              (char_to_bool "1"
                                            :: char_to_bool "0"
                                            :: x1 ++
                                            char_to_bool "1"
                                            :: char_to_bool "0"
                                            :: char_to_bool "0"
                                            :: char_to_bool "0"
                                            :: char_to_bool "0"
                                            :: char_to_bool "1"
                                            :: char_to_bool "0"
                                            ::
                                            char_to_bool "0" :: x2) /
                              256)) = bB[b["10"]++x1++b["100"]]). {
                replace (char_to_bool "1"
                                       :: char_to_bool "0"
                                       :: x1 ++
                                       char_to_bool "1"
                                       :: char_to_bool "0"
                                       :: char_to_bool "0"
                                       :: char_to_bool "0"
                                       :: char_to_bool "0"
                                       :: char_to_bool "1"
                                       :: char_to_bool "0"
                                       ::
                                       char_to_bool "0" :: x2)
              with
                ((char_to_bool "1"
                                       :: char_to_bool "0"
                                       :: x1 ++
                                       char_to_bool "1"
                                       :: char_to_bool "0"
                                       :: char_to_bool "0"
                                       ::[])++ (char_to_bool "0"
                                       :: char_to_bool "0"
                                       :: char_to_bool "1"
                                       :: char_to_bool "0"
                                       ::
                                       char_to_bool "0" :: x2)).
            replace 256 with (2^8).
            rewrite <- Z.shiftr_div_pow2.
            rewrite (Z_shru_bits 8).
            auto.
            simpl.
            resolve_reg_length x2. omega. omega.
            simpl.
            unfold Z.pow_pos. simpl. auto.
            repeat rewrite app_comm_cons.
            rewrite <- app_assoc.
            auto.
               }
                 
               rewrite HTurncate.
               assert(HEQx1:(Byte.shru
        (Byte.and bB[ b[ "10"] ++ x1 ++ b[ "100"]] (Byte.repr 56))
        (Byte.repr 3)) = bB[x1]). {
                 rewrite <- Byte.and_shru.
                 rewrite shru563.
                 replace  ( b[ "10"] ++ x1 ++ b[ "100"])
               with
                 ( (b[ "10"] ++ x1) ++ (b[ "100"])).
             rewrite (shru_bits 3 _ _).
             setoid_rewrite (and7 b["10"] x1).
             all:auto.

             all: repeat rewrite app_length; simpl.
             all:rewrite (encode_reg_length rd x1); try omega.
             all: auto.
               }
               rewrite HEQx1.
               generalize (encode_decode_ireg_refl _ _ EQ0).
               intros Hrd.
               destruct Hrd.
               destruct H as [H H12].
               rewrite H. rewrite H12. simpl.
               assert(HEQ2: (Byte.shru
                               bB[ char_to_bool "1"
                                                :: char_to_bool "0"
                                                :: x1 ++
                                                [char_to_bool "1"; char_to_bool "0";
                                                 char_to_bool "0"]] (Byte.repr 6))=Byte.repr 2). {
                 replace (char_to_bool "1"
        :: char_to_bool "0"
           :: x1 ++
              [char_to_bool "1"; char_to_bool "0";
               char_to_bool "0"])
                   with ((char_to_bool "1"
        :: char_to_bool "0"::[]) ++ (x1 ++
              [char_to_bool "1"; char_to_bool "0";
               char_to_bool "0"])).
                 rewrite (shru_bits 6).
                 f_equal.
                 1-2: repeat rewrite app_length; simpl;
                   resolve_reg_length x1; simpl; omega.
                 simpl. auto.
               }
               rewrite HEQ2.
               rewrite byte_eq_false.
               rewrite byte_eq_false.
               rewrite byte_eq_true; auto.
               assert(HEQ4: (Byte.and
                               bB[ char_to_bool "1"
                                                :: char_to_bool "0"
                                                :: x1 ++
                                                [char_to_bool "1"; char_to_bool "0";
                                                 char_to_bool "0"]] (Byte.repr 7)) = Byte.repr 4). {
                 replace (char_to_bool "1":: char_to_bool "0":: x1 ++[char_to_bool "1"; char_to_bool "0";char_to_bool "0"])
                         with ((char_to_bool "1":: char_to_bool "0":: x1) ++[char_to_bool "1"; char_to_bool "0";char_to_bool "0"]).
               rewrite and7.
               f_equal.
                all: repeat rewrite app_length;
                  try resolve_reg_length x1; simpl.
                resolve_reg_length x1.
                1-2: omega.
                simpl. auto.

               }
               rewrite HEQ4.
               unfold addrmode_parse_reg.
               do 4 (try(rewrite byte_eq_false)).
               rewrite byte_eq_true;auto.
               simpl.
               rewrite byte_eq_true.
               assert(Hmod:  bB[ char_to_bool "1"
                                              :: char_to_bool "0"
                                              :: x1 ++
                                              char_to_bool "1"
                                              :: char_to_bool "0"
                                              :: char_to_bool "0"
                                              :: char_to_bool "0"
                                              :: char_to_bool "0"
                                              :: char_to_bool "1"
                                              :: char_to_bool "0" :: char_to_bool "0" :: x2] = bB[b["00100"]++x2]). {
                 replace (char_to_bool "1"
                                              :: char_to_bool "0"
                                              :: x1 ++
                                              char_to_bool "1"
                                              :: char_to_bool "0"
                                              :: char_to_bool "0"
                                              :: char_to_bool "0"
                                              :: char_to_bool "0"
                                              :: char_to_bool "1"
                                              :: char_to_bool "0" :: char_to_bool "0" :: x2)
                   with ((char_to_bool "1"
                                              :: char_to_bool "0"
                                              :: x1 ++
                                              char_to_bool "1"
                                              :: char_to_bool "0"
                                              :: char_to_bool "0"::[])++(char_to_bool "0":: char_to_bool "0":: char_to_bool "1":: char_to_bool "0" :: char_to_bool "0" :: x2)).
                 apply BbTruncate.
                 simpl. resolve_reg_length x2.
                 omega.
                 repeat rewrite app_comm_cons.
                 rewrite <- app_assoc.
                 auto.
               }
               rewrite Hmod.
               unfold addrmode_parse_SIB.
               assert(HEQ4_2:(Byte.shru (Byte.and bB[ b[ "00100"] ++ x2] (Byte.repr 56)) (Byte.repr 3)) = Byte.repr 4). {
                 rewrite <- Byte.and_shru.
                 rewrite shru563.
                 rewrite (shru_bits 3 _ _).
                 setoid_rewrite (and7 b["00"] b["100"]).
                 all:auto.
                 rewrite app_length; simpl.
                 all: rewrite (encode_reg_length RSP x2); try omega; auto.
               }
               rewrite HEQ4_2.
               unfold addrmode_parse_reg.
               do 4 (try(rewrite byte_eq_false)).
               rewrite byte_eq_true; auto.
               simpl.
               assert(HEQ0: (Byte.shru
                               bB[ char_to_bool "0"
                                                :: char_to_bool "0"
                                                :: char_to_bool "1" :: char_to_bool "0" :: char_to_bool "0" :: x2](Byte.repr 6)) = Byte.repr 0). {
                 replace ( char_to_bool "0"
        :: char_to_bool "0"
           :: char_to_bool "1"
           :: char_to_bool "0" :: char_to_bool "0" :: x2)
                         with ( (char_to_bool "0"
        :: char_to_bool "0"::[])++ char_to_bool "1"
                              :: char_to_bool "0" :: char_to_bool "0" :: x2).
                 rewrite (shru_bits 6).
                 f_equal.
                 1-2: simpl; resolve_reg_length x2; omega.
                 simpl. auto.
               }
               rewrite HEQ0.
               unfold addrmode_SIB_parse_scale.
               rewrite byte_eq_true; auto.
               assert(HEQx2: (Byte.and
                                bB[ char_to_bool "0"
                                                 :: char_to_bool "0"
                                                 :: char_to_bool "1" :: char_to_bool "0" :: char_to_bool "0" :: x2](Byte.repr 7)) = bB[x2]). {
                 replace (char_to_bool "0"
        :: char_to_bool "0"
           :: char_to_bool "1"
           :: char_to_bool "0" :: char_to_bool "0" :: x2) with
                    ((char_to_bool "0"
        :: char_to_bool "0"
           :: char_to_bool "1"
              :: char_to_bool "0" :: char_to_bool "0" :: []) ++ x2).
                 rewrite and7.
                 auto. simpl.
                 1-2: resolve_reg_length x2; omega.
                 simpl; auto.
               }
               rewrite HEQx2.
               simpl.
               fold (addrmode_parse_reg bB[x2]).
               generalize (encode_decode_ireg_refl _ _ EQ).
               intros HEQRSP.
               destruct HEQRSP. destruct H10 as [H13 H14].
               rewrite H13. rewrite H14. simpl.
               unfold addrmode_SIB_parse_base.
               unfold encode_ireg in EQ.
               inversion EQ.
               rewrite byte_eq_false.
               do 2 (try (rewrite byte_eq_false)).
               rewrite byte_eq_true; auto.
               simpl.
               rewrite HRelocOfs in EQ1.
               unfold get_instr_reloc_addend' in EQ1.
               unfold get_reloc_addend in EQ1.
               unfold find_ofs_in_rtbl.
               destruct ( ZTree.get (iofs + sofs) rtbl_ofs_map); inversion EQ1.
               assert (Hvalid: valid_int32 x0) by admit.
               generalize (encode_decode_int32_same_prefix _ l Hvalid).
               intros Hint.
               rewrite Hint.
               simpl.

               
               rewrite byte_eq_false. simpl.
               repeat f_equal.
               generalize (encode_int32_4_exists x0 l (encode_int32 x0 ++ l) eq_refl).
               intros (b1 & b2 & b3 & b4 & HEncInt).
               rewrite HEncInt.
               simpl.
               
               rewrite Ptrofs.unsigned_repr.
               auto.
               unfold valid_int32 in Hvalid.
               unfold two_power_pos in Hvalid.
               simpl in Hvalid.
               unfold Ptrofs.max_unsigned.
               unfold Ptrofs.modulus.
               unfold two_power_nat. unfold Ptrofs.wordsize.
               unfold Wordsize_Ptrofs.wordsize. destruct Archi.ptr64 eqn:EQAR;inversion EQAR.
               simpl. omega.
               1-14: intros HNot; inversion HNot.
               
          ++++
            inversion EQ3.
            unfold decode_addrmode.
            simpl.
            assert(HEQx1:(Byte.shru
                            (Byte.and bB[ char_to_bool "1" :: char_to_bool "0" :: x1 ++ x2] (Byte.repr 56))(Byte.repr 3)) = bB[x1]). {
              rewrite <- Byte.and_shru.
              rewrite shru563.
              replace (char_to_bool "1" :: char_to_bool "0" :: x1 ++ x2)
                with
                  ((char_to_bool "1" :: char_to_bool "0" :: x1) ++ x2).
              rewrite (shru_bits 3 _ _).
              setoid_rewrite (and7 (char_to_bool "1" :: [char_to_bool "0"]) x1).
              auto.

              1,3,4: repeat rewrite app_length; simpl.
              1,2,4:rewrite (encode_reg_length rd x1); try omega.
              1-8: auto.
              all: rewrite (encode_reg_length i0 x2); try omega; auto.
            }
            rewrite HEQx1.
            generalize(encode_decode_ireg_refl _ _ EQ0).
            intros Hrd.
            destruct Hrd. destruct H as [H H13].
            rewrite H. rewrite H13. simpl.
            assert(HEQ2: (Byte.shru bB[ char_to_bool "1" :: char_to_bool "0" :: x1 ++ x2] (Byte.repr 6)) = Byte.repr 2). {
              replace (char_to_bool "1" :: char_to_bool "0" :: x1 ++ x2) with ((char_to_bool "1" :: char_to_bool "0" ::[])++ (x1 ++ x2)).
              rewrite (shru_bits 6).
              f_equal.
              1-2: repeat rewrite app_length; resolve_reg_length x1;
                resolve_reg_length x2; simpl;omega.
              auto.
            }
            rewrite HEQ2.
            rewrite byte_eq_false.
            rewrite byte_eq_false.
            rewrite byte_eq_true; auto.
            assert(HEQx2: (Byte.and bB[ char_to_bool "1" :: char_to_bool "0" :: x1 ++ x2] (Byte.repr 7)) = bB[x2]). {
              replace (char_to_bool "1" :: char_to_bool "0" :: x1 ++ x2) with  ((char_to_bool "1" :: char_to_bool "0" :: x1) ++ x2).
              rewrite and7.
              auto.
              1-2: repeat rewrite app_length; simpl;
                try resolve_reg_length x1;
                resolve_reg_length x2; omega.
              auto.
            }
              
            rewrite HEQx2.
            generalize (encode_decode_ireg_refl _ _ EQ).
            intros Hri. destruct Hri as [reg1 H14].
            destruct H14 as [H14 H15].
            rewrite H14. rewrite H15.
            simpl.
            assert(HNE4: bB[x2] <> Byte.repr 4). {
              intros HNot.
              destruct i0;
              simpl in EQ;
              monadInv EQ;
              inversion HNot.
              auto.
            }
            rewrite byte_eq_false.
            rewrite HRelocOfs in EQ1.
            simpl in EQ1.            
            unfold get_instr_reloc_addend' in EQ1.
            unfold get_reloc_addend in EQ1.
            unfold find_ofs_in_rtbl.
            destruct(ZTree.get (iofs+sofs) rtbl_ofs_map);inversion EQ1.
            repeat f_equal.            
            assert (Hvalid: valid_int32 x0) by admit.
            generalize (encode_decode_int32_same_prefix _ l Hvalid).
            intros Hint.
            rewrite Hint.
            auto.
            intros HNot.
            resolve_rsp x2.

            1-2: intros HNot; inversion HNot.

      +++ unfold decode_addrmode.
          inversion EQ2.
          simpl.
          assert(HEQx1: (Byte.shru
                           (Byte.and
                              bB[ char_to_bool "0"
                                               :: char_to_bool "0"
                                               :: x1 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"]](Byte.repr 56)) (Byte.repr 3)) = bB[x1]). {
            rewrite <- Byte.and_shru.
            rewrite shru563.
            replace (char_to_bool "0"
           :: char_to_bool "0"
              :: x1 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"])
              with
                ((char_to_bool "0"
           :: char_to_bool "0"
              :: x1) ++ ([char_to_bool "1"; char_to_bool "0"; char_to_bool "1"])).
            rewrite (shru_bits 3 _ _).
            setoid_rewrite (and7 (char_to_bool "0" :: [char_to_bool "0"]) x1).
            all: auto.

            1,3,4: repeat rewrite app_length; simpl.
            all:rewrite (encode_reg_length rd x1); try omega.
            1-8: auto.
          }
          rewrite HEQx1.
          generalize (encode_decode_ireg_refl _ _ EQ0).
          intros Hrd.
          destruct Hrd. destruct H as [H H13]. rewrite H.
          rewrite H13. simpl.
          assert(HEQ0:  (Byte.shru
                           bB[ char_to_bool "0"
                                            :: char_to_bool "0"
                                            :: x1 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"]](Byte.repr 6)) = Byte.repr 0). {
            replace (char_to_bool "0"
        :: char_to_bool "0"
           :: x1 ++
              [char_to_bool "1"; char_to_bool "0";
               char_to_bool "1"])
              with
                ((char_to_bool "0"
        :: char_to_bool "0"::[]) ++ (x1 ++
              [char_to_bool "1"; char_to_bool "0";
               char_to_bool "1"])).
            setoid_rewrite(shru_bits 6).
            f_equal.
            1-2: repeat rewrite app_length; simpl.
            1-2: resolve_reg_length x1.
            1-2: omega.
            auto.
          }
          rewrite HEQ0.
          rewrite byte_eq_true; auto.
          assert(HEQ5: (Byte.and
                          bB[ char_to_bool "0"
                                           :: char_to_bool "0"
                                           :: x1 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"]](Byte.repr 7)) = Byte.repr 5). {
            setoid_rewrite and7.
            f_equal.
            1-2: repeat rewrite app_length; simpl.
            resolve_reg_length x1.
            all: omega.
          }
          rewrite HEQ5.
          unfold addrmode_parse_reg.
          do 5(try(rewrite byte_eq_false)).
          rewrite byte_eq_true; auto.
          simpl.
          rewrite byte_eq_false.
          rewrite byte_eq_true; auto.
          rewrite HRelocOfs in EQ1.
          simpl in EQ1.
          unfold get_instr_reloc_addend' in EQ1.
          unfold get_reloc_addend in EQ1.
          unfold find_ofs_in_rtbl.
          destruct(ZTree.get (iofs+sofs) rtbl_ofs_map); inversion EQ1.
          repeat f_equal.
          assert (Hvalid: valid_int32 x0) by admit.
          generalize (encode_decode_int32_same_prefix _ l Hvalid).
          intros Hint.
          rewrite Hint.
          auto.
          1-6:
          intros HNot; inversion HNot.

           
  +

    (* inversion EQ2. *)
    unfold encode_addrmode_aux in EQ.
    destruct ofs eqn:EQOFS.
    
    ++ monadInv EQ.
       destruct p0 eqn:EQP0.
       +++ destruct base eqn: EQB.
           ++++
             destruct (ireg_eq i0 RSP); monadInv EQ2.
             destruct p eqn:EQP.
             destruct i2; try monadInv EQ1.
             unfold decode_addrmode.
             simpl.
             assert(HEQX1: Byte.shru
                       (Byte.and
                          (Byte.repr
                             (bits_to_Z
                                (char_to_bool "1"
                                              :: char_to_bool "0"
                                              :: x1 ++
                                              char_to_bool "1"
                                              :: char_to_bool "0" :: char_to_bool "0" :: x2 ++ x3 ++ x4) / 256))(Byte.repr 56)) (Byte.repr 3) = bB[x1]). {
               rewrite <- Byte.and_shru.
               rewrite shru563.
               replace 256 with (2^8).
               rewrite <- Z.shiftr_div_pow2.
               replace  (char_to_bool "1"
                                      :: char_to_bool "0"
                                      :: x1 ++
                                      char_to_bool "1"
                                      :: char_to_bool "0" :: char_to_bool "0" :: x2 ++ x3 ++ x4)
                 with
                   (((char_to_bool "1"
                                   :: char_to_bool "0"
                                   :: x1) ++
                                          (char_to_bool "1"
                                                        :: char_to_bool "0" :: [char_to_bool "0"])) ++ (x2 ++ x3 ++ x4)).
               
               setoid_rewrite (Z_shru_bits 8 ((char_to_bool "1"
                                                            :: char_to_bool "0"
                                                            :: x1) ++
                                                                   (char_to_bool "1"
                                                                                 :: char_to_bool "0" :: [char_to_bool "0"]))  (x2 ++ x3 ++ x4)).
               rewrite (shru_bits 3 _ _).
               setoid_rewrite (and7 (char_to_bool "1" :: [char_to_bool "0"]) x1).
               auto.

               1,3,4: repeat rewrite app_length; simpl.
               1,2,4:rewrite (encode_reg_length rd x1); try omega.
               1-8: auto.
               repeat rewrite app_length. 
               rewrite (encode_scale_length z).
               rewrite (encode_reg_length i0).
               rewrite (encode_reg_length i1).
               omega.
               all: auto.
               repeat rewrite <- app_assoc.
               auto.
               omega.
             }
             rewrite HEQX1.
             generalize (encode_decode_ireg_refl _ _  EQ0).
             intros HRx1.
             destruct HRx1. destruct H.
             rewrite H. simpl.
             assert(HEQ2: (Byte.shru
                             (Byte.repr
                                (bits_to_Z
                                   (char_to_bool "1"
                                                 :: char_to_bool "0"
                                                 :: x1 ++
                                                 char_to_bool "1"
                                                 :: char_to_bool "0" :: char_to_bool "0" :: x2 ++ x3 ++ x4) / 256)) (Byte.repr 6)) = Byte.repr 2). {
               replace 256 with (2^8).
               rewrite <- Z.shiftr_div_pow2.
               replace (char_to_bool "1"
              :: char_to_bool "0"
                 :: x1 ++
                    char_to_bool "1"
                    :: char_to_bool "0"
                    :: char_to_bool "0" :: x2 ++ x3 ++ x4)
                 with
                   ((char_to_bool "1"
              :: char_to_bool "0"
                 :: x1 ++
                    char_to_bool "1"
                    :: char_to_bool "0"
                    :: char_to_bool "0"::[]) ++ (x2 ++ x3 ++ x4)).
               rewrite (Z_shru_bits 8).
               replace ( char_to_bool "1"
                                      :: char_to_bool "0"
                                      :: x1 ++
                                      [char_to_bool "1"; char_to_bool "0";char_to_bool "0"])
                 with ( (char_to_bool "1"
        :: char_to_bool "0"::[]) ++ (x1 ++
              [char_to_bool "1"; char_to_bool "0";
              char_to_bool "0"])).
               rewrite (shru_bits 6).
               f_equal.
               1,2,4: repeat rewrite app_length;
                 simpl;
                 try resolve_reg_length x1;
                 try resolve_reg_length x3;
                 try resolve_reg_length x4;
                 try resolve_scale_length x2;
                 omega.
               auto.
               repeat rewrite app_comm_cons.
               rewrite <- app_assoc.
               auto.
               omega.
               simpl. unfold Z.pow_pos.
               simpl. omega.
             }
             rewrite HEQ2.
             branch_byte_eq.
             assert(HEQ4: (Byte.and
                             (Byte.repr
                                (bits_to_Z
                                   (char_to_bool "1"
                                                 :: char_to_bool "0"
                                                 :: x1 ++
                                                 char_to_bool "1"
                                                 :: char_to_bool "0" :: char_to_bool "0" :: x2 ++ x3 ++ x4) / 256)) (Byte.repr 7)) = Byte.repr 4). {
               replace 256 with (2^8).
               rewrite <- Z.shiftr_div_pow2.
                replace (char_to_bool "1"
              :: char_to_bool "0"
                 :: x1 ++
                    char_to_bool "1"
                    :: char_to_bool "0"
                    :: char_to_bool "0" :: x2 ++ x3 ++ x4)
                 with
                   ((char_to_bool "1"
              :: char_to_bool "0"
                 :: x1 ++
                    char_to_bool "1"
                    :: char_to_bool "0"
                    :: char_to_bool "0"::[]) ++ (x2 ++ x3 ++ x4)).
                rewrite (Z_shru_bits 8).
                replace (char_to_bool "1"
        :: char_to_bool "0"
           :: x1 ++
              [char_to_bool "1"; char_to_bool "0";
               char_to_bool "0"])
                  with
                    ((char_to_bool "1" :: char_to_bool "0":: x1) ++
                                  ([char_to_bool "1"; char_to_bool "0";char_to_bool "0"])).
                rewrite and7.
                f_equal.
                1,2,4: repeat rewrite app_length;
                  simpl;
                  try resolve_reg_length x1;
                  try resolve_reg_length x3;
                  try resolve_reg_length x4;
                  try resolve_scale_length x2;
                  omega.
                auto.
                repeat rewrite app_comm_cons.
                repeat rewrite <- app_assoc.
                auto.
                omega.
                simpl. unfold Z.pow_pos.
                simpl; auto.

             }
             rewrite HEQ4.
             assert(HEQRSP: addrmode_parse_reg (Byte.repr 4) = OK RSP). {
               unfold addrmode_parse_reg.
               branch_byte_eq.
               auto.
             }
             rewrite HEQRSP.
             simpl.
             rewrite byte_eq_true.
             unfold addrmode_parse_SIB.
             assert(HbBTruncate: bB[ char_to_bool "1"
                                                  :: char_to_bool "0"
                                                  :: x1 ++
                                                  char_to_bool "1"
                                                  :: char_to_bool "0" :: char_to_bool "0" :: x2 ++ x3 ++ x4] = bB[x2++x3++x4]). {
               replace ( char_to_bool "1"
      :: char_to_bool "0"
         :: x1 ++
            char_to_bool "1"
            :: char_to_bool "0"
            :: char_to_bool "0" :: x2 ++ x3 ++ x4)
                 with
                   ( (char_to_bool "1"
      :: char_to_bool "0"
         :: x1 ++
            char_to_bool "1"
            :: char_to_bool "0"
               :: char_to_bool "0" ::[])++ (x2 ++ x3 ++ x4)).
               apply BbTruncate.
               repeat rewrite app_length.
               resolve_scale_length x2.
               resolve_reg_length x3.
               resolve_reg_length x4.
               omega.
               repeat rewrite app_comm_cons.
               rewrite <- app_assoc.
               auto.
             }
             rewrite HbBTruncate.
             assert (HEQX3:Byte.shru (Byte.and bB[ x2 ++ x3 ++ x4] (Byte.repr 56)) (Byte.repr 3) = bB[x3]). {
               rewrite <- Byte.and_shru.
               rewrite shru563.
               rewrite app_assoc.
               rewrite (shru_bits 3 _ _).
               setoid_rewrite (and7 x2 x3).
               all:auto.
               1,3: repeat rewrite app_length; simpl.
               1-3: rewrite (encode_reg_length i0 x3).
               1,3: rewrite (encode_scale_length z).
               all: auto; try omega.
               all: rewrite (encode_reg_length i1 x4); try omega.
               all: auto.
             }
             rewrite HEQX3.
             generalize (encode_decode_ireg_refl _ _  EQ2).
             intros HRi.
             destruct HRi. destruct H11.
             rewrite H11. rewrite H12. simpl.
             assert(HEQx2: (Byte.shru bB[ x2 ++ x3 ++ x4] (Byte.repr 6)) = bB[x2]). {
               setoid_rewrite (shru_bits 6 x2 (x3++x4)).
               auto.
               all:repeat rewrite app_length.
               all: try resolve_scale_length x2.
               all: try resolve_reg_length x3.
               all: try resolve_reg_length x4.
               all: omega.
             }
             rewrite HEQx2.
             rewrite (encode_parse_scale_refl _ _ EQ).
             simpl.
             assert(HEQx4: (Byte.and bB[ x2 ++ x3 ++ x4] (Byte.repr 7)) = bB[x4]). {
               rewrite app_assoc.
               rewrite (and7 (x2++x3) x4).
               auto.
               all:repeat rewrite app_length.
               all: try resolve_scale_length x2.
               all: try resolve_reg_length x3.
               all: try resolve_reg_length x4.
               all: omega.
             }
               
             rewrite HEQx4.
             generalize(encode_decode_ireg_refl _ _ EQ3).
             intros HRi0. destruct HRi0. destruct H13.
             rewrite H13. rewrite H14. simpl.
             unfold addrmode_SIB_parse_base.
             destruct (Byte.eq_dec bB[ x4] HB[ "5"]) eqn:EQx4.
             +++++
               rewrite byte_eq_false.
             rewrite byte_eq_false.
             rewrite byte_eq_true.
             simpl.
             rewrite HRelocOfs in EQ4.
             inversion EQ4. subst x.
             unfold get_instr_reloc_addend' in EQ1.
             unfold find_ofs_in_rtbl.
             unfold get_reloc_addend in EQ1.
             destruct (ZTree.get (iofs+sofs) rtbl_ofs_map) eqn:EQREloc ; inversion EQ1.
             
             
             assert (Hvalid: valid_int32 (Ptrofs.unsigned i3)). {
               unfold valid_int32.
               generalize (Ptrofs.unsigned_range i3).
               unfold Ptrofs.modulus.
               unfold Ptrofs.wordsize.
               unfold Wordsize_Ptrofs.wordsize.
               destruct Archi.ptr64 eqn:EQA; inversion EQA.
               unfold two_power_nat. simpl.
               unfold two_power_pos. simpl.
               omega.
             }
             (* rewrite H17. *)
             generalize (encode_decode_int32_same_prefix _ l Hvalid).
             intros Hint.
             rewrite Hint.
             simpl.


             rewrite byte_eq_false.
             simpl.
             repeat f_equal.
             auto.
             unfold addrmode_SIB_parse_index.
             destruct (Byte.eq_dec bB[x3] HB["4"]).
             generalize (encode_int32_4_exists (Ptrofs.unsigned i3) l ( encode_int32 (Ptrofs.unsigned i3) ++ l) eq_refl).
             intros (b1 & b2 & b3 & b4 & HEncInt).
             rewrite HEncInt.
             simpl.
             ++++++ resolve_rsp x3.
             ++++++
               generalize (encode_int32_4_exists (Ptrofs.unsigned i3) l ( encode_int32 (Ptrofs.unsigned i3) ++ l) eq_refl).
             intros (b1 & b2 & b3 & b4 & HEncInt).
             rewrite HEncInt.
             simpl. 
             subst x0.
             rewrite Ptrofs.repr_unsigned.
             auto.
             (* ++++++ auto. *)
             ++++++ intros HNot. inversion HNot.
             ++++++ intros HNot. inversion HNot.
             ++++++ intros HNot. inversion HNot.

             +++++
               rewrite byte_eq_false. rewrite byte_eq_false. rewrite byte_eq_true.
             simpl.
             rewrite HRelocOfs in EQ4.
             inversion EQ4.
             subst x.
             unfold get_instr_reloc_addend' in EQ1.
             unfold find_ofs_in_rtbl.
             unfold get_reloc_addend in EQ1.
             destruct (ZTree.get (iofs+sofs) rtbl_ofs_map); inversion EQ1.
             assert (Hvalid: valid_int32 (Ptrofs.unsigned i3)). {
               unfold valid_int32.
               generalize (Ptrofs.unsigned_range i3).
               unfold Ptrofs.modulus.
               unfold Ptrofs.wordsize.
               unfold Wordsize_Ptrofs.wordsize.
               destruct Archi.ptr64 eqn:EQA; inversion EQA.
               unfold two_power_nat. simpl.
               unfold two_power_pos. simpl.
               omega.
             }
               
             generalize (encode_decode_int32_same_prefix _ l Hvalid).
             intros Hint.
             rewrite Hint.
             simpl.
             
             rewrite byte_eq_false.
             simpl. repeat f_equal.
             auto.
             unfold addrmode_SIB_parse_index.
             destruct(Byte.eq_dec bB[x3] HB["4"]).
             generalize (encode_int32_4_exists (Ptrofs.unsigned i3) l (encode_int32 (Ptrofs.unsigned i3) ++ l) eq_refl).
             intros (b1 & b2 & b3 & b4 & HEncInt).
             rewrite HEncInt.
             simpl.             
             
             ++++++ resolve_rsp x3.
             ++++++
               generalize (encode_int32_4_exists (Ptrofs.unsigned i3) l (encode_int32 (Ptrofs.unsigned i3) ++ l) eq_refl).
             intros (b1 & b2 & b3 & b4 & HEncInt).
             rewrite HEncInt.
             simpl. subst rd.
             rewrite Ptrofs.repr_unsigned.
             auto.
             
             (* ++++++ auto. *)
             ++++++ intros HNot. inversion HNot.
             ++++++ intros HNot. inversion HNot.
             ++++++ intros HNot. inversion HNot.
             
           ++++
             destruct (ireg_eq i0 RSP); monadInv EQ2.
             unfold decode_addrmode. simpl.
             assert(Hdiv256:  (bits_to_Z
                 (char_to_bool "0"
                  :: char_to_bool "0"
                     :: x1 ++
                        char_to_bool "1"
                        :: char_to_bool "0"
                           :: char_to_bool "0"
                              :: x2 ++
                                 x3 ++
                                 [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"]) /
               256) = bits_to_Z
                        (char_to_bool "0"
                                      :: char_to_bool "0"
                                      :: x1 ++
                                      char_to_bool "1"
                                      :: char_to_bool "0"
                                      :: char_to_bool "0"::[])). {
               replace 256 with (2^8).
               rewrite <- Z.shiftr_div_pow2.
               replace 
       (char_to_bool "0"
        :: char_to_bool "0"
           :: x1 ++
              char_to_bool "1"
              :: char_to_bool "0"
                 :: char_to_bool "0"
                    :: x2 ++
                       x3 ++
                       [char_to_bool "1"; char_to_bool "0";
                        char_to_bool "1"])
         with ((char_to_bool "0"
        :: char_to_bool "0"
           :: x1 ++
              char_to_bool "1"
              :: char_to_bool "0"
              :: char_to_bool "0"::[])++(x2++x3++[char_to_bool "1"; char_to_bool "0";char_to_bool "1"])).          
               setoid_rewrite (Z_shru_bits 8).
               auto.
               all: repeat rewrite app_length.
               all: try resolve_scale_length x2.
               all: try resolve_reg_length x3.
               all: try resolve_reg_length x4.
               all: simpl.
               omega.
               repeat rewrite<- app_assoc.
               auto.
               omega.
               unfold Z.pow_pos.
               simpl. auto.
             }
             rewrite Hdiv256.
             simpl.
             assert(HEQx1: Byte.shru
                             (Byte.and
                                bB[ char_to_bool "0"
                                                 :: char_to_bool "0"
                                                 :: x1 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "0"]](Byte.repr 56)) (Byte.repr 3) = bB[x1]). {
               rewrite <- Byte.and_shru.
               rewrite shru563.
               replace (char_to_bool "0"
           :: char_to_bool "0"
              :: x1 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "0"])
                 with
                   ((char_to_bool "0"
           :: char_to_bool "0"
              :: x1) ++ ([char_to_bool "1"; char_to_bool "0"; char_to_bool "0"])).
               rewrite (shru_bits 3 _ _).
               setoid_rewrite (and7 (char_to_bool "0" :: [char_to_bool "0"]) x1).
               auto.

               all: repeat rewrite app_length; simpl.
               1-3:rewrite (encode_reg_length rd x1); try omega.
               1-8: auto.
             }
             rewrite HEQx1.
             generalize (encode_decode_ireg_refl _ _ EQ0).
             intros Hreg1. destruct Hreg1.
             destruct H. rewrite H. simpl.
             assert(Heq0: Byte.shru
                            bB[ char_to_bool "0"
                                             :: char_to_bool "0"
                                             :: x1 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "0"]](Byte.repr 6) = Byte.repr 0). {
               replace (bB[ char_to_bool "0"
                                             :: char_to_bool "0"
                                             :: x1 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "0"]])
                 with
                   (bB[ (char_to_bool "0"
                                             :: char_to_bool "0"::[])++x1 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "0"]]
                   ).
               setoid_rewrite (shru_bits 6).
               f_equal.
               all: repeat rewrite app_length;
                 try resolve_reg_length x1; simpl.
               1-2: omega.
               auto.
             }
             rewrite Heq0.
             rewrite byte_eq_true.
             assert(Heq4: Byte.and
                            bB[ char_to_bool "0"
                                             :: char_to_bool "0"
                                             :: x1 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "0"]](Byte.repr 7) = Byte.repr 4). {

               replace (char_to_bool "0"
        :: char_to_bool "0"
           :: x1 ++
              [char_to_bool "1"; char_to_bool "0";
               char_to_bool "0"]) with
                   ((char_to_bool "0"
        :: char_to_bool "0"
           :: x1) ++
              ([char_to_bool "1"; char_to_bool "0";
                char_to_bool "0"])).
               rewrite and7.
               f_equal.
                all: repeat rewrite app_length;
                  try resolve_reg_length x1; simpl.
                resolve_reg_length x1.
                1-2: omega.
                simpl. auto.
             }
             rewrite Heq4.
             unfold addrmode_parse_reg.
             do 4 (try (rewrite byte_eq_false)).
             rewrite byte_eq_true; auto.
             simpl.
             rewrite byte_eq_true; auto.
             assert(HTruncate:
                      bB[ char_to_bool "0"
                                       :: char_to_bool "0"
                                       :: x1 ++
                                       char_to_bool "1"
                                       :: char_to_bool "0"
                                       :: char_to_bool "0"
                                       :: x2 ++
                                       x3 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"]] = bB[x2 ++ x3 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"]]). {
               replace (char_to_bool "0"
                                       :: char_to_bool "0"
                                       :: x1 ++
                                       char_to_bool "1"
                                       :: char_to_bool "0"
                                       :: char_to_bool "0"
                                       :: x2 ++
                                       x3 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"])
                 with
                   ((char_to_bool "0"
                                       :: char_to_bool "0"
                                       :: x1 ++
                                       char_to_bool "1"
                                       :: char_to_bool "0"
                                       :: char_to_bool "0"::[])
                                       ++ (x2 ++
                                       x3 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"])).
               apply BbTruncate.
               repeat rewrite app_length.
               resolve_reg_length x3.
               resolve_scale_length x2.
               simpl. omega.
               simpl.
               repeat rewrite app_comm_cons.
               rewrite <- app_assoc.
               auto.
             }
             rewrite HTruncate.
             unfold addrmode_parse_SIB.
             assert(HEQx3: Byte.shru
                             (Byte.and
                                bB[ x2 ++ x3 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"]](Byte.repr 56)) (Byte.repr 3) = bB[x3]). {
               rewrite <- Byte.and_shru.
               rewrite shru563.
               replace ( x2 ++ x3 ++ ([char_to_bool "1"; char_to_bool "0"; char_to_bool "1"]))
                 with
                   ( (x2 ++ x3) ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"]).
               rewrite (shru_bits 3 _ _).
               setoid_rewrite (and7 x2 x3).
               all: auto.
               1,3: repeat rewrite app_length; simpl.
               1-2: try rewrite(encode_scale_length z).
               all: try rewrite(encode_reg_length i0).
               all: try omega; auto.
               repeat rewrite app_assoc. auto.
             }
             rewrite HEQx3.
             generalize(encode_decode_ireg_refl _ _ EQ2).
             intros Hregi.
             destruct Hregi. destruct H11.
             rewrite H11.
             simpl.
             assert(HEQx2: Byte.shru bB[ x2 ++ x3 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"]](Byte.repr 6) = bB[x2]). {
               rewrite (shru_bits 6).
               auto.
               1-2: repeat rewrite app_length.
               1-2: try resolve_scale_length x2;
                 try resolve_reg_length x3;
                 simpl;
                 omega.
               }
             rewrite HEQx2.
             generalize (encode_parse_scale_refl _ _ EQ).
             intros Hscale. rewrite Hscale. simpl.
             assert(HEQ5: Byte.and bB[ x2 ++ x3 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"]](Byte.repr 7) = Byte.repr 5). {
               replace (x2 ++
        x3 ++
        [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"])
                 with
                   ((x2 ++x3) ++
        [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"]).
               setoid_rewrite and7.
               f_equal.
               1-2: repeat rewrite app_length; simpl.
               resolve_scale_length x2.
               resolve_reg_length x3.
               all: try omega.
               rewrite app_assoc.
               auto.
             }
             rewrite HEQ5.
             unfold addrmode_parse_reg.
             do 5 (try (rewrite byte_eq_false)).
             rewrite byte_eq_true; auto.
             simpl.
             unfold addrmode_SIB_parse_base.
             rewrite byte_eq_true; auto.
             rewrite byte_eq_true; auto.
             simpl.
             destruct p.
             
             destruct i1; inversion EQ1.
             monadInv EQ1.
             rewrite HRelocOfs in EQ3. inversion EQ3.
             subst x5.
             unfold get_instr_reloc_addend' in EQ1.
             unfold find_ofs_in_rtbl.
             unfold get_reloc_addend in EQ1.
             destruct (ZTree.get (iofs+sofs) rtbl_ofs_map); inversion EQ1.
             assert (Hvalid: valid_int32 (Ptrofs.unsigned i2)). {
              unfold valid_int32.
              generalize (Ptrofs.unsigned_range i2).
              unfold Ptrofs.modulus.
              unfold Ptrofs.wordsize.
              unfold Wordsize_Ptrofs.wordsize.
              destruct Archi.ptr64 eqn:EQA; inversion EQA.
              unfold two_power_nat. simpl.
              unfold two_power_pos. simpl.
              omega.
             }
             generalize (encode_decode_int32_same_prefix _ l Hvalid).
             intros Hint.
             rewrite Hint.
             simpl.
             rewrite byte_eq_true; auto.
             rewrite byte_eq_true; auto.
             simpl. repeat f_equal.
             generalize (encode_int32_4_exists (Ptrofs.unsigned i2) l (encode_int32 (Ptrofs.unsigned i2) ++ l) eq_refl).
             intros (b1 & b2 & b3 & b4 & HEncInt).
             rewrite HEncInt.
             simpl.

             repeat f_equal.
             +++++
               unfold addrmode_SIB_parse_index.
             destruct Byte.eq_dec eqn:EQx3.
             resolve_rsp x3.
             auto.
             +++++ rewrite Ptrofs.repr_unsigned. auto.
             +++++ intros HNot; inversion HNot.
             +++++ intros HNot; inversion HNot.
             +++++ intros HNot; inversion HNot.
             +++++ intros HNot; inversion HNot.
             +++++ intros HNot; inversion HNot.
             +++++ intros HNot; inversion HNot.
             +++++ intros HNot; inversion HNot.
             +++++ intros HNot; inversion HNot.
             +++++ intros HNot; inversion HNot.
             
    ++
      destruct p.
      destruct i0; inversion EQ1.
      monadInv EQ1.
      destruct base eqn:EQB.

      +++
        monadInv EQ.
        destruct(ireg_eq i0 RSP).
        ++++
          unfold decode_addrmode.
          inversion EQ4.
          unfold encode_int_big.
          simpl.
          assert(HTurncate:
                   (Byte.repr
                      (bits_to_Z
                         (char_to_bool "1"
                                       :: char_to_bool "0"
                                       :: x0 ++
                                       char_to_bool "1"
                                       :: char_to_bool "0"
                                       :: char_to_bool "0"
                                       :: char_to_bool "0"
                                       :: char_to_bool "0"
                                       :: char_to_bool "1"
                                       :: char_to_bool "0"
                                       ::
                                       char_to_bool "0" :: x3) /
                         256)) = bB[b["10"]++x0++b["100"]]). {
            replace (char_to_bool "1"
                                       :: char_to_bool "0"
                                       :: x0 ++
                                       char_to_bool "1"
                                       :: char_to_bool "0"
                                       :: char_to_bool "0"
                                       :: char_to_bool "0"
                                       :: char_to_bool "0"
                                       :: char_to_bool "1"
                                       :: char_to_bool "0"
                                       ::
                                       char_to_bool "0" :: x3)
              with
                ((char_to_bool "1"
                                       :: char_to_bool "0"
                                       :: x0 ++
                                       char_to_bool "1"
                                       :: char_to_bool "0"
                                       :: char_to_bool "0"
                                       ::[])++ (char_to_bool "0"
                                       :: char_to_bool "0"
                                       :: char_to_bool "1"
                                       :: char_to_bool "0"
                                       ::
                                       char_to_bool "0" :: x3)).
            replace 256 with (2^8).
            rewrite <- Z.shiftr_div_pow2.
            rewrite (Z_shru_bits 8).
            auto.
            simpl.
            resolve_reg_length x3. omega. omega.
            simpl.
            unfold Z.pow_pos. simpl. auto.
            repeat rewrite app_comm_cons.
            rewrite <- app_assoc.
            auto.
          }
          rewrite HTurncate.
          
          assert(HEQx1:(Byte.shru
                          (Byte.and bB[ b[ "10"] ++ x0 ++ b[ "100"]] (Byte.repr 56))
                          (Byte.repr 3)) = bB[x0]). {
            rewrite <- Byte.and_shru.
            rewrite shru563.
            replace ( b[ "10"] ++ x0 ++ b[ "100"])
              with
                ( (b[ "10"] ++ x0) ++ b[ "100"]).
            rewrite (shru_bits 3 _ _).
            setoid_rewrite (and7 (char_to_bool "1" :: [char_to_bool "0"]) x0).
            all:auto.

                 1,3: repeat rewrite app_length; simpl.
                 1,2,3:rewrite (encode_reg_length rd x0); try omega.
                 1-8: auto.
               }
               rewrite HEQx1.
               generalize (encode_decode_ireg_refl _ _ EQ2).
               intros Hrd.
               destruct Hrd.
               destruct H.
               rewrite H. rewrite H12. simpl.
               assert(HEQ2: (Byte.shru
                               bB[ char_to_bool "1"
                                                :: char_to_bool "0"
                                                :: x0 ++
                                                [char_to_bool "1"; char_to_bool "0";
                                                 char_to_bool "0"]] (Byte.repr 6))=Byte.repr 2). {
                 replace (char_to_bool "1"
        :: char_to_bool "0"
           :: x0 ++
              [char_to_bool "1"; char_to_bool "0";
               char_to_bool "0"])
                   with ((char_to_bool "1"
        :: char_to_bool "0"::[]) ++ (x0 ++
              [char_to_bool "1"; char_to_bool "0";
               char_to_bool "0"])).
                 rewrite (shru_bits 6).
                 f_equal.
                 1-2: repeat rewrite app_length; simpl;
                   resolve_reg_length x0; simpl; omega.
                 simpl. auto.
               }
               rewrite HEQ2.
               rewrite byte_eq_false.
               rewrite byte_eq_false.
               rewrite byte_eq_true; auto.
               assert(HEQ4: (Byte.and
                               bB[ char_to_bool "1"
                                                :: char_to_bool "0"
                                                :: x0 ++
                                                [char_to_bool "1"; char_to_bool "0";
                                                 char_to_bool "0"]] (Byte.repr 7)) = Byte.repr 4). {
                 replace (char_to_bool "1":: char_to_bool "0":: x0 ++[char_to_bool "1"; char_to_bool "0";char_to_bool "0"])
                         with ((char_to_bool "1":: char_to_bool "0":: x0) ++[char_to_bool "1"; char_to_bool "0";char_to_bool "0"]).
               rewrite and7.
               f_equal.
                all: repeat rewrite app_length;
                  try resolve_reg_length x1; simpl.
                resolve_reg_length x0.
                1-2: omega.
                simpl. auto.
               }
               rewrite HEQ4.
               unfold addrmode_parse_reg.
               do 4 (try(rewrite byte_eq_false)).
               rewrite byte_eq_true;auto.
               simpl.
               rewrite byte_eq_true.
               assert(Hmod:  bB[ char_to_bool "1"
                                              :: char_to_bool "0"
                                              :: x0 ++
                                              char_to_bool "1"
                                              :: char_to_bool "0"
                                              :: char_to_bool "0"
                                              :: char_to_bool "0"
                                              :: char_to_bool "0"
                                              :: char_to_bool "1"
                                              :: char_to_bool "0" :: char_to_bool "0" :: x3] = bB[b["00100"]++x3]). {
                 replace (char_to_bool "1"
                                              :: char_to_bool "0"
                                              :: x0 ++
                                              char_to_bool "1"
                                              :: char_to_bool "0"
                                              :: char_to_bool "0"
                                              :: char_to_bool "0"
                                              :: char_to_bool "0"
                                              :: char_to_bool "1"
                                              :: char_to_bool "0" :: char_to_bool "0" :: x3)
                   with ((char_to_bool "1"
                                              :: char_to_bool "0"
                                              :: x0 ++
                                              char_to_bool "1"
                                              :: char_to_bool "0"
                                              :: char_to_bool "0"::[])++(char_to_bool "0":: char_to_bool "0":: char_to_bool "1":: char_to_bool "0" :: char_to_bool "0" :: x3)).
                 apply BbTruncate.
                 simpl. resolve_reg_length x3.
                 omega.
                 repeat rewrite app_comm_cons.
                 rewrite <- app_assoc.
                 auto.
               }
               rewrite Hmod.
               unfold addrmode_parse_SIB.
               assert(HEQ4_2:(Byte.shru (Byte.and bB[ b[ "00100"] ++ x3] (Byte.repr 56)) (Byte.repr 3)) = Byte.repr 4). {
                 rewrite <- Byte.and_shru.
                 rewrite shru563.
                 rewrite (shru_bits 3 _ _).
                 setoid_rewrite (and7 b["00"] b["100"]).
                 all:auto.
                 rewrite app_length; simpl.
                 all: rewrite e in EQ.
                 all: rewrite (encode_reg_length RSP x3); try omega; auto.
               }
               rewrite HEQ4_2.
               unfold addrmode_parse_reg.
               do 4 (try(rewrite byte_eq_false)).
               rewrite byte_eq_true; auto.
               simpl.
               assert(HEQ0: (Byte.shru
                               bB[ char_to_bool "0"
                                                :: char_to_bool "0"
                                                :: char_to_bool "1" :: char_to_bool "0" :: char_to_bool "0" :: x3](Byte.repr 6)) = Byte.repr 0). {
                 replace ( char_to_bool "0"
        :: char_to_bool "0"
           :: char_to_bool "1"
           :: char_to_bool "0" :: char_to_bool "0" :: x3)
                         with ( (char_to_bool "0"
        :: char_to_bool "0"::[])++ char_to_bool "1"
                              :: char_to_bool "0" :: char_to_bool "0" :: x3).
                 rewrite (shru_bits 6).
                 f_equal.
                 1-2: simpl; resolve_reg_length x3; omega.
                 simpl. auto.
               }
               rewrite HEQ0.
               unfold addrmode_SIB_parse_scale.
               rewrite byte_eq_true; auto.
               assert(HEQx2: (Byte.and
                                bB[ char_to_bool "0"
                                                 :: char_to_bool "0"
                                                 :: char_to_bool "1" :: char_to_bool "0" :: char_to_bool "0" :: x3](Byte.repr 7)) = bB[x3]). {
                 replace (char_to_bool "0"
        :: char_to_bool "0"
           :: char_to_bool "1"
           :: char_to_bool "0" :: char_to_bool "0" :: x3) with
                    ((char_to_bool "0"
        :: char_to_bool "0"
           :: char_to_bool "1"
              :: char_to_bool "0" :: char_to_bool "0" :: []) ++ x3).
                 rewrite and7.
                 auto. simpl.
                 1-2: resolve_reg_length x3; omega.
                 simpl; auto.
               }
               rewrite HEQx2.
               simpl.
               fold (addrmode_parse_reg bB[x3]).
               generalize (encode_decode_ireg_refl _ _ EQ).
               intros HEQRSP.
               destruct HEQRSP. destruct H13.
               rewrite H13. rewrite H14. simpl.
               unfold addrmode_SIB_parse_base.
               rewrite e in EQ.
               unfold encode_ireg in EQ.
               inversion EQ.
               rewrite byte_eq_false.
               do 2 (try (rewrite byte_eq_false)).
               rewrite byte_eq_true; auto.
               simpl.
               rewrite HRelocOfs in EQ0.
               inversion EQ0. subst x1.
               unfold get_instr_reloc_addend' in EQ1.
               unfold find_ofs_in_rtbl.
               unfold get_reloc_addend in EQ1.
               destruct (ZTree.get (iofs+sofs) rtbl_ofs_map); inversion EQ1.
               assert (Hvalid: valid_int32 (Ptrofs.unsigned i1)). {
                unfold valid_int32.
                generalize (Ptrofs.unsigned_range i1).
                unfold Ptrofs.modulus.
                unfold Ptrofs.wordsize.
                unfold Wordsize_Ptrofs.wordsize.
                destruct Archi.ptr64 eqn:EQA; inversion EQA.
                unfold two_power_nat. simpl.
                unfold two_power_pos. simpl.
                omega.
               }
               rewrite H16.
               generalize (encode_decode_int32_same_prefix _ l Hvalid).
               intros Hint.
               rewrite Hint.
               simpl.

               
               rewrite byte_eq_false. simpl.
               generalize (encode_int32_4_exists (Ptrofs.unsigned i1) l (encode_int32 (Ptrofs.unsigned i1) ++ l) eq_refl).
               intros (b1 & b2 & b3 & b4 & HEncInt).
               rewrite HEncInt.
               simpl.
               repeat f_equal.

               
               all: try(intros HNot; inversion HNot).
               rewrite Ptrofs.repr_unsigned. auto.
        ++++
          inversion EQ4.
            unfold decode_addrmode.
            simpl.
            assert(HEQx1:(Byte.shru
                            (Byte.and bB[ char_to_bool "1" :: char_to_bool "0" :: x0 ++ x3] (Byte.repr 56))(Byte.repr 3)) = bB[x0]). {
              rewrite <- Byte.and_shru.
              rewrite shru563.
              replace (char_to_bool "1" :: char_to_bool "0" :: x0 ++ x3)
                with
                  ((char_to_bool "1" :: char_to_bool "0" :: x0) ++ x3).
              rewrite (shru_bits 3 _ _).
              setoid_rewrite (and7 (char_to_bool "1" :: [char_to_bool "0"]) x0).
              auto.

              1,3,4: repeat rewrite app_length; simpl.
              1,2,4:rewrite (encode_reg_length rd x0); try omega.
              1-8: auto.
              all: rewrite (encode_reg_length i0 x3); try omega; auto.
            }
            
            rewrite HEQx1.
           
            resolve_enc_dec_ireg_refl x0.
            rewrite H12; rewrite H13. simpl.
            assert(HEQ2: (Byte.shru bB[ char_to_bool "1" :: char_to_bool "0" :: x0 ++ x3] (Byte.repr 6)) = Byte.repr 2). {
              replace ( char_to_bool "1" :: char_to_bool "0" :: x0 ++ x3) with ( (char_to_bool "1" :: char_to_bool "0" ::[])++( x0 ++ x3)).
              rewrite (shru_bits 6).
              f_equal.
              simpl.
              1-2: repeat rewrite app_length;
                resolve_reg_length x0;
                resolve_reg_length x3;
                omega.
              auto.
            }
            rewrite HEQ2.
            rewrite byte_eq_false.
            rewrite byte_eq_false.
            rewrite byte_eq_true; auto.
            assert(HEQx2: (Byte.and bB[ char_to_bool "1" :: char_to_bool "0" :: x0 ++ x3] (Byte.repr 7)) = bB[x3]). {
              replace (char_to_bool "1" :: char_to_bool "0" :: x0 ++ x3) with ((char_to_bool "1" :: char_to_bool "0" :: x0) ++ x3).
              rewrite and7.
              auto.
              simpl.
              1-2: repeat rewrite app_length;
                resolve_reg_length x3.
              resolve_reg_length x0.
              1-2:omega.
              auto.
            }
            rewrite HEQx2.
            resolve_enc_dec_ireg_refl x3.
            rewrite H14. rewrite H15.
            simpl.
            assert(HNE4: bB[x3] <> Byte.repr 4). {
              intros HNot.
              destruct i0;
              simpl in EQ;
              monadInv EQ;
              inversion HNot.
              auto.
            }
            rewrite byte_eq_false.

            assert (Hvalid: valid_int32 (Ptrofs.unsigned i1)). {
              unfold valid_int32.
               generalize (Ptrofs.unsigned_range i1).
               unfold Ptrofs.modulus.
               unfold Ptrofs.wordsize.
               unfold Wordsize_Ptrofs.wordsize.
               destruct Archi.ptr64 eqn:EQA; inversion EQA.
               unfold two_power_nat. simpl.
               unfold two_power_pos. simpl.
               omega.
            }
            generalize (encode_decode_int32_same_prefix _ l Hvalid).
            intros Hint.
            rewrite Hint.
            simpl.
            
           
            resolve_reloc iofs sofs.
            generalize (encode_int32_4_exists (Ptrofs.unsigned i1) l (encode_int32 (Ptrofs.unsigned i1) ++ l) eq_refl).
            intros (b1 & b2 & b3 & b4 & HEncInt).
            rewrite HEncInt.
            simpl.
            repeat f_equal.
            rewrite Ptrofs.repr_unsigned. auto. auto.
            intros HNot. inversion HNot.
            intros HNot. inversion HNot.
      +++ unfold decode_addrmode.
          monadInv EQ.
          simpl.
          assert(HEQx1: (Byte.shru
                           (Byte.and
                              bB[ char_to_bool "0"
                                               :: char_to_bool "0"
                                               :: x0 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"]](Byte.repr 56)) (Byte.repr 3)) = bB[x0]). {
            rewrite <- Byte.and_shru.
            rewrite shru563.
            replace (char_to_bool "0"
           :: char_to_bool "0"
              :: x0 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"])
              with
                ((char_to_bool "0"
           :: char_to_bool "0"
              :: x0) ++ ([char_to_bool "1"; char_to_bool "0"; char_to_bool "1"])).
            rewrite (shru_bits 3 _ _).
            setoid_rewrite (and7 (char_to_bool "0" :: [char_to_bool "0"]) x0).
            all: auto.

            1,3,4: repeat rewrite app_length; simpl.
            all:rewrite (encode_reg_length rd x0); try omega.
            1-8: auto.
          }
          rewrite HEQx1.
          resolve_enc_dec_ireg_refl x0.
          rewrite H11. rewrite H12.
          assert(HEQ0:  (Byte.shru
                           bB[ char_to_bool "0"
                                            :: char_to_bool "0"
                                            :: x0 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"]](Byte.repr 6)) = Byte.repr 0). {
            replace (char_to_bool "0"
        :: char_to_bool "0"
           :: x0 ++
              [char_to_bool "1"; char_to_bool "0";
               char_to_bool "1"])
              with ((char_to_bool "0":: char_to_bool "0"::[])++( x0 ++
                                                                  [char_to_bool "1"; char_to_bool "0";char_to_bool "1"])).
            rewrite (shru_bits 6).
            f_equal.
            simpl.
            1-2: repeat rewrite app_length;
            resolve_reg_length x0; simpl;
              omega.
            simpl. auto.
          }
          rewrite HEQ0. simpl.
          rewrite byte_eq_true; auto.
          assert(HEQ5: (Byte.and
                          bB[ char_to_bool "0"
                                           :: char_to_bool "0"
                                           :: x0 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"]](Byte.repr 7)) = Byte.repr 5). {
            replace (char_to_bool "0"
                                           :: char_to_bool "0"
                                           :: x0 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"])
                    with ((char_to_bool "0"
                                           :: char_to_bool "0"
                                           :: x0) ++ ([char_to_bool "1"; char_to_bool "0"; char_to_bool "1"])).
            rewrite and7.
            f_equal.
            1-2: repeat rewrite app_length;
              simpl;
              try resolve_reg_length x0;
              omega.
            auto.
          }
          rewrite HEQ5.
          unfold addrmode_parse_reg.
          do 5(try(rewrite byte_eq_false)).
          rewrite byte_eq_true; auto.
          simpl.
          rewrite byte_eq_false.
          rewrite byte_eq_true; auto.
          resolve_reloc iofs sofs.
          assert (Hvalid: valid_int32 (Ptrofs.unsigned i1)). {
            unfold valid_int32.
               generalize (Ptrofs.unsigned_range i1).
               unfold Ptrofs.modulus.
               unfold Ptrofs.wordsize.
               unfold Wordsize_Ptrofs.wordsize.
               destruct Archi.ptr64 eqn:EQA; inversion EQA.
               unfold two_power_nat. simpl.
               unfold two_power_pos. simpl.
               omega.
          }
          generalize (encode_decode_int32_same_prefix _ l Hvalid).
          intros Hint.
          rewrite Hint.
          simpl.
          generalize (encode_int32_4_exists (Ptrofs.unsigned i1) l (encode_int32 (Ptrofs.unsigned i1) ++ l) eq_refl).
          intros (b1 & b2 & b3 & b4 & HEncInt).
          rewrite HEncInt.
          simpl.

          repeat f_equal.
          auto.
          rewrite Ptrofs.repr_unsigned. auto.
          1-6:
            intros HNot; inversion HNot.
          (* valid_int32 *)
Admitted.


Lemma encode_decode_addr_size_relf: forall a rd abytes,
    encode_addrmode_aux a rd = OK abytes
    ->forall l, decode_addrmode_size (abytes++l) = OK (addrmode_reloc_offset a).
Proof.
  intros a rd abytes HEncode l.
  unfold decode_addrmode_size.
  unfold encode_addrmode_aux in HEncode.
  destruct a.
  monadInv HEncode.
  destruct ofs eqn:EQOFS.
  destruct p.
  destruct base eqn:EQBase.
  + destruct ireg_eq.
    inversion EQ0.
    monadInv EQ0.
    simpl.
    assert(HTruncate: Byte.repr
                        (bits_to_Z
                           (b["10"]++x ++ b["100"] ++x0 ++ x1 ++ x2) /256) = bB[b["10"]++x ++ b["100"]]). {
      replace (b[ "10"] ++ x ++ b[ "100"] ++ x0 ++ x1 ++ x2)
        with ((b[ "10"] ++ x ++ b[ "100"]) ++ (x0 ++ x1 ++ x2)).
      replace 256 with (2^8).
      rewrite <- Z.shiftr_div_pow2.
      rewrite (Z_shru_bits 8).

      auto.
      repeat rewrite app_length.
      resolve_reg_length x1.
      resolve_reg_length x2.
      resolve_scale_length x0.
      1-2:omega.
      simpl.
      unfold Z.pow_pos. simpl. auto.
      repeat rewrite <-app_assoc.
      auto.
    }
    simpl in HTruncate.
    rewrite HTruncate.
    assert(HEQ2: Byte.shru  bB[b["10"]++x ++ b["100"]] (Byte.repr 6) = Byte.repr 2). {
      rewrite (shru_bits 6).
      f_equal.
      1-2: repeat rewrite app_length;
      resolve_reg_length x; simpl; omega.
    }
    simpl in HEQ2.
    rewrite HEQ2.
    rewrite byte_eq_false.
    assert(HEQ4: Byte.and bB[b["10"]++x ++ b["100"]] (Byte.repr 7) = Byte.repr 4). {
      rewrite app_assoc.
      rewrite and7.
      f_equal.
      f_equal.
      1-2: repeat rewrite app_length;
        try resolve_reg_length x; simpl; omega.
    }
      
    simpl in HEQ4.
    rewrite HEQ4.
    rewrite byte_eq_true. auto.
    intros HNot. inversion HNot.
  + destruct ireg_eq; inversion EQ0.
    monadInv H10.
    simpl.
    assert(HTruncate: Byte.repr
                        (bits_to_Z
                           (b["00"]++x ++ b["100"] ++x0 ++ x1 ++ b["101"]) /
                           256) = bB[b["00"]++x ++ b["100"]]). {

       replace (b[ "00"] ++ x ++ b[ "100"] ++ x0 ++ x1 ++ b["101"])
        with ((b[ "00"] ++ x ++ b[ "100"]) ++ (x0 ++ x1 ++b["101"])).
      replace 256 with (2^8).
      rewrite <- Z.shiftr_div_pow2.
      rewrite (Z_shru_bits 8).

      auto.
      repeat rewrite app_length.
      resolve_reg_length x1.
      resolve_scale_length x0.
      simpl.
      1-2:omega.
      simpl.
      unfold Z.pow_pos. simpl. auto.
      repeat rewrite <-app_assoc.
      auto.
    }
    simpl in HTruncate. rewrite HTruncate.
    assert(HEQ0: Byte.shru  bB[b["00"]++x ++ b["100"]] (Byte.repr 6) = Byte.repr 0). {
            rewrite (shru_bits 6).
            f_equal.
            1-2: repeat rewrite app_length;
              resolve_reg_length x; simpl; omega.
    }
    simpl in HEQ0; rewrite HEQ0.
    rewrite byte_eq_false.
    assert(HEQ4:  Byte.and bB[b["00"]++x ++ b["100"]] (Byte.repr 7) = Byte.repr 4). {
            rewrite app_assoc.
      rewrite and7.
      f_equal.
      f_equal.
      1-2: repeat rewrite app_length;
        try resolve_reg_length x; simpl; omega.
    }
    simpl in HEQ4.
    rewrite HEQ4.
    rewrite byte_eq_true.
    auto.
    intros HNot. inversion HNot.
  + destruct base eqn:EQBase.
    monadInv EQ0.
    destruct ireg_eq eqn:EQI.
    (* (b[ "10"] ++ x ++ b[ "100"] ++ b[ "00"] ++ b[ "100"] ++ x0) *)
    inversion EQ2.
    simpl.
    assert(HTruncate: Byte.repr
                        (bits_to_Z
                           (b[ "10"] ++ x ++ b[ "100"] ++ b[ "00"] ++ b[ "100"] ++ x0) /256) = bB[b["10"]++x ++ b["100"]]). {
      replace (b[ "10"] ++ x ++ b[ "100"] ++b[ "00"] ++ b[ "100"] ++ x0)
        with ((b[ "10"] ++ x ++ b[ "100"]) ++ (b[ "00"] ++ b[ "100"] ++ x0)).
      replace 256 with (2^8).
      rewrite <- Z.shiftr_div_pow2.
      rewrite (Z_shru_bits 8).
      auto.
      repeat rewrite app_length.
      resolve_reg_length x0.
      simpl.
      1-2:omega.
      simpl.
      unfold Z.pow_pos. simpl. auto.
      repeat rewrite <-app_assoc.
      auto.
    }
    simpl in HTruncate. rewrite HTruncate.
    assert(HEQ2: Byte.shru  bB[b["10"]++x ++ b["100"]] (Byte.repr 6) = Byte.repr 2). {
      rewrite (shru_bits 6).
      f_equal.
      1-2: repeat rewrite app_length;
        resolve_reg_length x; simpl; omega.
    }
    simpl in HEQ2. rewrite HEQ2.
    rewrite byte_eq_false.
    assert(HEQ4:  Byte.and bB[b["10"]++x ++ b["100"]] (Byte.repr 7) = Byte.repr 4). {
      rewrite app_assoc.
      rewrite and7.
      f_equal.
      f_equal.
      1-2: repeat rewrite app_length;
        try resolve_reg_length x; simpl; omega.
    }
    simpl in HEQ4. rewrite HEQ4.
    rewrite byte_eq_true.
    rewrite e. auto.
    intros HNot. inversion HNot.
    inversion EQ2.
    simpl.
    assert(HEQ2: Byte.shru  bB[b["10"]++x ++ x0] (Byte.repr 6) = Byte.repr 2). {
      rewrite (shru_bits 6).
      f_equal.
      1-2: repeat rewrite app_length;
        resolve_reg_length x0;
        resolve_reg_length x;
        simpl; omega.
    }
    simpl in HEQ2.
    rewrite HEQ2.
    rewrite byte_eq_false.
    
    assert(HEQ4:  Byte.and bB[b["10"]++x ++ x0] (Byte.repr 7) <> Byte.repr 4). {
      rewrite app_assoc.
      rewrite and7.
      f_equal.
      f_equal.
      2,3: repeat rewrite app_length;
        try resolve_reg_length x; try resolve_reg_length x0; simpl; try omega.
      intros HNot.
      destruct i;
      simpl in EQ1;
      inversion EQ1;
      rewrite <- H11 in HNot;
      inversion HNot.
      congruence.
    }
    simpl in HEQ4.
    rewrite byte_eq_false.
    destruct i; simpl; auto.
    congruence.
    auto.
    intros HNot. inversion HNot.

    inversion EQ0.
    simpl.
    assert(HEQ0: Byte.shru  bB[b["00"]++x ++ b["101"]] (Byte.repr 6) = Byte.repr 0). {
      rewrite (shru_bits 6).
      f_equal.
      1-2: repeat rewrite app_length;
        resolve_reg_length x;
      simpl; omega.
    }
    simpl in HEQ0. rewrite HEQ0.
    rewrite byte_eq_false.
    assert(HEQ5:  Byte.and bB[b["00"]++x ++ b["101"]] (Byte.repr 7) = Byte.repr 5). {
            rewrite app_assoc.
      rewrite and7.
      f_equal.
      f_equal.
      1-2: repeat rewrite app_length;
        try resolve_reg_length x; simpl; omega.
    }
    simpl in HEQ5. rewrite HEQ5.
    rewrite byte_eq_false. auto.
    1-2:intros HNot; inversion HNot.
Qed.


Lemma encode_addr_neq_c0: forall a rd x l,
    encode_addrmode_aux a rd = OK x ->
    exists modrm, get_n (x++l) 0 = OK modrm /\ (Byte.and modrm HB["C0"]) <> HB["C0"].
Proof.
  intros a rd x l EQ.
  destruct a.
  destruct base.
  + destruct ofs.
    ++ unfold encode_addrmode_aux in EQ.
       simpl in EQ.
       monadInv EQ.
       destruct p in EQ1.
       destruct (ireg_eq i0 RSP) eqn:EQR; inversion EQ1.
       monadInv EQ1.
       simpl.
       exists (bB[ b[ "10"] ++ x0 ++ b[ "100"]]).
       replace 256 with (2^8).
       rewrite <- Z.shiftr_div_pow2.
      
       assert(length(x1 ++ x2 ++ x3) = 8%nat) as len. {
         repeat rewrite app_length.
         simpl.
         rewrite (encode_scale_length z).
         rewrite (encode_reg_length i0); auto.
         rewrite (encode_reg_length i); auto.
         auto.
       }
       generalize (Z_shru_bits 8 (b["10"] ++ x0 ++ b["100"]) (x1 ++ x2 ++ x3) len).
       intros H.
       repeat rewrite <- app_assoc in H.
       simpl in H.
       rewrite H.
       split.
       +++ simpl. auto.
       +++ 
         assert((length b["10"] <= 2)%nat) as len2 by (simpl;omega).
         assert((length (x0 ++ b[ "100"]) = 6)%nat) as len6. {
           rewrite app_length.
           simpl.
           rewrite (encode_reg_length rd); auto.
         }
         generalize (byte_and_C0 b["10"] (x0++b["100"]) len2 len6).
         intros H11.
         simpl in *.
         rewrite H11.
         unfold not. intros H12. inversion H12.
       +++ omega.
       +++ unfold Z.pow. unfold Z.pow_pos. simpl. auto.
    ++
      unfold encode_addrmode in EQ.
      unfold encode_addrmode_aux in EQ.
      destruct (ireg_eq i RSP) eqn:EQR.
      +++       
        simpl in EQ.
        monadInv EQ.
        exists(bB[ b["10"] ++ x0 ++ b["100"]]).
        split.
        ++++ simpl.
              replace 256 with (2^8).
              rewrite <- Z.shiftr_div_pow2.
              assert(length(b["00100"] ++ x1) = 8%nat) as len. {
                rewrite app_length.
                simpl.
                rewrite (encode_reg_length RSP);auto.
              }
              generalize (Z_shru_bits 8 (b["10"] ++ x0 ++ b["100"]) ( b["00100"] ++ x1) len).
              intros H.
              repeat rewrite <- app_assoc in H.
              simpl in H.
              setoid_rewrite H.
              auto.
              omega.
              simpl. unfold Z.pow_pos. simpl. auto.
        ++++ assert((length b["10"] <= 2)%nat) as len2 by (simpl;omega).
             assert((length (x0 ++ b[ "100"]) = 6)%nat) as len6. {
               rewrite app_length.
               simpl.
               rewrite (encode_reg_length rd);auto.
             }
             generalize (byte_and_C0 b["10"] (x0++b["100"]) len2 len6).
             intros H11.
             simpl in *.
             rewrite H11.
             unfold not. intros H12. inversion H12.
      +++ simpl in EQ.
          monadInv EQ.
          exists(bB[ b["10"] ++ x0 ++ x1]).
          split.
          ++++ simpl. auto.
          ++++ assert((length b["10"] <= 2)%nat) as len2 by (simpl;omega).
               assert((length (x0 ++ x1) = 6)%nat) as len6. {
                 rewrite app_length.
                 rewrite (encode_reg_length rd); auto.
                 rewrite (encode_reg_length i); auto.
               }
               generalize (byte_and_C0 b["10"] (x0++x1) len2 len6).
               intros H11.
               simpl in *.
               rewrite H11.
               unfold not. intros H12. inversion H12.
  + destruct ofs.
    ++ unfold encode_addrmode in EQ.
       monadInv EQ.
       unfold encode_addrmode_aux in EQ0.
       destruct p.
       destruct (ireg_eq i RSP) eqn:EQR; inversion EQ1.
       monadInv H10.
       exists (bB[b[ "00"] ++ x0 ++ b[ "100"]]).
       split.
       +++ monadInv EQ1.
           simpl.
           replace 256 with (2^8).
           rewrite <- Z.shiftr_div_pow2.
      
           assert(length(x1++x2 ++  [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"] ) = 8%nat) as len. {
             repeat rewrite app_length.
             simpl.
             rewrite (encode_scale_length z).
             rewrite (encode_reg_length i);auto. auto.
           }
           generalize (Z_shru_bits 8 (b["00"] ++ x0 ++ b["100"]) ( x1 ++ x2 ++  [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"]) len).
           intros H.
           repeat rewrite <- app_assoc in H.
           setoid_rewrite H.
           simpl. auto.
           omega.
           simpl.
           unfold Z.pow_pos. simpl.
           omega.
       +++
         assert ((length b["00"] <=2)%nat) as len by (simpl; auto).
         assert ((length  (x0++b["100"]) = 6)%nat) as len2. {
           rewrite app_length.
           simpl.
           rewrite (encode_reg_length rd).
           auto. auto.
         }
         generalize (byte_and_C0 b["00"] (x0++b["100"]) len len2).
         intros H.
         unfold not.
         intros H11.
         rewrite H in H11.
         inversion H11.
    ++ unfold encode_addrmode in EQ.
       unfold encode_addrmode_aux in EQ.
       monadInv EQ.       
       exists (bB[ b[ "00"] ++ x0 ++ b[ "101"]]).
       simpl.
       split.
       +++ auto.
       +++
         assert((length b["00"] <=2)%nat) as len by (simpl; auto).
         assert ((length  (x0++b["101"]) = 6)%nat) as len2. {
           rewrite app_length.
           simpl.
           rewrite (encode_reg_length rd).
           auto. auto.
         }
         generalize(byte_and_C0 b["00"] (x0++b["101"]) len len2).
         intros H.
         unfold not.
         intros H10.
         simpl in H.
         rewrite H in H10.
         inversion H10.
Qed.



Ltac unfold_and_simpl_encoder:=
  match goal with
  |[ H: encode_instr _ _ _ _ = OK _|- _]=>
   unfold encode_instr in H; cbn [negb ready_for_proof negb] in H;
   unfold encode_instr' in H
  |_ => idtac
  end.

Lemma encode_decode_instr_refl: forall ofs i s l,
    encode_instr rtbl_ofs_map false ofs i = OK s
    -> exists i', fmc_instr_decode ofs (s++l) = OK(i',l) /\
                  instr_eq i i'.

  intros ofs i s l HEncode.
  destruct i; inversion HEncode.
  all: repeat unfold_and_simpl_encoder.
  + (* Pmov_rr rd r1 *)
    unfold encode_instr in H10.
    cbn [negb ready_for_proof negb] in H10.
    exists(Pmov_rr rd r1).
    split; try (unfold instr_eq; auto).
    destruct negb;inversion H10.
    monadInv H10.
    unfold fmc_instr_decode.
    simpl.
    branch_byte_eq'.
    unfold decode_8b.
    unfold get_n.
    simpl.
    cut((Byte.and bB[ char_to_bool "1" :: char_to_bool "1" :: x ++ x0] (Byte.repr 192)) = Byte.repr 192).
    intros HC0.
    rewrite HC0.
    rewrite byte_eq_true;auto.
    unfold decode_mov_rr. simpl.
    setoid_rewrite (decode_encode_rr_operand_refl b["11"] rd r1 x x0);auto.
    setoid_rewrite (byte_and_C0 b["11"] (x++x0) ).
    auto. auto.
    rewrite app_length. rewrite (encode_reg_length rd),(encode_reg_length r1);auto.
  + (* Pmovl_ri rd n *)
    exists (Pmovl_ri rd n).
    split; try(unfold instr_eq;auto).
    destruct negb; inversion H10.
    monadInv H10.
    simpl.
    branch_byte_eq'.
    assert (Byte.and bB[ b[ "10111"] ++ x] HB["F0"] =  HB["B0"]) as opcode. {
      
      setoid_rewrite (andf0 b["1011"] (b["1"]++x)).
      simpl. auto.
      repeat rewrite app_length. simpl.
      rewrite (encode_reg_length rd);auto.
      rewrite app_length. simpl.
      rewrite (encode_reg_length rd);auto.
    }
    simpl in opcode.
    rewrite opcode.
    rewrite byte_eq_true.
    unfold decode_movl_ri.
    simpl.
    setoid_rewrite(and7 b["10111"] x).
    setoid_rewrite (encode_parse_reg_refl rd);auto.
    simpl.
    repeat f_equal.
    
    rewrite (encode_decode_int32_same_prefix).
    simpl.
    generalize (encode_int32_4_exists _ l (encode_int32 (Int.unsigned n) ++ l) eq_refl).
    intros (b1 & b2 & b3 & b4 & HEncInt).
    rewrite HEncInt.
    simpl.
    repeat f_equal.
    apply Int.repr_unsigned.
    generalize (Int.unsigned_range n). intros H.
    unfold valid_int32.
    unfold Int.modulus in H.
    unfold Int.wordsize in H. unfold Wordsize_32.wordsize in H.
    unfold two_power_nat in H. simpl in H.
    unfold two_power_pos;simpl.
    omega.
    repeat rewrite app_length.
    simpl.
    rewrite (encode_reg_length rd).
    auto. auto.
    rewrite (encode_reg_length rd);auto.
    
  + (* Pmov_rs rd id *)
    exists (Pmovl_rm rd (Addrmode None None (inr (id, Ptrofs.zero)))).
    split; try (unfold instr_eq; auto).
    destruct negb; inversion H10.
    monadInv H10.
    unfold fmc_instr_decode. simpl.    
    branch_byte_eq'. unfold decode_8b.
    unfold encode_instr in HEncode.    
    unfold encode_addrmode in EQ.
    assert (HmodrmExists: exists modrm, get_n (x ++ l) 0 = OK modrm). {
      monadInv EQ.
      simpl in EQ0.
      inversion EQ0.
      monadInv H10.
      simpl.
      eauto.
    }
    destruct HmodrmExists.
    rewrite H. simpl.
    assert (HModrmPrefix : (Byte.and x0 HB[ "C0"]) <> HB["C0"] ). {
      monadInv EQ.
      simpl in EQ0.
      inversion EQ0.
      monadInv H12.
      simpl in H.
      inversion H.
      replace (char_to_bool "0"
            :: char_to_bool "0"
               :: x ++
                  [char_to_bool "1"; char_to_bool "0";
                   char_to_bool "1"])
        with ((char_to_bool "0"
            :: char_to_bool "0"
               ::[])++ (x ++
                  [char_to_bool "1"; char_to_bool "0";
                  char_to_bool "1"])).
      rewrite byte_and_C0.
      simpl. intros HNot. inversion HNot.
      simpl. 2:simpl.
      omega.
      rewrite app_length.
      simpl.
      resolve_reg_length x. omega.
      auto.
    }
    rewrite byte_eq_false; auto.
    unfold decode_movl_rm.
    cbn [negb ready_for_proof negb] in HEncode.
    unfold encode_instr' in HEncode.
    monadInv HEncode.
    assert (exists irofs, instr_reloc_offset (Pmov_rs rd 1%positive)= OK irofs) as HInstr_reloc . {
      unfold instr_reloc_offset.
      eauto.
    }
    destruct HInstr_reloc as [irofs HInstr_reloc].
    assert(HOfs: ofs + 1 + 1 = irofs + ofs). {
        unfold instr_reloc_offset in HInstr_reloc.
        replace (ofs+1+1)with (1 + 1 + ofs) by omega.
        monadInv HInstr_reloc.        
        omega.
    }
    monadInv EQ.
    destruct id; inversion EQ.
    monadInv EQ.
    generalize (encode_decode_addrmode_relf _ _ _ (ofs + 1 + 1) _ _ ofs HInstr_reloc EQ0 HOfs).
    intros HAddrmode.
    unfold encode_addrmode in EQ0.
    unfold get_instr_reloc_addend' in EQ.
    unfold get_reloc_addend in EQ.
    simpl in EQ2. inversion EQ2.
    subst x.
    destruct (ZTree.get (2+ofs)) eqn:HReloc;inversion EQ.
    monadInv H11.
    (* rewrite <- H12 in H11. *)
    (* monadInv H12. *)
    (* monadInv EQ0. *)
    (* destruct (Ptrofs.eq_dec Ptrofs.zero Ptrofs.zero); inversion EQ0. *)
    monadInv EQ0.
    generalize(encode_decode_addr_size_relf _ _ _ EQ4 (encode_int32 x2 ++l)).
    intros HAddrsize.
    rewrite <- app_assoc.
    rewrite HAddrsize.
    simpl.
    monadInv EQ0.
    simpl in EQ5. inversion EQ5.
    subst x3.
    rewrite app_assoc.
    rewrite H11.
    generalize (HAddrmode l).
    intros HAddrmode1.
    rewrite HAddrmode1.
    simpl. auto.
  + (* Pmovl_rm rd a *)
    exists (Pmovl_rm rd a).
    split; try (unfold instr_eq; auto).
    unfold fmc_instr_decode.
    destruct negb; inversion H10.
    clear H11.
    monadInv H10. simpl.
    branch_byte_eq'.
    unfold decode_8b.
    unfold encode_instr in HEncode.    
    unfold encode_addrmode in EQ.
    assert (HmodrmExists: exists modrm, get_n (x ++ l) 0 = OK modrm). {
      destruct a.
      monadInv EQ.
      simpl in EQ0.
      inversion EQ0.
      monadInv H10.
      destruct ofs0. destruct p.
      destruct base. destruct ireg_eq. inversion EQ2.
      monadInv EQ2. simpl. eauto.
      destruct ireg_eq. inversion EQ2.
      monadInv EQ2. simpl; eauto.
      destruct base.
      monadInv EQ2.
      destruct ireg_eq.
      inversion EQ4.
      simpl.
      eauto.
      inversion EQ4.
      simpl.
      eauto.
      inversion EQ2.
      simpl.
      eauto.
    }
    destruct HmodrmExists.
    rewrite H. simpl.
    assert (HModrmPrefix : (Byte.and x0 HB[ "C0"]) <> HB["C0"] ). {
      destruct a.
      monadInv EQ.
      simpl in EQ0.
      inversion EQ0.
      monadInv H11.
      destruct ofs0. destruct p.
      destruct base. destruct ireg_eq. inversion EQ2.
      monadInv EQ2. simpl in H.
      inversion H.
      assert(HTruncate: bits_to_Z ((b["10"]++x++b["100"])++(x3++x4++x5))/256 = bits_to_Z (b["10"]++x++b["100"])). {
        replace 256 with (2^8).
        rewrite <- Z.shiftr_div_pow2.
        rewrite (Z_shru_bits 8).
        auto.
        repeat rewrite app_length.
        resolve_scale_length x3.
        resolve_reg_length x4.
        resolve_reg_length x5.
        simpl.
        1-2:omega.
        simpl.
        unfold Z.pow_pos. simpl. auto.
      }
      repeat rewrite <- app_assoc in HTruncate.
      simpl in HTruncate.
      rewrite HTruncate.
      replace (char_to_bool "1"
        :: char_to_bool "0"
           :: x ++
              [char_to_bool "1"; char_to_bool "0";
               char_to_bool "0"])
              with ((char_to_bool "1"
        :: char_to_bool "0"::[]) ++ x ++
              [char_to_bool "1"; char_to_bool "0";
               char_to_bool "0"]).
      rewrite byte_and_C0.
      intros HNot. inversion HNot.
      simpl. omega.
      rewrite app_length.
      resolve_reg_length x.
      simpl. omega.
      auto.
      
      destruct ireg_eq. inversion EQ2.
      monadInv EQ2.
      simpl in H.
      inversion H.
      assert(HTruncate: bits_to_Z ((b["00"]++x++b["100"])++(x3++x4++b["101"]))/256 = bits_to_Z (b["00"]++x++b["100"])). {
        replace 256 with (2^8).
        rewrite <- Z.shiftr_div_pow2.
        rewrite (Z_shru_bits 8).
        auto.
        repeat rewrite app_length.
        resolve_scale_length x3.
        resolve_reg_length x4.
        simpl.
        1-2:omega.
        simpl.
        unfold Z.pow_pos. simpl. auto.
      }
      repeat rewrite <-app_assoc in HTruncate.
      simpl in HTruncate.
      rewrite HTruncate.
      replace (char_to_bool "0":: char_to_bool "0":: x ++
                            [char_to_bool "1"; char_to_bool "0";
                             char_to_bool "0"])
        with ((char_to_bool "0":: char_to_bool "0"::[]) ++ x ++
                                                    [char_to_bool "1"; char_to_bool "0";char_to_bool "0"]).
      rewrite byte_and_C0.
      intros HNot. inversion HNot.
      simpl. omega.
      rewrite app_length.
      resolve_reg_length x.
      simpl. omega.
      auto.

      
      destruct base.
      monadInv EQ2.
      monadInv EQ0.
      destruct ireg_eq.
      simpl in EQ4.
      inversion EQ4.
      subst x1.
      unfold encode_int_big in H.
      simpl in H.
      inversion H.
      assert(HTruncate: bits_to_Z ((b["10"]++x++b["100"])++(b["00100"]++x3))/256 = bits_to_Z (b["10"]++x++b["100"])). {
        replace 256 with (2^8).
        rewrite <- Z.shiftr_div_pow2.
        rewrite (Z_shru_bits 8).
        auto.
        repeat rewrite app_length.
        resolve_reg_length x3.
        simpl.
        1-2:omega.
        simpl.
        unfold Z.pow_pos. simpl. auto.
      }
      repeat rewrite <-app_assoc in HTruncate.
      simpl in HTruncate.
      rewrite HTruncate.
      replace (char_to_bool "1":: char_to_bool "0":: x ++
                            [char_to_bool "1"; char_to_bool "0";
                             char_to_bool "0"])
        with ((char_to_bool "1":: char_to_bool "0"::[]) ++ x ++
                                                       [char_to_bool "1"; char_to_bool "0";char_to_bool "0"]).
      rewrite byte_and_C0.
      intros HNot. inversion HNot.
      simpl. omega.
      rewrite app_length.
      resolve_reg_length x.
      simpl. omega.
      auto.

      inversion EQ4.
      subst x1.
      simpl in H.
      inversion H.
      replace ( char_to_bool "1" :: char_to_bool "0" :: x ++ x3)
        with((char_to_bool "1" :: char_to_bool "0" ::[])++(x ++ x3)).
      rewrite byte_and_C0.
      intros HNot. inversion HNot.
      simpl. omega.
      rewrite app_length.
      resolve_reg_length x.
      resolve_reg_length x3.
      simpl. omega.
      auto.
      
      inversion EQ2.
      monadInv EQ0.
      simpl in H.
      inversion H.
      replace (char_to_bool "0":: char_to_bool "0":: x ++
                            [char_to_bool "1"; char_to_bool "0";
                             char_to_bool "1"])
        with ((char_to_bool "0":: char_to_bool "0"::[]) ++ x ++
                                                       [char_to_bool "1"; char_to_bool "0";char_to_bool "1"]).
      rewrite byte_and_C0.
      intros HNot. inversion HNot.
      simpl. omega.
      rewrite app_length.
      resolve_reg_length x.
      simpl. omega.
      auto.
    }
    rewrite byte_eq_false; auto.
    unfold decode_movl_rm.
    destruct a eqn:EQA.
    monadInv EQ.
    destruct const eqn:EQConst.
    ++
      unfold instr_reloc_offset in EQ.
      unfold addrmode_reloc_offset in EQ.
      generalize(encode_decode_addr_size_relf _ _ _ EQ0 (encode_int32 x2 ++l)).
      intros HAddrsize.
      rewrite <- app_assoc.
      rewrite HAddrsize.
      set (am:= (addrmode_reloc_offset (Addrmode base ofs0 (inl z)))).
      cbn [negb ready_for_proof negb] in HEncode.
      unfold encode_instr' in HEncode.
      monadInv HEncode.
      assert (exists irofs, instr_reloc_offset (Pmovl_rm rd (Addrmode base ofs0 (inl z))) = OK irofs)as HInstr_reloc . {
        unfold instr_reloc_offset.
        eauto.
      }
      destruct HInstr_reloc as [irofs HInstr_reloc].     
      assert(HOfs: ofs + am + 1 = irofs + ofs). {
        unfold instr_reloc_offset in HInstr_reloc.
        replace (ofs+am+1)with (1 + am + ofs) by omega.
        monadInv HInstr_reloc.        
        unfold am.
        simpl. setoid_reflexivity. 
      }                
      generalize (encode_decode_addrmode_relf _ _ _ (ofs + am + 1) _ _ _ HInstr_reloc EQ1 HOfs l).
      intros HAddr.
      rewrite app_assoc.
      simpl.
      rewrite  HAddr.
      simpl. auto.
      
    ++
      cbn [negb ready_for_proof negb] in HEncode.
      unfold encode_instr' in HEncode.
      monadInv HEncode.
      destruct p.
      destruct i; inversion EQ.
      monadInv EQ.
      generalize (encode_decode_addr_size_relf _ _ _ EQ0 (encode_int32 (Ptrofs.unsigned i0) ++ l)).
      intros HAddrsize.      
      rewrite <- app_assoc.
      remember (addrmode_reloc_offset (Addrmode base ofs0 (inr (1%positive, i0)))) as a_size.      
      setoid_rewrite <- Heqa_size in HAddrsize.
      rewrite HAddrsize.      
      simpl.
      
      assert (HOfs: ofs+a_size+1 = x + ofs). {
        replace (ofs+a_size+1) with (1+a_size+ofs) by omega.
        simpl in EQ2.
        inversion EQ2.
        rewrite Heqa_size.
        simpl. auto.
      }
      generalize (encode_decode_addrmode_relf _ _ _ (ofs + a_size + 1) _ _ _ EQ2 EQ1 HOfs l).
      intros HAddrmode.
      rewrite app_assoc.
      rewrite HAddrmode.
      simpl. auto.       
  + (* (Pmovl_mr a rs) *)
    exists  (Pmovl_mr a rs).
    split;try(unfold instr_eq; auto).
    destruct negb; inversion H10.
    clear H11.
    monadInv HEncode.
    unfold fmc_instr_decode. simpl.
    branch_byte_eq'.
    unfold decode_movl_mr.
    unfold encode_addrmode in EQ.
    destruct a. monadInv EQ.
    destruct const eqn:EQConst.
    ++ (* not reloc *)
      generalize (encode_decode_addr_size_relf _ _ _ EQ0).
      intros HAddrsize.
      rewrite <- app_assoc.
      rewrite (HAddrsize (encode_int32 x1 ++ l)).      
      remember (addrmode_reloc_offset (Addrmode base ofs0 (inl z))) as am.
      assert (exists irofs, instr_reloc_offset (Pmovl_mr (Addrmode base ofs0 (inl z)) rs) = OK irofs)as HInstr_reloc . {
        unfold instr_reloc_offset.
        eauto.
      }
      destruct HInstr_reloc as [irofs HInstr_reloc].
      simpl.
      assert(HOfs: ofs + am + 1 = irofs + ofs). {
        unfold instr_reloc_offset in HInstr_reloc.
        replace (ofs+am+1)with (1 + am + ofs) by omega.
        rewrite <- Heqam in HInstr_reloc.
        inversion HInstr_reloc.
        rewrite Heqam.
        simpl. setoid_reflexivity. 
      }
      monadInv H10.
      remember (addrmode_reloc_offset (Addrmode base ofs0 (inl z))) as am.
      generalize (encode_decode_addrmode_relf _ _ _ (ofs + am + 1) _ _ _ HInstr_reloc EQ1 HOfs l).
      intros HAddrmode.
      rewrite <- app_assoc in HAddrmode.
      rewrite HAddrmode.
      simpl. auto.
    ++ (* reloc *)
      generalize (encode_decode_addr_size_relf _ _ _ EQ0).
      intros HAddrsize.
      rewrite <- app_assoc.
      rewrite (HAddrsize (encode_int32 x1 ++ l)).      
      remember (addrmode_reloc_offset (Addrmode base ofs0 (inr p))) as am.
      assert (exists irofs, instr_reloc_offset (Pmovl_mr (Addrmode base ofs0 (inr p)) rs) = OK irofs)as HInstr_reloc . {
        unfold instr_reloc_offset.
        eauto.
      }
      destruct HInstr_reloc as [irofs HInstr_reloc].
      simpl.
      assert(HOfs: ofs + am + 1 = irofs + ofs). {
        unfold instr_reloc_offset in HInstr_reloc.
        replace (ofs+am+1)with (1 + am + ofs) by omega.
        rewrite <- Heqam in HInstr_reloc.
        inversion HInstr_reloc.
        rewrite Heqam.
        simpl. setoid_reflexivity. 
      }
      monadInv H10.
      remember (addrmode_reloc_offset (Addrmode base ofs0 (inr p))) as am.
      generalize (encode_decode_addrmode_relf _ _ _ (ofs + am + 1) _ _ _ HInstr_reloc EQ1 HOfs l).
      intros HAddrmode.
      rewrite <- app_assoc in HAddrmode.
      rewrite HAddrmode.
      simpl. auto.
      
  + (* (Pleal rd a) *)
    exists (Pleal rd a).
    split; try(unfold instr_eq; auto).
    destruct negb; inversion H10. clear H11.
    monadInv HEncode.
    unfold fmc_instr_decode. simpl.
    branch_byte_eq'.
    unfold decode_leal.
    unfold encode_addrmode in EQ.
    destruct a. monadInv EQ.
    destruct const eqn:EQConst.
    ++ (* not reloc *)
      generalize (encode_decode_addr_size_relf _ _ _ EQ0).
      intros HAddrsize.
      rewrite <- app_assoc.
      rewrite (HAddrsize (encode_int32 x1 ++ l)).      
      remember (addrmode_reloc_offset (Addrmode base ofs0 (inl z))) as am.
      assert (exists irofs, instr_reloc_offset (Pleal rd (Addrmode base ofs0 (inl z))) = OK irofs)as HInstr_reloc . {
        unfold instr_reloc_offset.
        eauto.
      }
      destruct HInstr_reloc as [irofs HInstr_reloc].
      simpl.
      assert(HOfs: ofs + am + 1 = irofs + ofs). {
        unfold instr_reloc_offset in HInstr_reloc.
        replace (ofs+am+1)with (1 + am + ofs) by omega.
        rewrite <- Heqam in HInstr_reloc.
        inversion HInstr_reloc.
        rewrite Heqam.
        simpl. setoid_reflexivity. 
      }
      monadInv H10.
      remember (addrmode_reloc_offset (Addrmode base ofs0 (inl z))) as am.
      generalize (encode_decode_addrmode_relf _ _ _ (ofs + am + 1) _ _ _ HInstr_reloc EQ1 HOfs l).
      intros HAddrmode.
      rewrite <- app_assoc in HAddrmode.
      rewrite HAddrmode.
      simpl. auto.
    ++ (* reloc *)
      generalize (encode_decode_addr_size_relf _ _ _ EQ0).
      intros HAddrsize.
      rewrite <- app_assoc.
      rewrite (HAddrsize (encode_int32 x1 ++ l)).      
      remember (addrmode_reloc_offset (Addrmode base ofs0 (inr p))) as am.
      assert (exists irofs, instr_reloc_offset  (Pleal rd (Addrmode base ofs0 (inr p))) = OK irofs) as HInstr_reloc . {
        unfold instr_reloc_offset.
        eauto.
      }
      destruct HInstr_reloc as [irofs HInstr_reloc].
      simpl.
      assert(HOfs: ofs + am + 1 = irofs + ofs). {
        unfold instr_reloc_offset in HInstr_reloc.
        replace (ofs+am+1)with (1 + am + ofs) by omega.
        rewrite <- Heqam in HInstr_reloc.
        inversion HInstr_reloc.
        rewrite Heqam.
        simpl. setoid_reflexivity. 
      }
      monadInv H10.
      remember (addrmode_reloc_offset (Addrmode base ofs0 (inr p))) as am.
      generalize (encode_decode_addrmode_relf _ _ _ (ofs + am + 1) _ _ _ HInstr_reloc EQ1 HOfs l).
      intros HAddrmode.
      rewrite <- app_assoc in HAddrmode.
      rewrite HAddrmode.
      simpl. auto.
  + (* (Paddl_ri rd n) *)
    exists (Paddl_ri rd n).
    split; try(unfold instr_eq;auto).
    destruct negb; inversion H10. clear H11.
    monadInv HEncode.
    unfold fmc_instr_decode.
    simpl.
    branch_byte_eq'.
    unfold decode_81.
    cbn.
    rewrite <- Byte.and_shru.
    rewrite shru563.
    repeat fold (bits_to_Z  (b[ "11"] ++ b[ "000"])).
    assert(Byte.shru bB[ b[ "11"] ++ b[ "000"] ++ x ] (Byte.repr 3) = Byte.repr 24) as shruValue. {
      rewrite app_assoc.
      setoid_rewrite (shru_bits 3 (b["11"]++b["000"]) x).
      simpl. auto.
      repeat rewrite app_length. simpl.
      rewrite (encode_reg_length rd); auto.
      rewrite (encode_reg_length rd); auto.
    }
    unfold bits_to_Z in shruValue.
    cbn in shruValue.
    rewrite shruValue.
    assert(Byte.and (Byte.repr 24) (Byte.repr 7) = Byte.repr 0). {
      unfold Byte.and. f_equal.
    }
    rewrite H.
    branch_byte_eq.
    unfold decode_addl_ri.
    simpl.
    assert(Byte.and  bB[ b[ "11"] ++ b[ "000"] ++ x ] (Byte.repr 7) = bB[x]) as regValue. {
      setoid_rewrite (and7 (b[ "11"] ++ b[ "000"]) x).
      auto.
      repeat rewrite app_length. simpl.
      rewrite (encode_reg_length rd); auto.
      rewrite (encode_reg_length rd); auto.
    }
    setoid_rewrite regValue.
    rewrite (encode_parse_reg_refl rd).
    simpl.
    generalize (encode_int32_size_Z (Int.unsigned n)).
    intros Hintsize.
    assert(exists e1 e2 e3 e4, (encode_int32 (Int.unsigned n))=[e1;e2;e3;e4]). {
      generalize (list_len_gt1 _ (encode_int32 (Int.unsigned n)) 3 Hintsize).
      intros (l' & t & H11).
      unfold encode_int32. unfold encode_int. unfold bytes_of_int.
      unfold rev_if_be. destruct Archi.big_endian eqn:EQED.
      inversion EQED. eauto.
    }
    destruct H11 as (e1 & e2 & e3 & e4 & H12).
    rewrite H12.
    ++ repeat f_equal.
       rewrite <- H12.         
       rewrite (encode_decode_int32_same_prefix (Int.unsigned n) l).
       simpl.
       generalize (encode_int32_4_exists _ l (encode_int32 (Int.unsigned n) ++ l) eq_refl).
       intros (b1 & b2 & b3 & b4 & HEncInt).
       rewrite HEncInt.
       simpl.
       repeat f_equal.
       rewrite Int.repr_unsigned.
       auto.
       generalize(Int.unsigned_range n).
       intros H11.
       unfold valid_int32.
       unfold Int.modulus in H11.
       unfold Int.wordsize in H11.
       unfold Wordsize_32.wordsize in H11.
       unfold two_power_nat in H11.
       simpl in H11.
       unfold two_power_pos.
       simpl.
       omega.
    ++ auto.
  + (* (Psubl_rr rd r1) *)
    exists (Psubl_rr rd r1).
    split;try(unfold instr_eq; auto).
    unfold fmc_instr_decode.
    destruct negb; inversion H10. clear H11.
    monadInv HEncode.
    simpl. 
    branch_byte_eq.
    unfold decode_subl_rr.
    cbn.
    rewrite <- Byte.and_shru.
    rewrite shru563.
    assert(Byte.shru  bB[ b[ "11"] ++ x ++ x0] (Byte.repr 3) =  bB[ b[ "11"] ++ x]) as shruValue. {
      rewrite app_assoc.
      setoid_rewrite(shru_bits 3 (b[ "11"] ++ x) x0).
      auto.
      repeat rewrite app_length.
      simpl.
      rewrite (encode_reg_length rd);auto.
      rewrite (encode_reg_length r1);auto.
      rewrite (encode_reg_length r1);auto.
    }
    unfold bits_to_Z in shruValue.
    simpl in shruValue.
    rewrite shruValue.
    setoid_rewrite (and7 b["11"] x).
    rewrite (encode_parse_reg_refl rd).
    simpl.
    setoid_rewrite (and7 (b["11"] ++ x) x0).
    rewrite (encode_parse_reg_refl r1).
    simpl. auto. auto.
    repeat rewrite app_length.
    simpl.
    rewrite (encode_reg_length rd);auto.
    1-2 :rewrite (encode_reg_length r1); auto.
    auto.
    repeat rewrite app_length.
    simpl.
    1-2 :rewrite (encode_reg_length rd); auto.
  + (* (Pimull_rr rd r1) *)
    exists (Pimull_rr rd r1).
    split;try(unfold instr_eq; auto).
    destruct negb; inversion H10. clear H11.
    monadInv HEncode.
    simpl. branch_byte_eq'.
    unfold decode_0f.
    simpl.
    rewrite byte_eq_true.
    unfold decode_imull_rr.
    simpl.
    assert((length b["11"] = 2)%nat) as len by auto.
    generalize  (decode_encode_rr_operand_refl b["11"] rd r1 x x0 len EQ EQ1).
    intros Hrr.
    simpl in Hrr.
    setoid_rewrite Hrr.
    simpl.
    auto.
  + (* (Pimull_ri rd n) *)
    exists (Pimull_ri rd n).
    split;try(unfold instr_eq; auto).
    destruct negb; inversion H10. clear H11.
    monadInv HEncode.
    simpl.
    branch_byte_eq'.
    unfold decode_imull_ri.
    simpl.      
    setoid_rewrite (and7 (b["11"]++x) x).
    rewrite (encode_parse_reg_refl rd).
    simpl.
    repeat f_equal.
    rewrite (encode_decode_int32_same_prefix (Int.unsigned n) l).
    simpl.
    generalize (encode_int32_4_exists _ l (encode_int32 (Int.unsigned n) ++ l) eq_refl).
    intros (b1 & b2 & b3 & b4 & HEncInt).
    rewrite HEncInt.
    simpl.
    repeat f_equal.
    rewrite Int.repr_unsigned. auto.
    generalize (Int.unsigned_range n). intros H.
    unfold valid_int32.
    unfold Int.modulus in H.
    unfold two_power_nat in H.
    simpl in H.
    unfold two_power_pos.
    simpl. omega.
    auto.
    repeat rewrite app_length.
    simpl.
    rewrite (encode_reg_length rd).
    auto. auto.
    rewrite (encode_reg_length rd);auto.
  + (* Pcltd *)
    exists Pcltd.
    split; try(unfold instr_eq;auto).
  + (* (Pidivl r1) *)
    exists (Pidivl r1).
    split;try(unfold instr_eq; auto).
    destruct negb; inversion H10. clear H11.
    monadInv HEncode.
    simpl. branch_byte_eq'.
    unfold decode_idivl.
    simpl.
    setoid_rewrite(and7 (b["11"]++b["111"]) x).
    rewrite (encode_parse_reg_refl r1).
    simpl.
    1-4: auto.
    repeat rewrite app_length.
    simpl.
    1-2: rewrite(encode_reg_length r1);auto.
  + (* (Pxorl_r rd) *)
    exists (Pxorl_r rd).
    split; try(unfold instr_eq; auto).
    destruct negb; inversion H10. clear H11.
    monadInv HEncode.
    simpl. branch_byte_eq. unfold decode_xorl_r.
    simpl.
    setoid_rewrite(and7 (b["11"] ++ x) x).
    rewrite (encode_parse_reg_refl rd x EQ).
    simpl.
    auto.
    repeat rewrite app_length.
    simpl.
    1-2:  repeat rewrite (encode_reg_length rd); auto.
  + (* PSall_ri rd n *)
    exists(Psall_ri rd (Int.repr (Int.unsigned n mod Byte.modulus))).
    split;try (unfold instr_eq;auto).
    destruct negb; inversion H10. clear H11.
    monadInv HEncode.
    simpl.
    branch_byte_eq'.
    unfold decode_sall_ri.
    simpl.
    setoid_rewrite(and7 ( b[ "11"] ++ b[ "100"]) x).
    rewrite (encode_parse_reg_refl rd).
    simpl.
    repeat f_equal.
    unfold decode_int_n.
    setoid_rewrite (sublist_prefix [(Byte.repr (Int.unsigned n))] l).
    
    unfold decode_int.
    unfold int_of_bytes.
    assert (rev_if_be [Byte.repr (Int.unsigned n)] = [Byte.repr (Int.unsigned n)]) as rid. {
      unfold rev_if_be.
      destruct Archi.big_endian; simpl; auto.
    }
    simpl.
    rewrite rid.
    rewrite Byte.unsigned_repr_eq.
    simpl.
    rewrite <- (Zplus_0_r_reverse (Int.unsigned n mod Byte.modulus)).
    1-4: auto.
    repeat rewrite length_app. simpl.
    1-2: rewrite (encode_reg_length rd);auto.
  + (* (Pcmpl_rr r1 r2) *)
    exists (Pcmpl_rr r1 r2).
    split;try(unfold instr_eq; auto).
    destruct negb; inversion H10. clear H11.
    monadInv HEncode.
    simpl. branch_byte_eq'.
    unfold decode_cmpl_rr.
    simpl.
    assert((length b["11"] = 2)%nat) as len by auto.
    generalize  (decode_encode_rr_operand_refl b["11"] r2 r1 x0 x len EQ1 EQ).
    intros Hrr.
    simpl in Hrr.
    setoid_rewrite Hrr.
    simpl.
    auto.
  + (* (Pcmpl_ri r1 n) *)
    exists (Pcmpl_ri r1 n).
    split; try(unfold instr_eq; auto).
    destruct negb; inversion H10. clear H11.
    monadInv HEncode.
    simpl. branch_byte_eq'.
    unfold decode_81.      
    simpl.
    assert (Byte.shru (Byte.and  bB[ b[ "11"] ++ b[ "111"] ++ x] (Byte.repr 56)) (Byte.repr 3) = Byte.repr 7) as opcodeEQ. {
      rewrite <- Byte.and_shru.
      setoid_rewrite (shru_bits 3 (b["11"]++b["111"]) x).
      unfold Byte.shru.
      simpl. repeat rewrite Byte.unsigned_repr. unfold Z.shiftr.
      simpl. unfold Byte.and. f_equal.
      unfold Byte.max_unsigned. simpl. omega.
      unfold Byte.max_unsigned. simpl. omega.
      repeat rewrite app_length.
      simpl.
      rewrite (encode_reg_length r1).
      omega.
      apply EQ.
      rewrite (encode_reg_length r1); auto.
    }
    simpl in opcodeEQ.
    rewrite opcodeEQ.
    rewrite byte_eq_true.
    unfold decode_cmpl_ri.
    simpl.
    setoid_rewrite (and7 (b["11"]++b["111"]) x).
    rewrite (encode_parse_reg_refl r1).
    simpl. repeat f_equal.
    rewrite (encode_decode_int32_same_prefix (Int.unsigned n) l).
    simpl.
    generalize (encode_int32_4_exists _ l (encode_int32 (Int.unsigned n) ++ l) eq_refl).
    intros (b1 & b2 & b3 & b4 & HEncInt).
    rewrite HEncInt.
    simpl.
    
    rewrite Int.repr_unsigned. auto.
    generalize (Int.unsigned_range n). intros H.
    unfold valid_int32.
    unfold Int.modulus in H.
    unfold two_power_nat in H.
    simpl in H.
    unfold two_power_pos.
    simpl. omega.
    1-3: auto.
    repeat rewrite app_length.
    simpl.
    1-2: rewrite (encode_reg_length r1).
    1-4: auto.
  + (* (Ptestl_rr r1 r2) *)
    exists (Ptestl_rr r2 r1).
    split;try (unfold instr_eq; auto).
    destruct negb; inversion H10. clear H11.
    monadInv HEncode.
    simpl.
    branch_byte_eq'.
    unfold decode_testl_rr.
    simpl.
    assert((length b["11"] = 2)%nat) as len by auto.
    generalize  (decode_encode_rr_operand_refl b["11"] r2 r1 x0 x len EQ1 EQ).
    intros Hrr.
    rewrite app_assoc in Hrr.
    simpl in Hrr.
    rewrite Hrr.
    simpl.
    auto.
  + (*  (Pcall ros sg) *)
    exists (Pcall ros (mksignature [] None (mkcallconv false false false))).
    split; try(unfold instr_eq; auto).
    destruct ros; inversion H10.
    destruct negb; inversion H10. clear H11.
    destruct i; inversion H10.
    clear H11.
    unfold fmc_instr_decode.
    monadInv HEncode. simpl.
    branch_byte_eq'.
    unfold decode_call.
    unfold get_instr_reloc_addend in EQ.
    monadInv EQ.
    simpl in EQ0.
    monadInv EQ0.
    unfold get_reloc_addend in EQ1.
    unfold find_ofs_in_rtbl. simpl.
    rewrite encode_decode_int32_same_prefix.
    simpl.
    destruct (ZTree.get (ofs + 1) rtbl_ofs_map); inversion EQ1.
    
    rewrite H11.
    assert(Hvalid: valid_int32 x) by admit.
    generalize (encode_int32_4_exists x l (encode_int32 x ++ l)).
    intros (b1 & b2 & b3 & b4 & HInt).
    auto.
    rewrite HInt.
    simpl. auto.
    assert(Hvalid: valid_int32 x) by admit.
    auto.
  + (* Pret *)
    exists Pret.
    split;try(unfold instr_eq; auto).
  + (* (Pmov_rm_a rd a) *)
    
    exists (Pmovl_rm rd a).
    split; try (unfold instr_eq; auto).
    destruct negb; inversion H10. clear H11.
    unfold fmc_instr_decode.
    monadInv H10. simpl.
    branch_byte_eq'.
    unfold decode_8b.
    unfold encode_instr in HEncode.    
    unfold encode_addrmode in EQ.
    assert (HmodrmExists: exists modrm, get_n (x ++ l) 0 = OK modrm). {
      destruct a.
      monadInv EQ.
      simpl in EQ0.
      inversion EQ0.
      monadInv H10.
      destruct ofs0. destruct p.
      destruct base. destruct ireg_eq. inversion EQ2.
      monadInv EQ2. simpl. eauto.
      destruct ireg_eq. inversion EQ2.
      monadInv EQ2. simpl; eauto.
      destruct base.
      monadInv EQ2.
      destruct ireg_eq.
      inversion EQ4.
      simpl.
      eauto.
      inversion EQ4.
      simpl.
      eauto.
      inversion EQ2.
      simpl.
      eauto.
    }
    destruct HmodrmExists.
    rewrite H. simpl.
    assert (HModrmPrefix : (Byte.and x0 HB[ "C0"]) <> HB["C0"] ). {
      destruct a.
      monadInv EQ.
      simpl in EQ0.
      inversion EQ0.
      monadInv H11.
      destruct ofs0. destruct p.
      destruct base. destruct ireg_eq. inversion EQ2.
      monadInv EQ2. simpl in H.
      inversion H.
      assert(HTruncate: bits_to_Z ((b["10"]++x++b["100"])++(x3++x4++x5))/256 = bits_to_Z (b["10"]++x++b["100"])). {
        replace 256 with (2^8).
        rewrite <- Z.shiftr_div_pow2.
        rewrite (Z_shru_bits 8).
        auto.
        repeat rewrite app_length.
        resolve_scale_length x3.
        resolve_reg_length x4.
        resolve_reg_length x5.
        simpl.
        1-2:omega.
        simpl.
        unfold Z.pow_pos. simpl. auto.
      }
      repeat rewrite <- app_assoc in HTruncate.
      simpl in HTruncate.
      rewrite HTruncate.
      replace (char_to_bool "1"
        :: char_to_bool "0"
           :: x ++
              [char_to_bool "1"; char_to_bool "0";
               char_to_bool "0"])
              with ((char_to_bool "1"
        :: char_to_bool "0"::[]) ++ x ++
              [char_to_bool "1"; char_to_bool "0";
               char_to_bool "0"]).
      rewrite byte_and_C0.
      intros HNot. inversion HNot.
      simpl. omega.
      rewrite app_length.
      resolve_reg_length x.
      simpl. omega.
      auto.
      
      destruct ireg_eq. inversion EQ2.
      monadInv EQ2.
      simpl in H.
      inversion H.
      assert(HTruncate: bits_to_Z ((b["00"]++x++b["100"])++(x3++x4++b["101"]))/256 = bits_to_Z (b["00"]++x++b["100"])). {
        replace 256 with (2^8).
        rewrite <- Z.shiftr_div_pow2.
        rewrite (Z_shru_bits 8).
        auto.
        repeat rewrite app_length.
        resolve_scale_length x3.
        resolve_reg_length x4.
        simpl.
        1-2:omega.
        simpl.
        unfold Z.pow_pos. simpl. auto.
      }
      repeat rewrite <-app_assoc in HTruncate.
      simpl in HTruncate.
      rewrite HTruncate.
      replace (char_to_bool "0":: char_to_bool "0":: x ++
                            [char_to_bool "1"; char_to_bool "0";
                             char_to_bool "0"])
        with ((char_to_bool "0":: char_to_bool "0"::[]) ++ x ++
                                                    [char_to_bool "1"; char_to_bool "0";char_to_bool "0"]).
      rewrite byte_and_C0.
      intros HNot. inversion HNot.
      simpl. omega.
      rewrite app_length.
      resolve_reg_length x.
      simpl. omega.
      auto.

      
      destruct base.
      monadInv EQ2.
      monadInv EQ0.
      destruct ireg_eq.
      simpl in EQ4.
      inversion EQ4.
      subst x1.
      unfold encode_int_big in H.
      simpl in H.
      inversion H.
      assert(HTruncate: bits_to_Z ((b["10"]++x++b["100"])++(b["00100"]++x3))/256 = bits_to_Z (b["10"]++x++b["100"])). {
        replace 256 with (2^8).
        rewrite <- Z.shiftr_div_pow2.
        rewrite (Z_shru_bits 8).
        auto.
        repeat rewrite app_length.
        resolve_reg_length x3.
        simpl.
        1-2:omega.
        simpl.
        unfold Z.pow_pos. simpl. auto.
      }
      repeat rewrite <-app_assoc in HTruncate.
      simpl in HTruncate.
      rewrite HTruncate.
      replace (char_to_bool "1":: char_to_bool "0":: x ++
                            [char_to_bool "1"; char_to_bool "0";
                             char_to_bool "0"])
        with ((char_to_bool "1":: char_to_bool "0"::[]) ++ x ++
                                                       [char_to_bool "1"; char_to_bool "0";char_to_bool "0"]).
      rewrite byte_and_C0.
      intros HNot. inversion HNot.
      simpl. omega.
      rewrite app_length.
      resolve_reg_length x.
      simpl. omega.
      auto.

      inversion EQ4.
      subst x1.
      simpl in H.
      inversion H.
      replace ( char_to_bool "1" :: char_to_bool "0" :: x ++ x3)
        with((char_to_bool "1" :: char_to_bool "0" ::[])++(x ++ x3)).
      rewrite byte_and_C0.
      intros HNot. inversion HNot.
      simpl. omega.
      rewrite app_length.
      resolve_reg_length x.
      resolve_reg_length x3.
      simpl. omega.
      auto.
      
      inversion EQ2.
      monadInv EQ0.
      simpl in H.
      inversion H.
      replace (char_to_bool "0":: char_to_bool "0":: x ++
                            [char_to_bool "1"; char_to_bool "0";
                             char_to_bool "1"])
        with ((char_to_bool "0":: char_to_bool "0"::[]) ++ x ++
                                                       [char_to_bool "1"; char_to_bool "0";char_to_bool "1"]).
      rewrite byte_and_C0.
      intros HNot. inversion HNot.
      simpl. omega.
      rewrite app_length.
      resolve_reg_length x.
      simpl. omega.
      auto.
    }
    rewrite byte_eq_false; auto.
    unfold decode_movl_rm.
    destruct a eqn:EQA.
    monadInv EQ.
    destruct const eqn:EQConst.
    ++
      unfold instr_reloc_offset in EQ.
      unfold addrmode_reloc_offset in EQ.
      generalize(encode_decode_addr_size_relf _ _ _ EQ0 (encode_int32 x2 ++l)).
      intros HAddrsize.
      rewrite <- app_assoc.
      rewrite HAddrsize.
      set (am:= (addrmode_reloc_offset (Addrmode base ofs0 (inl z)))).
      simpl.
      monadInv HEncode.
      assert (exists irofs, instr_reloc_offset (Pmov_rm_a rd (Addrmode base ofs0 (inl z))) = OK irofs)as HInstr_reloc . {
        unfold instr_reloc_offset.
        eauto.
      }
      destruct HInstr_reloc as [irofs HInstr_reloc].     
      assert(HOfs: ofs + am + 1 = irofs + ofs). {
        unfold instr_reloc_offset in HInstr_reloc.
        replace (ofs+am+1)with (1 + am + ofs) by omega.
        monadInv HInstr_reloc.        
        unfold am.
        simpl. setoid_reflexivity. 
      }                
      generalize (encode_decode_addrmode_relf _ _ _ (ofs + am + 1) _ _ _ HInstr_reloc EQ1 HOfs l).
      intros HAddr.
      rewrite app_assoc.
      rewrite  HAddr.
      simpl. auto.
      
    ++
      monadInv HEncode.
      destruct p.
      destruct i; inversion EQ.
      monadInv EQ.
      generalize (encode_decode_addr_size_relf _ _ _ EQ0 (encode_int32 (Ptrofs.unsigned i0) ++ l)).
      intros HAddrsize.      
      rewrite <- app_assoc.
      remember (addrmode_reloc_offset (Addrmode base ofs0 (inr (1%positive, i0)))) as a_size.      
      setoid_rewrite <- Heqa_size in HAddrsize.
      rewrite HAddrsize.      
      simpl.
      
      assert (HOfs: ofs+a_size+1 = x + ofs). {
        replace (ofs+a_size+1) with (1+a_size+ofs) by omega.
        simpl in EQ2.
        inversion EQ2.
        rewrite Heqa_size.
        simpl. auto.
      }
      generalize (encode_decode_addrmode_relf _ _ _ (ofs + a_size + 1) _ _ _ EQ2 EQ1 HOfs l).
      intros HAddrmode.
      rewrite app_assoc.
      rewrite HAddrmode.
      simpl. auto.
  + (* (Pmov_mr_a a rs) *)

    exists  (Pmovl_mr a rs).
    split;try(unfold instr_eq; auto).
    destruct negb; inversion H10. clear H11.
    monadInv HEncode.
    unfold fmc_instr_decode. simpl.
    branch_byte_eq'.
    unfold decode_movl_mr.
    unfold encode_addrmode in EQ.
    destruct a. monadInv EQ.
    destruct const eqn:EQConst.
    ++ (* not reloc *)
      generalize (encode_decode_addr_size_relf _ _ _ EQ0).
      intros HAddrsize.
      rewrite <- app_assoc.
      rewrite (HAddrsize (encode_int32 x1 ++ l)).      
      remember (addrmode_reloc_offset (Addrmode base ofs0 (inl z))) as am.
      assert (exists irofs, instr_reloc_offset (Pmov_mr_a (Addrmode base ofs0 (inl z)) rs) = OK irofs)as HInstr_reloc . {
        unfold instr_reloc_offset.
        eauto.
      }
      destruct HInstr_reloc as [irofs HInstr_reloc].
      simpl.
      assert(HOfs: ofs + am + 1 = irofs + ofs). {
        unfold instr_reloc_offset in HInstr_reloc.
        replace (ofs+am+1)with (1 + am + ofs) by omega.
        rewrite <- Heqam in HInstr_reloc.
        inversion HInstr_reloc.
        rewrite Heqam.
        simpl. setoid_reflexivity. 
      }
      monadInv H10.
      remember (addrmode_reloc_offset (Addrmode base ofs0 (inl z))) as am.
      generalize (encode_decode_addrmode_relf _ _ _ (ofs + am + 1) _ _ _ HInstr_reloc EQ1 HOfs l).
      intros HAddrmode.
      rewrite <- app_assoc in HAddrmode.
      rewrite HAddrmode.
      simpl. auto.
    ++ (* reloc *)
      generalize (encode_decode_addr_size_relf _ _ _ EQ0).
      intros HAddrsize.
      rewrite <- app_assoc.
      rewrite (HAddrsize (encode_int32 x1 ++ l)).      
      remember (addrmode_reloc_offset (Addrmode base ofs0 (inr p))) as am.
      assert (exists irofs, instr_reloc_offset (Pmov_mr_a (Addrmode base ofs0 (inr p)) rs) = OK irofs)as HInstr_reloc . {
        unfold instr_reloc_offset.
        eauto.
      }
      destruct HInstr_reloc as [irofs HInstr_reloc].
      simpl.
      assert(HOfs: ofs + am + 1 = irofs + ofs). {
        unfold instr_reloc_offset in HInstr_reloc.
        replace (ofs+am+1)with (1 + am + ofs) by omega.
        rewrite <- Heqam in HInstr_reloc.
        inversion HInstr_reloc.
        rewrite Heqam.
        simpl. setoid_reflexivity. 
      }
      monadInv H10.
      remember (addrmode_reloc_offset (Addrmode base ofs0 (inr p))) as am.
      generalize (encode_decode_addrmode_relf _ _ _ (ofs + am + 1) _ _ _ HInstr_reloc EQ1 HOfs l).
      intros HAddrmode.
      rewrite <- app_assoc in HAddrmode.
      rewrite HAddrmode.
      simpl. auto.
  + admit.
  + (*  (Pjmp_l_rel ofs0) *)
    exists  (Pjmp_l_rel ofs0).
    split;try(unfold instr_eq; auto).
    unfold fmc_instr_decode.
    simpl. branch_byte_eq'.
    unfold decode_jmp_l_rel. repeat f_equal.
    assert(H_de: (decode_int_n (encode_int32 ofs0 ++ l) 4)= OK ofs0). {
         apply (encode_decode_int32_same_prefix (ofs0) l).
         admit.
    }
    rewrite -> H_de. auto.
  + (* (Pjcc_rel c ofs0) *)
    exists (Pjcc_rel c ofs0).
    split;try(unfold instr_eq; auto).
    destruct c.
    1-12: unfold fmc_instr_decode; simpl; branch_byte_eq'.
    1-12: unfold decode_0f; simpl; rewrite byte_eq_false.
    1-24: try(intros HNot; inversion HNot).
    1-12: unfold decode_jcc_rel; simpl; branch_byte_eq'; repeat f_equal.
    1-12: rewrite (encode_decode_int32_same_prefix (ofs0) l); simpl.
    1-24: try(generalize (encode_int32_4_exists _ l (encode_int32 ofs0 ++ l) eq_refl); intros (b1 & b2 & b3 & b4 & HEncInt); rewrite HEncInt; simpl).
    1-24: try(branch_byte_eq'; auto).
    1-12: admit.
  + (* Pnop *)
    exists Pnop.
    split; try(unfold instr_eq; auto).
  + (* Psubl_ri rd n *)
    exists (Psubl_ri rd n).
    split; try(unfold instr_eq; auto).
    destruct negb; inversion H10. clear H11.
    monadInv HEncode.
    unfold fmc_instr_decode. simpl.
    branch_byte_eq.
    unfold decode_81.
    cbn.
    rewrite <- Byte.and_shru.
    rewrite shru563.
    assert(Byte.shru (bB[b[ "11"] ++ b[ "101"] ++ x]) (Byte.repr 3) = (bB[b[ "11"] ++ b[ "101"]])) as shruValue. {
      rewrite app_assoc.
      setoid_rewrite(shru_bits 3 (b[ "11"] ++ b[ "101"]) x).
      auto.
      repeat rewrite app_length.
      simpl.
      rewrite (encode_reg_length rd);auto.
      rewrite (encode_reg_length rd);auto.
    }
    unfold bits_to_Z in shruValue.
    simpl in shruValue.
    rewrite shruValue.
    assert(Byte.and (Byte.repr 29) (Byte.repr 7) = Byte.repr 5) as and297. {
      unfold Byte.and.
      f_equal.
    }
    rewrite and297.
    branch_byte_eq.
    unfold decode_subl_ri. simpl.
    setoid_rewrite (and7 ( b[ "11"] ++ b[ "101"]) x).
    rewrite (encode_parse_reg_refl rd);auto.
    simpl.
    repeat f_equal.
    rewrite encode_decode_int32_same_prefix.
    simpl.
    generalize (encode_int32_4_exists _ l (encode_int32 (Int.unsigned n) ++ l) eq_refl).
    intros (b1 & b2 & b3 & b4 & HEncInt); rewrite HEncInt.
    simpl.
    repeat f_equal.
    rewrite Int.repr_unsigned. auto.
    generalize (Int.unsigned_range n).
    intros H.
    unfold Int.modulus in H; unfold Int.wordsize in H; unfold Wordsize_32.wordsize in H.
    unfold two_power_nat in H; simpl in H.
    unfold valid_int32.
    unfold two_power_pos. simpl. omega.
    repeat rewrite app_length.
    simpl.
    rewrite (encode_reg_length rd).
    auto.
    auto.
    rewrite (encode_reg_length rd); auto.
Admitted.




  
End  PRESERVATION.
