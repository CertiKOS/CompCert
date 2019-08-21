Require Import Coqlib Integers AST Maps.
Require Import Asm Segment.
Require Import Errors.
Require Import Memtype.
Require Import FlatProgram FlatAsm FlatBinary.
Require Import Hex Bits Memdata.
Import ListNotations.
Import Hex Bits.
Require Import FlatBingen.


Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.


(** To be implemented and proved by Xu XiangZhe *)
(* Parameter fmc_instr_decode : FlatBinary.instruction -> res FlatAsm.instruction. *)


(* utils *)

Fixpoint sublist {X:Type} (lst: list X) (n: nat){struct n}: list X :=
  match lst with
  |nil => nil 
  |h::t => match n with
           |O => nil
           |S n' => h::sublist t n'
           end
  end.

Fixpoint remove_first_n  {X:Type} (lst: list X) (n: nat) {struct n} : list X :=
  match n with
  | O => lst
  | S n' =>
    match lst with
    | nil => nil
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

Definition decode_int_n (lst: list byte)(n: nat): Z := decode_int (sublist lst n).

Compute (decode_int_n [HB["00"];HB["00"];HB["00"];HB["80"]] 2).

(* parse the reg *)
Definition addrmode_parse_reg(reg: byte): res(ireg) :=
  if Byte.eq_dec reg (Byte.repr 0) then OK(RAX)
  else if Byte.eq_dec reg (Byte.repr   1) then OK(RCX)
  else if Byte.eq_dec reg (Byte.repr   2) then OK(RDX)
  else if Byte.eq_dec reg (Byte.repr   3) then OK(RBX)
  else if Byte.eq_dec reg (Byte.repr   4) then OK(RSP)
  else if Byte.eq_dec reg (Byte.repr  5) then OK(RBP)
  else if Byte.eq_dec reg (Byte.repr   6) then OK(RSI)
  else if Byte.eq_dec reg (Byte.repr  7) then OK(RDI)
  else Error(msg "reg not found").

Compute (addrmode_parse_reg (Byte.repr 2)).

(* parse SIB *)

(* parse the scale *)
Definition addrmode_SIB_parse_scale(ss: byte): res(scale) :=
  if Byte.eq_dec ss (Byte.repr 0) then OK(Scale1)
  else if Byte.eq_dec ss (Byte.repr 1) then OK(Scale2)
       else if Byte.eq_dec ss (Byte.repr 2) then OK(Scale4)
            else if Byte.eq_dec ss (Byte.repr 3) then OK(Scale8)
                 else Error(msg "Scale not found").

Compute (addrmode_SIB_parse_scale (Byte.repr 2)).

(* parse index utility *)

Definition addrmode_SIB_parse_index (idx: byte)(index: ireg) (s: scale): option (ireg * scale):=
  if Byte.eq_dec idx HB["4"] then
    None
  else
    Some (index, s).

(* parse base utility *)

Definition addrmode_SIB_parse_base (mode_b: byte)(base: ireg)(bs : byte)(mc:list byte) : res ((option ireg) * ptrofs) :=
  if Byte.eq_dec bs HB["5"] then
    if Byte.eq_dec mode_b HB["0"] then
      let ofs := decode_int_n mc 4 in
      (* no base, offset 32 *)
      OK(None, Ptrofs.repr ofs)
    else
      if Byte.eq_dec mode_b HB["1"] then
        let ofs := decode_int_n mc 1 in
        (* offset 8 *)
        OK(Some base, Ptrofs.repr ofs)
      else
        if Byte.eq_dec mode_b HB["2"] then
          let ofs := decode_int_n mc 4 in
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
        let ofs := decode_int_n mc 1 in
        (* offset 8 *)
        OK(Some base, Ptrofs.repr ofs)
      else
        if Byte.eq_dec mode_b HB["2"] then
          let ofs := decode_int_n mc 4 in
          (* offset 32 *)
          OK(Some base, Ptrofs.repr ofs)
        else
          (* error *)
          Error(msg "error in parse sib base").
                         
      

(* parse the sib *)

Definition addrmode_parse_SIB (sib: byte)(mod_b: byte)(mc:list byte): res(addrmode * (list byte)) :=
  let idx := ( Byte.shru (Byte.and sib (Byte.repr 56)) (Byte.repr 3)) in
  let ss :=  (Byte.shru sib (Byte.repr 6)) in
  let bs := (Byte.and sib (Byte.repr 7)) in
  do index <- addrmode_parse_reg idx;
  do scale <- addrmode_SIB_parse_scale ss;
  do base <- addrmode_parse_reg bs;
  let index_s := addrmode_SIB_parse_index idx index scale in
  do base_offset <- addrmode_SIB_parse_base mod_b base bs mc;
    if Byte.eq_dec mod_b HB["0"]  then
      if Byte.eq_dec bs HB["5"] then
        OK(Addrmode (fst base_offset) (index_s) (snd base_offset),(remove_first_n mc 4))
      else
        OK(Addrmode (fst base_offset) (index_s) (snd base_offset),mc)
    else
      OK(Addrmode (fst base_offset) (index_s) (snd base_offset),mc).

(* test begins here *)

(* ebp eax*1 2018915346 *)
Compute (addrmode_parse_SIB HB["05"] HB["02"] [HB["12"]; HB["34"]; HB["56"]; HB["78"]]).
(* esp eax*2 18 *)
Compute (addrmode_parse_SIB HB["44"] HB["01"] [HB["12"]; HB["34"]; HB["56"]; HB["78"]]).
(* edi None  0 *)
Compute (addrmode_parse_SIB HB["E7"] HB["00"] [HB["12"]; HB["34"]; HB["56"]; HB["78"]]).
(* None ebp*8 2018915346 *)
Compute (addrmode_parse_SIB HB["ED"] HB["00"] [HB["12"]; HB["34"]; HB["56"]; HB["78"]]).

(* test ends here *)

(* decode addr mode *)
Definition decode_addrmode(mc:list byte): res(ireg * addrmode * (list byte)):=
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
                  do result <- addrmode_parse_SIB sib MOD (remove_first_n t 1);
                    OK(reg, fst result, snd result)
                else if Byte.eq_dec RM HB["5"] then
                       let ofs:=decode_int_n t 4 in
                       OK(reg, Addrmode None None (Ptrofs.repr ofs), remove_first_n t 4)
                     else
                       OK(reg, Addrmode (Some ea_reg) None (Ptrofs.repr 0), t)
            else if Byte.eq_dec MOD HB["1"] then
                   do ea_reg <- addrmode_parse_reg RM;
                     if Byte.eq_dec RM HB["4"] then
                       do sib <- get_n t 0;
                       do result <- addrmode_parse_SIB sib MOD (remove_first_n t 1);
                         OK(reg, fst result, remove_first_n (snd result) 1)
                     else
                       let ofs:=decode_int_n t 1 in
                       OK(reg, Addrmode (Some ea_reg) None (Ptrofs.repr ofs), remove_first_n t 1)
                 else if Byte.eq_dec MOD HB["2"] then
                        do ea_reg <- addrmode_parse_reg RM;
                          if Byte.eq_dec RM HB["4"] then
                            do sib<- get_n t 0;                             
                              do result <- addrmode_parse_SIB sib MOD (remove_first_n t 1);
                              OK(reg, fst result, remove_first_n (snd result) 4)
                          else
                            let ofs:=decode_int_n t 4 in
                            OK(reg, Addrmode (Some ea_reg) None (Ptrofs.repr ofs), remove_first_n t 4)
                      else
                        Error( msg "unknown address mode")
end.

(* test begins here *)

(* eax <- edi 8ebp 1 *)
Compute (decode_addrmode [HB["44"];HB["EF"];HB["01"];HB["AA"];HB["03"];HB["04"]]).

(* ecx <- edi 1 *)
Compute (decode_addrmode [HB["4F"];HB["01"];HB["AA"];HB["03"];HB["04"]]).

(* ecx <- edi 2147483647 *)
Compute (decode_addrmode [HB["8F"];HB["FF"];HB["FF"];HB["FF"];HB["7F"];HB["AA"]]).

(* ecx <- edi*1 000000ff *)
Compute (decode_addrmode [HB["0C"];HB["3D"];HB["FF"];HB["00"];HB["00"];HB["00"];HB["AA"]]).

(* ecx <- 00000002 *)
Compute (decode_addrmode [HB["0D"];HB["02"];HB["00"];HB["00"];HB["00"];HB["AA"]]).

(* ecx <- 00000002 *)
Compute (decode_addrmode [HB["0C"];HB["25"];HB["02"];HB["00"];HB["00"];HB["00"];HB["AA"]]).

(* test ends here *)


(* parse instructions *)


(* common routines *)

Definition decode_rr_operand (modrm: byte): res(ireg * ireg) :=
   do rd <- addrmode_parse_reg (Byte.shru (Byte.and modrm HB["38"]) HB["3"]);
     do rs <- addrmode_parse_reg (Byte.and modrm HB["7"]);
     OK(rd,rs).

(* decode instructions *)

Definition decode_jmp_l (mc: list byte) : res (FlatAsm.instruction * list byte):=
  let ofs := decode_int_n mc 4 in
  OK(Fjmp_l (Ptrofs.repr ofs), remove_first_n mc 4).

(* Example jmp_test1:
  (decode_jmp_l [HB["02"];HB["00"];HB["00"];HB["00"];HB["AA"] ]) =
  OK(Fjmp_l (Ptrofs.repr 02), [HB["AA"]]).
Proof.
  unfold decode_jmp_l. simpl.
  assert(H_decode_int: forall l,
            decode_int_n ([Byte.repr 2; Byte.repr 0; Byte.repr 0; Byte.repr 0]++l) 4 = 2) by admit.
  apply (H_decode_int [Byte.repr 170]).
  reflexivity. *)

Definition decode_jcc (mc: list byte) : res (FlatAsm.instruction * list byte):=
  let ofs := Ptrofs.repr (decode_int_n (remove_first_n mc 1) 4) in
  do cond <- get_n mc 0;
  if Byte.eq_dec cond HB["84"] then OK(Fjcc Cond_e ofs, remove_first_n mc 5)
  else if Byte.eq_dec cond HB["85"] then OK(Fjcc Cond_ne ofs, remove_first_n mc 5)
  else if Byte.eq_dec cond HB["82"] then OK(Fjcc Cond_b ofs, remove_first_n mc 5)
  else if Byte.eq_dec cond HB["86"] then OK(Fjcc Cond_be ofs, remove_first_n mc 5)
  else if Byte.eq_dec cond HB["83"] then OK(Fjcc Cond_ae ofs, remove_first_n mc 5)
  else if Byte.eq_dec cond HB["87"] then OK(Fjcc Cond_a ofs, remove_first_n mc 5)
  else if Byte.eq_dec cond HB["8C"] then OK(Fjcc Cond_l ofs, remove_first_n mc 5)
  else if Byte.eq_dec cond HB["8E"] then OK(Fjcc Cond_le ofs, remove_first_n mc 5)
  else if Byte.eq_dec cond HB["8D"] then OK(Fjcc Cond_ge ofs, remove_first_n mc 5)
  else if Byte.eq_dec cond HB["8F"] then OK(Fjcc Cond_g ofs, remove_first_n mc 5)
  else if Byte.eq_dec cond HB["8A"] then OK(Fjcc Cond_p ofs, remove_first_n mc 5)
  else if Byte.eq_dec cond HB["8B"] then OK(Fjcc Cond_np ofs, remove_first_n mc 5)
       else Error (msg "Unknown jcc condition").

Compute (decode_rr_operand HB["D8"]).

Definition decode_imull_rr (mc: list byte) : res (FlatAsm.instruction * list byte):=
  do modrm <- get_n mc 0;
    do rds <- decode_rr_operand modrm;
    OK(Fimull_rr (fst rds) (snd rds), remove_first_n mc 1).

Definition decode_imull_ri (mc: list byte) : res (FlatAsm.instruction * list byte):=
  do modrm <- get_n mc 0;
     do rd <- addrmode_parse_reg (Byte.and modrm HB["7"]);
      let n := decode_int_n (remove_first_n mc 1) 4 in
      OK(Fimull_ri rd (Int.repr n), remove_first_n mc 5).
    

Definition decode_0f (mc: list byte): res(FlatAsm.instruction * list byte):=
  do code <- get_n mc 0;
  if Byte.eq_dec  code HB["AF"] then
    decode_imull_rr (remove_first_n mc 1)
  else
    decode_jcc mc.

Definition decode_shortcall (mc: list byte): res(FlatAsm.instruction * list byte):=
  let ofs := Ptrofs.repr (decode_int_n mc 4) in
  OK(Fshortcall ofs (mksignature [] None (mkcallconv false false false)), remove_first_n mc 4).

Definition decode_leal (mc: list byte): res(FlatAsm.instruction * list byte):=
  do addrs <- decode_addrmode mc;
    OK(Fleal (fst (fst addrs)) (snd (fst addrs)), (snd addrs)).

(* test begins here *)
(* Fleal RCX 2 *)
Compute (decode_leal  [HB["0C"];HB["25"];HB["02"];HB["00"];HB["00"];HB["00"];HB["AA"]]).
(* test ends here *)

Definition decode_xorl_r (mc: list byte): res(FlatAsm.instruction * list byte):=
  do modrm <- get_n mc 0;
    do rd <- addrmode_parse_reg (Byte.and modrm HB["7"]);
       OK(Fxorl_r rd, remove_first_n mc 1).

(* test_xor begins here *)
(* test_xor ends here *)

Definition decode_addl_ri  (mc: list byte): res(FlatAsm.instruction * list byte):=
    do modrm <- get_n mc 0;
      do rd <- addrmode_parse_reg (Byte.and modrm HB["7"]);
      let n := decode_int_n (remove_first_n mc 1) 4 in
      OK(Faddl_ri rd (Int.repr n), remove_first_n mc 5).

(* test add ri begins here *)
(* add eax, 0 *)
Compute (decode_addl_ri  [HB["C0"];HB["00"];HB["00"];HB["00"];HB["00"];HB["AA"];HB["BB"]]).

(* test add ri ends here *)

Definition decode_subl_ri (mc: list byte): res(FlatAsm.instruction * list byte):=
  do modrm <- get_n mc 0;
    do rd <- addrmode_parse_reg (Byte.and modrm HB["7"]);
    let n := decode_int_n (remove_first_n mc 1) 4 in
    OK(Fsubl_ri rd (Int.repr n), remove_first_n mc 5).

Definition decode_cmpl_ri (mc: list byte): res(FlatAsm.instruction * list byte):=
  do modrm <- get_n mc 0;
     do rd <- addrmode_parse_reg (Byte.and modrm HB["7"]);
      let n := decode_int_n (remove_first_n mc 1) 4 in
      OK(Fcmpl_ri rd (Int.repr n), remove_first_n mc 5).
  
Definition decode_81  (mc: list byte): res(FlatAsm.instruction * list byte):=
  do modrm <- get_n mc 0;
    let opcode := Byte.shru (Byte.and modrm HB["38"]) HB["3"] in
    if Byte.eq_dec opcode HB["7"] then decode_cmpl_ri mc
    else if Byte.eq_dec opcode HB["0"] then decode_addl_ri mc
         else if Byte.eq_dec opcode HB["5"] then decode_subl_ri mc
              else Error(msg" instruction begins with 81 cannot be found").
    
Definition decode_subl_rr (mc: list byte): res(FlatAsm.instruction * list byte):=
  do modrm <- get_n mc 0;
    do rd <- addrmode_parse_reg (Byte.shru (Byte.and modrm HB["38"]) HB["3"]);
    do rs <- addrmode_parse_reg (Byte.and modrm HB["7"]);
    OK(Fsubl_rr rd rs, remove_first_n mc 1).

(* note that the opcode of movl begins with 0xB, so we can use this info to dispatch this instruction*)
Definition decode_movl_ri  (mc: list byte): res(FlatAsm.instruction * list byte):=
  do opcode <- get_n mc 0;
    do rd <- addrmode_parse_reg (Byte.and opcode HB["7"]);
    let n := decode_int_n (remove_first_n mc 1) 4 in
    OK(Fmovl_ri rd (Int.repr n), remove_first_n mc 5).

Definition decode_mov_rr  (mc: list byte): res(FlatAsm.instruction * list byte):=
   do modrm <- get_n mc 0;
    do rds <- decode_rr_operand modrm;
    OK(Fmov_rr (fst rds) (snd rds), remove_first_n mc 1).

Definition decode_movl_rm (mc: list byte): res(FlatAsm.instruction * list byte):=
  do addrs <- decode_addrmode mc;
    OK(Fmovl_rm (fst (fst addrs)) (snd (fst addrs)), (snd addrs)).

Definition decode_movl_mr (mc: list byte): res(FlatAsm.instruction * list byte):=
  do addrs <- decode_addrmode mc;
    OK(Fmovl_mr  (snd (fst addrs)) (fst (fst addrs)), (snd addrs)).

Definition decode_movl_rm_a (mc: list byte): res(FlatAsm.instruction * list byte):=
  do addrs <- decode_addrmode mc;
    OK(Fmov_rm_a (fst (fst addrs)) (snd (fst addrs)), (snd addrs)).

Definition decode_movl_mr_a (mc: list byte): res(FlatAsm.instruction * list byte):=
  do addrs <- decode_addrmode mc;
    OK(Fmov_mr_a  (snd (fst addrs)) (fst (fst addrs)), (snd addrs)).

Definition decode_testl_rr  (mc: list byte): res(FlatAsm.instruction * list byte):=
  do modrm <- get_n mc 0;
    do rds <- decode_rr_operand modrm;
     OK(Ftestl_rr (fst rds) (snd rds), remove_first_n mc 1).

Definition decode_cmpl_rr   (mc: list byte): res(FlatAsm.instruction * list byte):=
  do modrm <- get_n mc 0;
    do rds <- decode_rr_operand modrm;
     OK(Fcmpl_rr (snd rds) (fst rds), remove_first_n mc 1).

Definition decode_idivl  (mc: list byte): res(FlatAsm.instruction * list byte):=
  do modrm <- get_n mc 0;
    do rd <- addrmode_parse_reg (Byte.and modrm HB["7"]);
    OK(Fidivl rd, remove_first_n mc 1).

Definition decode_sall_ri (mc: list byte): res(FlatAsm.instruction * list byte):=
  do modrm <- get_n mc 0;
     do rd <- addrmode_parse_reg (Byte.and modrm HB["7"]);
      let n := decode_int_n (remove_first_n mc 1) 1 in
      OK(Fsall_ri rd (Int.repr n), remove_first_n mc 2).

Definition decode_8b (mc: list byte): res(FlatAsm.instruction * list byte):=
  do modrm <- get_n mc 0;
    if Byte.eq_dec (Byte.and modrm HB["C0"]) HB["C0"] then
      decode_mov_rr mc
    else
      decode_movl_rm mc.

(*Parameter fmc_instr_decode: list byte -> res (FlatAsm.instruction * list byte).*)

Definition fmc_instr_decode (mc: list byte) : res (FlatAsm.instruction * list byte):=
    match mc with
    | nil => Error(msg "Nothing to decode")
    | h::t => if Byte.eq_dec h HB["90"] then OK(Fnop,t)
              else if Byte.eq_dec h HB["E9"] then decode_jmp_l t
              else if Byte.eq_dec h HB["0F"] then decode_0f t
              else if Byte.eq_dec h HB["E8"] then decode_shortcall t
              else if Byte.eq_dec h HB["8D"] then decode_leal t
              else if Byte.eq_dec h HB["31"] then decode_xorl_r t
              else if Byte.eq_dec h HB["81"] then decode_81 t
              else if Byte.eq_dec h HB["2B"] then decode_subl_rr t
              else if Byte.eq_dec (Byte.and h HB["F0"]) HB["B0"] then decode_movl_ri mc
              else if Byte.eq_dec h HB["8B"] then decode_8b t
              else if Byte.eq_dec h HB["89"] then decode_movl_mr t
              else if Byte.eq_dec h HB["85"] then decode_testl_rr t
              else if Byte.eq_dec h HB["C3"] then OK(Fret,t)
              else if Byte.eq_dec h HB["69"] then decode_imull_ri t
              else if Byte.eq_dec h HB["39"] then decode_cmpl_rr t
              else if Byte.eq_dec h HB["99"] then OK(Fcltd,t)
              else if Byte.eq_dec h HB["F7"] then decode_idivl t
              else if Byte.eq_dec h HB["C1"] then decode_sall_ri t
                   (* else decode_testl_rr mc *)
                   else Error(msg "Unknown opcode!")
    end.

Check Fjcc = Fjcc.







Compute (fmc_instr_decode [HB["C1"] ;HB["E2"] ;HB["05"] ;HB["00"] ;HB["01"];HB["AA"]]).








Definition instr_eq (ins1 ins2: FlatAsm.instruction): Prop :=
  match ins1 with
(*  |Fjmp_l ofs => match ins2 with
                 |Fjmp_l ofs2 => ofs = ofs2
                 |_ => False
                 end
  |Fjcc c ofs => match ins2 with
                 |Fjcc c2 ofs2 => c=c2 /\ ofs = ofs2
                 |_ => False
                 end                                          *)
  |Fshortcall ofs _ => match ins2 with
                       |Fshortcall ofs2 _ => ofs = ofs2
                       |_ => False
                       end

  |Fmov_rm_a rd a => match ins2 with
                     |Fmovl_rm rd2 a2 => rd2=rd /\ a=a2
                     |_ => False
                     end
  |Fmov_mr_a a rs => match ins2 with
                     |Fmovl_mr a2 rs2 => rs=rs2 /\ a=a2
                     |_ => False
                     end
  |Ftestl_rr r1 r2=> match ins2 with
                     |Ftestl_rr r3 r4 => (r1=r3/\r2=r4)\/(r1=r4/\r2=r3)
                     |_ => False
                     end
  |_ => ins1 = ins2
  end.



Lemma remove_first_prefix: forall {A} (l1:list A) l2 n,
    List.length l1 = n -> remove_first_n (l1 ++ l2) n = l2.
Proof.
  induction l1; simpl; subst.
  - intros. subst. simpl. auto.
  - intros. subst. simpl. auto.
Qed.


Lemma encode_int32_size : forall ofs, List.length (FlatBingen.encode_int32 (Ptrofs.unsigned ofs)) = 4%nat.
Proof.
  intros. unfold FlatBingen.encode_int32.
  rewrite encode_int_length. auto.
Qed.

Lemma encode_int32_size_Z :forall n, List.length (FlatBingen.encode_int32 n) = 4%nat.
Proof.
  intros. unfold FlatBingen.encode_int32. rewrite encode_int_length. auto.
Qed.


Lemma remove_prefix_byte: forall l ofs,
    remove_first_n (FlatBingen.encode_int32 (Ptrofs.unsigned ofs) ++l) 4 = l.
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
    sublist (l1++l2) (length l1) = l1.
Proof.
  induction l1; intros.
  - simpl in *. subst. simpl. destruct l2; auto. 
  - simpl in *. subst. simpl. f_equal. auto.
Qed.

(* Lemma sublist_prefix: forall {X} (l1:list X) n l2, *)
(*     List.length l1 = n -> sublist (l1++l2) n = l1. *)
(* Proof. *)
(*   induction l1; intros. *)
(*   - simpl in *. subst. simpl. destruct l2; auto.  *)
(*   - simpl in *. subst. simpl. f_equal. auto. *)
(* Qed. *)

Lemma sublist_id: forall {X} (l: list X),
    sublist l (length l) = l.
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
    valid_int32 n -> decode_int_n (FlatBingen.encode_int32 n) 4 = n.
Proof.
  intros. subst. unfold decode_int_n. rewrite sublist_id.
  unfold FlatBingen.encode_int32. apply encode_decode_int32_int2Z. apply H.
Qed.

Lemma encode_decode_int32_same_prefix : forall n l,
    valid_int32 n -> (decode_int_n ((FlatBingen.encode_int32 n) ++ l) 4) = n.
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


Lemma bits_to_Z_prefix: forall bits b,
    bits_to_Z (bits ++ [b]) = 2 * (bits_to_Z bits) + bool_to_Z b.
Admitted.

Lemma encode_int_big_shru : forall bits b byte,
    encode_int_big 1 (2 * bits_to_Z bits + bool_to_Z b) = [byte]
    -> encode_int_big 1 (bits_to_Z bits) = [Byte.shru byte (Byte.repr 1)].
Admitted.

Lemma byte_testbit_shru : forall byte i bi,
    Byte.testbit (Byte.shru byte (Byte.repr 1)) (Z.of_nat i) = bi ->
    Byte.testbit byte (Z.of_nat (S i)) = bi.
Admitted.


Lemma non_zero_len_not_nil : forall (A:Type) (l: list A),
    (length l > 0)%nat -> (l <> nil).
Proof.
  destruct l; simpl.
  - intros. omega.
  - intros H. intro EQ. discriminate.
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

Lemma encode_int_big_test_lsb : forall bits b byte,
    encode_int_big 1 (2 * bits_to_Z bits + bool_to_Z b) = [byte]
    -> Byte.testbit byte (Z.of_nat 0) = b.
Admitted.


Lemma encode_decode_bits_refl: forall n bits (i:nat) bi byte,
    Nat.le (length bits) 8%nat
    -> n = length bits 
    -> nth_error (rev bits) i = Some bi
    -> encode_int_big 1 (bits_to_Z bits) = [byte]
    -> Byte.testbit byte (Z.of_nat i) = bi.
Proof.
  induction n; simpl.
  - intros bits i  bi byte LE LEN NTH ECD.
    symmetry in LEN. specialize (zero_length_list _ LEN). intro. subst.
    rewrite nth_error_nil in NTH. inversion NTH.
  - intros bits i  bi byte LE LEN NTH ECD.
    destruct i.
    + assert (exists bits' bl, bits = bits' ++ [bl]) as BREV
          by (eapply list_len_gt1; eauto).
      destruct BREV as (bits' & bl & BEQ). subst bits.
      rewrite rev_unit in NTH. simpl in NTH. inversion NTH; subst.
      rewrite bits_to_Z_prefix in ECD.     
      eapply encode_int_big_test_lsb; eauto.
    + assert (exists bits' bl, bits = bits' ++ [bl]) as BREV
          by (eapply list_len_gt1; eauto).
      destruct BREV as (bits' & bl & BEQ). subst bits.
      rewrite rev_unit in NTH. simpl in NTH.
      rewrite app_length in LEN. simpl in LEN.
      assert (n = length bits') as LEN' by omega.
      rewrite bits_to_Z_prefix in ECD.
      generalize (encode_int_big_shru _ _ _ ECD). intro ECD'.
      assert (Nat.le (length bits') 8) as LE'. {
        rewrite app_length in LE. simpl in LE.
        rewrite <- LEN' in *. 
        apply Nat.le_trans with (n+1)%nat. omega. auto.
      }
      specialize (IHn _ _ _ _ LE' LEN' NTH ECD').
      apply byte_testbit_shru; auto.
Qed.

(* Lemma encode_decode_bits_refl: forall bits (i:nat) bi byte, *)
(*     Nat.le (length bits) 8%nat *)
(*     -> nth_error bits i = Some bi *)
(*     -> encode_int_big 1 (bits_to_Z bits) = [byte] *)
(*     -> Byte.testbit byte (Z.of_nat i) = bi. *)
(* Proof. *)
(*   intro bits. induction bits; simpl. *)
(*   - intros i bi byte LE NTH ECD. *)
(*     rewrite nth_error_nil in NTH. inversion NTH. *)
(*   - intros i bi byte LE NTH ECD.  *)
     


(* Lemma encode_decode_bits_refl: forall bits (i:nat), *)
(*     Nat.le (List.length bits) 8%nat -> Nat.le i 8%nat *)
(*     -> exists b one_bit, nth_error bits i = Some (one_bit) /\ Byte.testbit b (Z.of_nat i) = one_bit /\[b] = encode_int_big 1 (bits_to_Z bits). *)
(* Proof. *)
  

(*   intros. subst. exists(Byte.repr (bits_to_Z bits0)). exists( Byte.testbit bB[ bits0] (Z.of_nat i)). *)
(*   split; try split. *)
(* Admitted. *)

(* Lemma encode_decode_bits_refl: forall bits, *)
(*     Nat.le (List.length bits) 8%nat -> exists b, [b] = encode_int_big 1 (bits_to_Z bits) /\ b = Byte.repr (bits_to_Z bits). *)
(* Admitted. *)

Lemma encode_decode_int_little_refl: forall i l,
    decode_int_n ((encode_int_little 4 i)++l) 4 = i.
Admitted.

Lemma encode_parse_reg_refl: forall rd x,
    encode_ireg rd = OK x
    ->addrmode_parse_reg bB[x] = OK rd.
Admitted.

Lemma encode_decode_reg_refl: forall r x bits1 bits2,
    encode_ireg r = OK x
    -> List.length bits1 = 2%nat
    -> List.length bits2 = 11%nat
    -> exists b1 b2,
           b2 = Byte.repr (bits_to_Z (remove_first_n bits2 3))
        /\ b1 = Byte.repr (bits_to_Z (bits1 ++ x ++ (sublist bits2 3)))
        /\ [b1;b2] = encode_int_big 2 (bits_to_Z (bits1++x++bits2))
        /\ (addrmode_parse_reg (Byte.shru (Byte.and b1 (Byte.repr 56)) (Byte.repr 3))) = OK r.
Proof.
  intros. destruct H.
Admitted.

Lemma encode_parse_scale_refl: forall s,
    addrmode_SIB_parse_scale bB[encode_scale s] = OK s.
Admitted.


Lemma encode_scale_length: forall s,
    length(encode_scale s) = 2%nat.
Proof.
  case s eqn:EQs;
    unfold encode_scale;
    simpl; auto.
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
    ++ simpl. omega.
    ++ simpl. unfold two_power_nat. simpl.
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
    simpl.
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
    simpl.
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


(** Reflexivity between the encoding and decoding of addressing modes *) 
Lemma encode_decode_addrmode_refl: forall a rd x l,
    encode_addrmode a rd = OK x ->
    decode_addrmode (x ++ l) = OK (rd, a, l).
Proof.
  intros. subst. unfold encode_addrmode in H. destruct a eqn:EQa.
  monadInv H. unfold encode_addrmode_aux in EQ. monadInv EQ.
  case index eqn:EQI.
  + case base eqn: EQB.
    ++ destruct p.
       destruct (ireg_eq i0 RSP) eqn:EQR in EQ1; inversion EQ1.
       monadInv EQ1.
       (* Set Printing All. *)
       set (X := (b[ "10"]) ) in EQ1.
       (* monadInv EQ1. *)
       exploit (encode_decode_reg_refl rd x b["10"] (char_to_bool "1" :: char_to_bool "0" :: char_to_bool "0" :: encode_scale s ++ x1 ++ x2) EQ0); eauto.
    * 
      unfold length.
      assert(Nat.eq (length((encode_scale s)++x1++x2)) (length(encode_scale s)+length(x1)+length(x2))) as lenBreakDown. {
        rewrite (app_length).
        rewrite (app_length).
        rewrite (Nat.add_assoc).
        unfold Nat.eq.
        auto.
      }
      
      
      rewrite lenBreakDown.
      rewrite (encode_scale_length s).
      simpl.
      rewrite (encode_reg_length i0 x1);auto.
      rewrite (encode_reg_length i x2);auto.
      
    * intros (b1 & b2 & B1 & B2 & ECD & ADDR).
      setoid_rewrite <- ECD. 
      simpl. rewrite ADDR. simpl.
      assert((Byte.shru b1 (Byte.repr 6))=(Byte.repr 2)) as modValue. {
        rewrite B2.
        setoid_rewrite (shru_bits 6 b["10"] ( x ++ sublist (char_to_bool "1" :: char_to_bool "0" :: char_to_bool "0" :: encode_scale s ++ x1 ++ x2) 3)).
        - simpl. auto.
        -
          setoid_rewrite (sublist_prefix [char_to_bool "1" ; char_to_bool "0" ; char_to_bool "0"] (encode_scale s ++ x1 ++ x2)).
          repeat rewrite app_length.
          simpl.
          rewrite (encode_reg_length rd);auto.
        - setoid_rewrite (sublist_prefix [char_to_bool "1" ; char_to_bool "0" ; char_to_bool "0"] (encode_scale s ++ x1 ++ x2)).
          repeat rewrite app_length.
          simpl.
          rewrite (encode_reg_length rd);auto.
      }
      rewrite modValue. branch_byte_eq.
      assert((Byte.and b1 (Byte.repr 7))=(Byte.repr 4)) as regValue. {

        rewrite B2.
        setoid_rewrite (and7 ( b[ "10"] ++ x) (sublist (char_to_bool "1" :: char_to_bool "0" :: char_to_bool "0" :: encode_scale s ++ x1 ++ x2) 3) ).
        + unfold sublist. simpl. destruct( encode_scale s ++ x1 ++ x2);auto.
        + auto. setoid_rewrite (sublist_prefix [char_to_bool "1" ; char_to_bool "0" ; char_to_bool "0"] (encode_scale s ++ x1 ++ x2)).
          repeat rewrite app_length.
          simpl.
          rewrite (encode_reg_length rd);auto.
        + setoid_rewrite (sublist_prefix [char_to_bool "1" ; char_to_bool "0" ; char_to_bool "0"] (encode_scale s ++ x1 ++ x2)).
          simpl.
          auto.
      }
      rewrite regValue. unfold addrmode_parse_reg.
      repeat (rewrite byte_eq_false; [ idtac | prove_byte_neq ]);
        rewrite byte_eq_true.
      simpl. branch_byte_eq.
      unfold addrmode_parse_SIB.
      assert((Byte.shru (Byte.and b2 (Byte.repr 56)) (Byte.repr 3))=bB[x1]) as indexBits. {
        rewrite <- Byte.and_shru.
        rewrite B1.
        setoid_rewrite (remove_first_prefix [char_to_bool "1" ; char_to_bool "0" ; char_to_bool "0" ] (encode_scale s ++ x1 ++ x2) 3).
        replace ( encode_scale s ++ x1 ++ x2) with (( encode_scale s ++ x1 )++ x2).
        
        + setoid_rewrite (shru_bits 3 (encode_scale s ++ x1) x2).
          ++ assert(Byte.shru (Byte.repr 56) (Byte.repr 3) = Byte.repr 7) as valueOfShr. {
               unfold Byte.shru. f_equal.
             }
             rewrite valueOfShr.
             rewrite and7;auto.
             +++ repeat rewrite app_length.
                 rewrite (encode_scale_length).
                 rewrite (encode_reg_length i0);auto.
             +++ rewrite (encode_reg_length i0);auto.
          ++ repeat rewrite app_length.
             rewrite (encode_scale_length).
             rewrite (encode_reg_length i0);auto.
             rewrite (encode_reg_length i);auto.
          ++ rewrite (encode_reg_length i);auto.
        + rewrite app_assoc. auto.
        + simpl. auto.
      }
      rewrite indexBits.
      assert( addrmode_parse_reg bB[ x1] = OK i0) as indexValue. {
        apply (encode_parse_reg_refl i0).
        apply EQ.
      }
      rewrite indexValue.
      simpl.
      assert((Byte.shru b2 (Byte.repr 6))=bB[(encode_scale s)]) as scaleBits. {
        rewrite B1.
        setoid_rewrite (remove_first_prefix [char_to_bool "1" ; char_to_bool "0" ;char_to_bool "0"] (encode_scale s ++ x1 ++ x2) 3).
        + setoid_rewrite (shru_bits 6 (encode_scale s) (x1++x2)).
          ++ auto.
          ++
            repeat rewrite app_length.
            rewrite (encode_scale_length).
            rewrite (encode_reg_length i0);auto.
            rewrite (encode_reg_length i);auto.
          ++
            repeat rewrite app_length.
            rewrite (encode_reg_length i0);auto.
            rewrite (encode_reg_length i);auto.
        + simpl. auto.
      }
      rewrite scaleBits.
      assert(addrmode_SIB_parse_scale bB[ encode_scale s] = (OK s)) as scale_refl. {
        apply (encode_parse_scale_refl s).
      }
      rewrite scale_refl.
      simpl.
      assert((Byte.and b2 (Byte.repr 7)) = bB[x2]) as baseBits. {
        rewrite B1.
        setoid_rewrite (remove_first_prefix  [char_to_bool "1" ; char_to_bool "0" ;char_to_bool "0"] (encode_scale s ++ x1 ++ x2) 3).
        + rewrite app_assoc.
          setoid_rewrite (and7 (encode_scale s ++ x1) x2);auto.
          ++
            repeat rewrite app_length.
            rewrite (encode_scale_length).
            rewrite (encode_reg_length i0);auto.
            rewrite (encode_reg_length i);auto.
          ++ rewrite (encode_reg_length i);auto.
        + simpl. auto.
      }
      rewrite baseBits.
      assert(addrmode_parse_reg bB[ x2] = (OK i)) as baseValue. {
        rewrite (encode_parse_reg_refl i).
        + auto.
        + apply EQ1.
      }
      rewrite baseValue.
      simpl.
      unfold addrmode_SIB_parse_base.
      destruct ( Byte.eq_dec bB[ x2] HB[ "5"]) eqn:EQ_Base.
      repeat (rewrite byte_eq_false; [ idtac | prove_byte_neq ]);
        rewrite byte_eq_true.
      simpl. rewrite byte_eq_false;try prove_byte_neq.
      simpl.
  - repeat f_equal.
    --
      unfold addrmode_SIB_parse_index.
      assert(bB[x1] <> HB["4"]) as x1EQ. {
        unfold not.
        intros H.
        unfold encode_ireg in EQ.
        case i0 eqn:EQI; inversion EQ; rewrite <- H12 in H; simpl in H; inversion H.
        auto.
      }
      rewrite byte_eq_false.
      --- auto.
      --- apply x1EQ.
    -- specialize (encode_decode_int_little_refl (Ptrofs.unsigned disp) l).
       intros.
       (* Set Printing All. *)
       simpl in H.
       rewrite H.  rewrite (Ptrofs.repr_unsigned). auto.
  -  repeat (rewrite byte_eq_false; [ idtac | prove_byte_neq ]);
       rewrite byte_eq_true. simpl.
     repeat (rewrite byte_eq_false; [ idtac | prove_byte_neq ]).
     simpl.
     repeat f_equal.
     --
       unfold addrmode_SIB_parse_index.
       assert(bB[x1] <> HB["4"]) as x1EQ. {
        unfold not.
        intros H.
        unfold encode_ireg in EQ.
        case i0 eqn:EQI; inversion EQ; rewrite <- H12 in H; simpl in H; inversion H.
        auto.
       }
       rewrite byte_eq_false.
       auto. auto.
     --  specialize (encode_decode_int_little_refl (Ptrofs.unsigned disp) l).
         intros.
         (* Set Printing All. *)
         simpl in H.
         rewrite H.  rewrite (Ptrofs.repr_unsigned). auto.



         
         ++ destruct p.
            destruct (ireg_eq i RSP) in EQ1; inversion EQ1.
            monadInv EQ1.
            exploit (encode_decode_reg_refl rd x b["00"] (char_to_bool "1" :: char_to_bool "0" :: char_to_bool "0" :: encode_scale s ++ x1 ++char_to_bool "1" :: char_to_bool "0" :: [char_to_bool "1"]) EQ0); eauto. simpl.
            repeat rewrite app_length.
            rewrite (encode_scale_length).
            rewrite (encode_reg_length i);auto.
            intros(b1 & b2 & B2 & B1 & Eenc & EAddr ).
            setoid_rewrite <- Eenc.
            unfold decode_addrmode.
            simpl.
            rewrite EAddr.
            simpl.
            assert ((Byte.shru b1 (Byte.repr 6))=(Byte.repr 0)) as modBits. {
              rewrite B1.
              setoid_rewrite (shru_bits 6  b[ "00"] (x++ sublist
             (char_to_bool "1"
              :: char_to_bool "0"
              :: char_to_bool "0" :: encode_scale s ++ x1 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"]) 3)).
              simpl. auto.
              +
                repeat rewrite app_length.
                setoid_rewrite(sublist_prefix [char_to_bool "1"
                                               ;char_to_bool "0" ; char_to_bool "0"] ( encode_scale s ++ x1 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"])).
                simpl.
                rewrite (encode_reg_length rd); auto. 
                
                
              + repeat rewrite app_length.
                setoid_rewrite(sublist_prefix [char_to_bool "1"
                                               ;char_to_bool "0" ; char_to_bool "0"] ( encode_scale s ++ x1 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"])).
                simpl.
                rewrite (encode_reg_length rd); auto. 
            }
            rewrite modBits.
            rewrite byte_eq_true.
            assert ((Byte.and b1 (Byte.repr 7))=(Byte.repr 4)) as rmBits. {
              rewrite B1.
              setoid_rewrite (and7 (b[ "00"]++x) (sublist
             (char_to_bool "1"
              :: char_to_bool "0"
              :: char_to_bool "0" :: encode_scale s ++ x1 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"]) 3)).
              + f_equal. setoid_rewrite (sublist_prefix [char_to_bool "1"
                                                         ; char_to_bool "0"; char_to_bool "0"] ( encode_scale s ++ x1 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"])).
                simpl. auto.
              +
                 repeat rewrite app_length.
                setoid_rewrite(sublist_prefix [char_to_bool "1"
                                               ;char_to_bool "0" ; char_to_bool "0"] ( encode_scale s ++ x1 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"])).
                simpl.
                rewrite (encode_reg_length rd); auto. 
              +  repeat rewrite app_length.
                setoid_rewrite(sublist_prefix [char_to_bool "1"
                                               ;char_to_bool "0" ; char_to_bool "0"] ( encode_scale s ++ x1 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"])).
                simpl. auto.
            }
            rewrite rmBits.
            unfold addrmode_parse_reg.
            repeat (rewrite byte_eq_false; [ idtac | prove_byte_neq ]);
              rewrite byte_eq_true.
            simpl.
            rewrite byte_eq_true.
            unfold addrmode_parse_SIB.
            assert ((Byte.shru (Byte.and b2 (Byte.repr 56)) (Byte.repr 3)) = bB[x1]) as indexBits. {
              rewrite <- Byte.and_shru.
              assert(Byte.shru (Byte.repr 56) (Byte.repr 3) = Byte.repr 7) as value7. {
                unfold Byte.shru. f_equal.
              }
              rewrite value7.
              rewrite B2.
              rewrite (remove_first_prefix [char_to_bool "1"; char_to_bool "0"; char_to_bool "0"]
                                           ( encode_scale s ++ x1 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"])).
              replace (encode_scale s ++ x1 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"]) with ((encode_scale s ++ x1)++[char_to_bool "1"; char_to_bool "0"; char_to_bool "1"]).
              setoid_rewrite (shru_bits 3 (encode_scale s ++ x1)  [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"]).
              rewrite (and7 (encode_scale s) x1).
              auto.
              +
                repeat rewrite app_length.
                rewrite (encode_scale_length).
                rewrite (encode_reg_length i); auto.
              + rewrite (encode_reg_length i); auto.
              + repeat rewrite app_length.
                rewrite (encode_scale_length).
                rewrite (encode_reg_length i); auto.              
              + simpl. auto.
              + rewrite app_assoc. auto.
              + simpl. auto.               
            }
            rewrite indexBits.
            exploit (encode_parse_reg_refl i);eauto.
            intros. rewrite H. simpl.
            assert ((Byte.shru b2 (Byte.repr 6)) = bB[(encode_scale s)]) as scaleBits. {
              rewrite B2.
              rewrite (remove_first_prefix  [char_to_bool "1"; char_to_bool "0"; char_to_bool "0"]
                                            ( encode_scale s ++ x1 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"])).
              replace (encode_scale s ++ x1 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"]) with ((encode_scale s) ++ x1++[char_to_bool "1"; char_to_bool "0"; char_to_bool "1"]).
              setoid_rewrite (shru_bits 6 (encode_scale s)  (x1++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"])).
              auto.
              + repeat rewrite app_length.
                rewrite (encode_scale_length).
                rewrite (encode_reg_length i); auto.
              + repeat rewrite app_length.             
                rewrite (encode_reg_length i); auto.
              
              + auto.
              + auto.
            }
            rewrite scaleBits.
            assert(addrmode_SIB_parse_scale bB[ encode_scale s] = (OK s)) as scale_refl. {
              apply (encode_parse_scale_refl s).
            }
            rewrite scale_refl. simpl.
            assert( (Byte.and b2 (Byte.repr 7)) = (Byte.repr 5)) as baseBits. {
              rewrite B2.
              rewrite (remove_first_prefix  [char_to_bool "1"; char_to_bool "0"; char_to_bool "0"]
                                            ( encode_scale s ++ x1 ++ [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"])).
              rewrite app_assoc.
              rewrite(and7 ( encode_scale s ++ x1)  [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"]).
              simpl. auto.
              + repeat rewrite app_length.
                rewrite (encode_scale_length).
                rewrite (encode_reg_length i); auto.              
              + auto.
              + auto.
            }
               
            rewrite baseBits.
            unfold addrmode_parse_reg.
            repeat (rewrite byte_eq_false; [ idtac | prove_byte_neq ]);
              rewrite byte_eq_true.
            simpl.
            unfold addrmode_SIB_parse_base.
            rewrite byte_eq_true.
            rewrite byte_eq_true. simpl.
            repeat rewrite byte_eq_true.
            simpl.
            repeat f_equal.
     --
       unfold addrmode_SIB_parse_index.
       assert(bB[x1] <> HB["4"]) as x1EQ. {
         unfold not.
         intros H11.

         unfold encode_ireg in EQ.
         case i eqn:EQI; inversion EQ; rewrite <- H13 in H11; simpl in H11; inversion H11.
         auto.
       }
      rewrite byte_eq_false. auto. auto.
     --  specialize (encode_decode_int_little_refl (Ptrofs.unsigned disp) l).
         intros.
         (* Set Printing All. *)
         simpl in H11.
         rewrite H11.  rewrite (Ptrofs.repr_unsigned). auto.
     + destruct base.
       ++ monadInv EQ1. destruct (ireg_eq i RSP) eqn:EQReg.
          +++ inversion EQ2. unfold decode_addrmode.
              exploit (encode_decode_reg_refl rd x b["10"] (b[ "100"] ++ b[ "00"] ++ b[ "100"] ++ x1));eauto.
  - repeat rewrite app_length.
    simpl.
    rewrite (encode_reg_length i); auto.
    
  - intros (b1 & b2 & B2 & B1 & Eenc & EAddr).
    setoid_rewrite <- Eenc.
    simpl.
    assert( (Byte.shru (Byte.and b1 (Byte.repr 56)) (Byte.repr 3)) = bB[x]) as regBits. {
      rewrite <- Byte.and_shru.
      assert(Byte.shru (Byte.repr 56) (Byte.repr 3) = Byte.repr 7) as valueOfShr. {
               unfold Byte.shru. f_equal.
      }
      rewrite valueOfShr.
      rewrite B1.
      rewrite app_assoc.
      setoid_rewrite (shru_bits 3 (b[ "10"] ++ x) ( sublist (b[ "100"] ++ b[ "00"] ++ b[ "100"] ++ x1) 3)).
      + setoid_rewrite (and7 b["10"] x).
        auto.
        ++ repeat rewrite app_length.
           simpl.
           rewrite (encode_reg_length rd); auto.
              
        ++ rewrite (encode_reg_length rd); auto.
      + repeat rewrite app_length.
        setoid_rewrite (sublist_prefix b["100"] ( b[ "00"] ++ b[ "100"] ++ x1)).
        simpl.
        rewrite (encode_reg_length rd);auto.
      + setoid_rewrite (sublist_prefix b["100"] (b[ "00"] ++ b[ "100"] ++ x1)). simpl. auto.
    }
    rewrite regBits.
    assert ( addrmode_parse_reg bB[ x] = (OK rd)) as regValue. {
      apply (encode_parse_reg_refl rd). auto.
    }
    rewrite regValue.
    simpl.
    assert((Byte.shru b1 (Byte.repr 6))=(Byte.repr 2)) as modBits. {
      rewrite B1.
      setoid_rewrite (shru_bits 6  b[ "10"] ( x ++ sublist (b[ "100"] ++ b[ "00"] ++ b[ "100"] ++ x1) 3)).
      simpl. auto.
      +
        repeat rewrite app_length.
        simpl.
        rewrite (encode_reg_length rd); auto.
      +
        repeat rewrite app_length.
        simpl.
        rewrite (encode_reg_length rd); auto.
    }
    rewrite modBits.
    repeat (rewrite byte_eq_false; [ idtac | prove_byte_neq ]);
      rewrite byte_eq_true.
    assert((Byte.and b1 (Byte.repr 7)) = (Byte.repr 4)) as ea_regBits. {
      rewrite B1.
      rewrite app_assoc.
      setoid_rewrite (and7  (b[ "10"] ++ x) ( sublist (b[ "100"] ++ b[ "00"] ++ b[ "100"] ++ x1) 3)).
      + setoid_rewrite (sublist_prefix b["100"]  (b[ "00"] ++ b[ "100"] ++ x1)). auto.
      + repeat rewrite app_length.
        simpl.
        rewrite (encode_reg_length rd); auto.
      +  setoid_rewrite (sublist_prefix b["100"]  (b[ "00"] ++ b[ "100"] ++ x1)). auto.
    }
    rewrite ea_regBits.
    unfold addrmode_parse_reg.
    repeat (rewrite byte_eq_false; [ idtac | prove_byte_neq ]);
      rewrite byte_eq_true.
    simpl.
    rewrite byte_eq_true.
    unfold addrmode_parse_SIB.
    assert((Byte.shru (Byte.and b2 (Byte.repr 56)) (Byte.repr 3)) = (Byte.repr 4)) as indexBits. {
      rewrite <- Byte.and_shru.
      assert(Byte.shru (Byte.repr 56) (Byte.repr 3) = Byte.repr 7) as valueOfShr. {
        unfold Byte.shru. f_equal.
      }
      rewrite valueOfShr.
      rewrite B2.
      rewrite (remove_first_prefix b["100"] ( b[ "00"] ++ b[ "100"] ++ x1)).
      +
        rewrite app_assoc.
        setoid_rewrite (shru_bits 3 ( b[ "00"] ++ b[ "100"]) x1).
        simpl. unfold Byte.and. f_equal.
        ++ repeat rewrite app_length.
           simpl.
           rewrite (encode_reg_length i); auto.
        ++ rewrite (encode_reg_length i); auto.
      + auto.
    }
    rewrite indexBits.
    unfold addrmode_parse_reg.
    simpl.
    repeat (rewrite byte_eq_false; [ idtac | prove_byte_neq ]);
      rewrite byte_eq_true.
    simpl.
    assert ( (Byte.shru b2 (Byte.repr 6)) = (Byte.repr 0)) as scaleBits. {
      rewrite B2.
      rewrite (remove_first_prefix b["100"] (b[ "00"] ++ b[ "100"] ++ x1)).
      setoid_rewrite (shru_bits 6 b["00"] ( b[ "100"] ++ x1)). auto.
      + repeat rewrite app_length.
        simpl.
        rewrite (encode_reg_length i); auto.
      + repeat rewrite app_length.
        simpl.
        rewrite (encode_reg_length i); auto.
      + auto.
    }
    rewrite scaleBits. unfold addrmode_SIB_parse_scale.
    repeat (rewrite byte_eq_false; [ idtac | prove_byte_neq ]);
      rewrite byte_eq_true.
    simpl.
    assert( (Byte.and b2 (Byte.repr 7)) = bB[x1]) as baseBits. {
      rewrite B2.
      rewrite (remove_first_prefix b["100"] ( b[ "00"] ++ b[ "100"] ++ x1)).
      rewrite app_assoc.
      setoid_rewrite (and7 (b[ "00"] ++ b[ "100"]) x1). auto.
      + repeat rewrite app_length.
        simpl.
        rewrite (encode_reg_length i); auto.
      + rewrite (encode_reg_length i); auto.
      + auto.
    }
    rewrite baseBits.
    assert(addrmode_parse_reg bB[ x1] = (OK i)) as baseValue. {
      apply(encode_parse_reg_refl i). auto.
    }
    setoid_rewrite baseValue.
    simpl.
    unfold addrmode_SIB_parse_base.
    assert(x1 = b["100"]) as iRsp. {
      rewrite e in EQ.
      unfold encode_ireg in EQ.
      inversion EQ.
      auto.
    }
    rewrite iRsp.
    repeat (rewrite byte_eq_false; [ idtac | prove_byte_neq ]);
      rewrite byte_eq_true.
    simpl.
    rewrite byte_eq_false;auto.
    simpl.
    repeat f_equal.
    -- specialize (encode_decode_int_little_refl (Ptrofs.unsigned disp) l).
       intros.
       (* Set Printing All. *)
       simpl in H.
       rewrite H.  rewrite (Ptrofs.repr_unsigned). auto.
    -- prove_byte_neq.
       +++ set (b1 := bB[ b[ "10"] ++ x ++ x1]) in EQ2. inversion EQ2. unfold decode_addrmode.
           simpl.
           assert( (Byte.shru (Byte.and b1 (Byte.repr 56)) (Byte.repr 3)) = bB[x]) as REGBits. {
             unfold b1.
             rewrite <- Byte.and_shru.
             assert(Byte.shru (Byte.repr 56) (Byte.repr 3) = Byte.repr 7) as valueOfShr. {
               unfold Byte.shru. f_equal.
             }             
             rewrite valueOfShr.
             rewrite app_assoc.
             setoid_rewrite(shru_bits 3 (b["10"]++x) x1).
             setoid_rewrite (and7 b["10"] x). auto.
             + repeat rewrite app_length.
               simpl.
               rewrite (encode_reg_length rd); auto.
             + repeat rewrite app_length.
               simpl.
               rewrite (encode_reg_length rd); auto.
             + repeat rewrite app_length.
               simpl.
               rewrite (encode_reg_length rd); auto.
               rewrite (encode_reg_length i); auto.
             + rewrite (encode_reg_length i); auto.
           }

           rewrite REGBits.
           rewrite (encode_parse_reg_refl rd).
           simpl.
           assert((Byte.shru b1 (Byte.repr 6))=(Byte.repr 2)) as modBits. {
             unfold b1.
             setoid_rewrite (shru_bits 6 b["10"] (x++x1)).
             auto.
             + repeat rewrite app_length.
               simpl.
               rewrite (encode_reg_length rd); auto.
               rewrite (encode_reg_length i); auto.
             + repeat rewrite app_length.
               simpl.
               rewrite (encode_reg_length rd); auto.
               rewrite (encode_reg_length i); auto.
           }
           rewrite modBits.
           repeat (rewrite byte_eq_false; [ idtac | prove_byte_neq ]);
             rewrite byte_eq_true.
           assert((Byte.and b1 (Byte.repr 7)) = bB[x1]) as ea_regBits. {
             unfold b1.
             rewrite app_assoc.
             setoid_rewrite(and7  (b[ "10"] ++ x) x1). auto.
             + repeat rewrite app_length.
               simpl.
               rewrite (encode_reg_length rd); auto.
               rewrite (encode_reg_length i) ; auto.
             + rewrite (encode_reg_length i); auto.
           }
           rewrite ea_regBits.
           rewrite (encode_parse_reg_refl i).
           simpl.
           assert( x1 <> b["100"]) as iNERsp. {
             unfold not.
             intros H.
             rewrite H in EQ.
             unfold encode_ireg in EQ.
             destruct i;inversion EQ.
             auto.
           }

           rewrite byte_eq_false.
           repeat f_equal.  specialize (encode_decode_int_little_refl (Ptrofs.unsigned disp) l).
           intros.
           (* Set Printing All. *)
           simpl in H.
           rewrite H.  rewrite (Ptrofs.repr_unsigned). auto.
    *
      unfold not. intros H.
      unfold encode_ireg in EQ.
      destruct i; inversion EQ; rewrite <- H12 in H; simpl in H; inversion H.
      auto.     
    * auto.
    * auto.
      ++ set (b1:= bB[ b[ "00"] ++ x ++ b[ "101"]]) in EQ1.
         inversion EQ1.
         unfold decode_addrmode.
         simpl.
         assert( (Byte.shru (Byte.and b1 (Byte.repr 56)) (Byte.repr 3)) = bB[x]) as REGBits. {
            unfold b1.
             rewrite <- Byte.and_shru.
             assert(Byte.shru (Byte.repr 56) (Byte.repr 3) = Byte.repr 7) as valueOfShr. {
               unfold Byte.shru. f_equal.
             }             
             rewrite valueOfShr.
             rewrite app_assoc.
             setoid_rewrite(shru_bits 3 (b["00"]++x) b["101"]).
             setoid_rewrite (and7 b["00"] x). auto.
            + repeat rewrite app_length.
              simpl.
              rewrite (encode_reg_length rd); auto.
            + repeat rewrite app_length.
              simpl.
              rewrite (encode_reg_length rd); auto.
            + repeat rewrite app_length.
              simpl.
              rewrite (encode_reg_length rd); auto.
            + auto.
         }
         rewrite REGBits.
         rewrite (encode_parse_reg_refl rd).
         simpl.
         assert( (Byte.shru b1 (Byte.repr 6)) = (Byte.repr 0)) as modBits. {
           unfold b1.
           setoid_rewrite (shru_bits 6 b["00"] (x++b["101"])).
           auto.
           + repeat rewrite app_length.
             simpl.
             rewrite (encode_reg_length rd); auto.
           + repeat rewrite app_length.
             simpl.
             rewrite (encode_reg_length rd); auto.
         }
         rewrite modBits.
         rewrite byte_eq_true.
         assert((Byte.and b1 (Byte.repr 7))=(Byte.repr 5)) as ea_regBits. {
           unfold b1.
           setoid_rewrite (and7 (b["00"]++x) b["101"]).
           auto.
           + repeat rewrite app_length.
             simpl.
             rewrite (encode_reg_length rd); auto.
           + auto.
         }
         rewrite ea_regBits.
         unfold addrmode_parse_reg.
         repeat (rewrite byte_eq_false; [ idtac | prove_byte_neq ]);
           rewrite byte_eq_true.
         simpl.
         rewrite byte_eq_false. rewrite byte_eq_true.
         repeat f_equal.  specialize (encode_decode_int_little_refl (Ptrofs.unsigned disp) l).
         intros.
         (* Set Printing All. *)
         simpl in H.
         rewrite H.  rewrite (Ptrofs.repr_unsigned). auto.
    * prove_byte_neq.
    * auto.
Qed.


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
Admitted.

Lemma decode_encode_rr_operand_refl: forall l r1 r2 x x0,
    (length l = 2)%nat ->
    encode_ireg r1 = OK x ->
    encode_ireg r2 = OK x0 ->
    decode_rr_operand bB[l++x++x0] = OK(r1, r2).
Admitted.

Lemma Z_shru_bits: forall n l1 l2,
    (length l2 = n)%nat ->
          Z.shiftr (bits_to_Z (l1++l2)) (Z.of_nat n) = bits_to_Z l1.
Admitted.

Lemma encode_addr_neq_c0: forall a rd x l,
    encode_addrmode a rd = OK x ->
    exists modrm, get_n (x++l) 0 = OK modrm /\ (Byte.and modrm HB["C0"]) <> HB["C0"].
Proof.
  intros a rd x l EQ.
  destruct a.
  destruct base.
  + destruct index.
    ++ unfold encode_addrmode in EQ.
       unfold encode_addrmode_aux in EQ.
       simpl in EQ.
       monadInv EQ.
       monadInv EQ0.
       destruct p in EQ1.
       destruct (ireg_eq i0 RSP) eqn:EQR; inversion EQ1.
       monadInv EQ1.
       simpl.
       exists (bB[ b[ "10"] ++ x ++ b[ "100"]]).
       replace 256 with (2^8).
       rewrite <- Z.shiftr_div_pow2.
      
       assert(length(encode_scale s ++ x1 ++ x2) = 8%nat) as len. {
         repeat rewrite app_length.
         simpl.
         rewrite (encode_scale_length s).
         rewrite (encode_reg_length i0); auto.
         rewrite (encode_reg_length i); auto.
       }
       generalize (Z_shru_bits 8 (b["10"] ++ x ++ b["100"]) ( encode_scale s ++ x1 ++ x2) len).
       intros H.
       repeat rewrite <- app_assoc in H.
       simpl in H.
       rewrite H.
       split.
       +++ simpl. auto.
       +++ 
         assert((length b["10"] <= 2)%nat) as len2 by (simpl;omega).
         assert((length (x ++ b[ "100"]) = 6)%nat) as len6. {
           rewrite app_length.
           simpl.
           rewrite (encode_reg_length rd); auto.
         }
         generalize (byte_and_C0 b["10"] (x++b["100"]) len2 len6).
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
        monadInv EQ0.
        exists(bB[ b["10"] ++ x ++ b["100"]]).
        split.
        ++++ simpl.
              replace 256 with (2^8).
              rewrite <- Z.shiftr_div_pow2.
              assert(length(b["00100"] ++ x1) = 8%nat) as len. {
                rewrite app_length.
                simpl.
                rewrite (encode_reg_length RSP);auto.
              }
              generalize (Z_shru_bits 8 (b["10"] ++ x ++ b["100"]) ( b["00100"] ++ x1) len).
              intros H.
              repeat rewrite <- app_assoc in H.
              simpl in H.
              setoid_rewrite H.
              auto.
              omega.
              simpl. unfold Z.pow_pos. simpl. auto.
        ++++ assert((length b["10"] <= 2)%nat) as len2 by (simpl;omega).
             assert((length (x ++ b[ "100"]) = 6)%nat) as len6. {
               rewrite app_length.
               simpl.
               rewrite (encode_reg_length rd);auto.
             }
             generalize (byte_and_C0 b["10"] (x++b["100"]) len2 len6).
             intros H11.
             simpl in *.
             rewrite H11.
             unfold not. intros H12. inversion H12.
      +++ simpl in EQ.
          monadInv EQ.
          monadInv EQ0.
          exists(bB[ b["10"] ++ x ++ x1]).
          split.
          ++++ simpl. auto.
          ++++ assert((length b["10"] <= 2)%nat) as len2 by (simpl;omega).
               assert((length (x ++ x1) = 6)%nat) as len6. {
                 rewrite app_length.
                 rewrite (encode_reg_length rd); auto.
                 rewrite (encode_reg_length i); auto.
               }
               generalize (byte_and_C0 b["10"] (x++x1) len2 len6).
               intros H11.
               simpl in *.
               rewrite H11.
               unfold not. intros H12. inversion H12.
  + destruct index.
    ++ unfold encode_addrmode in EQ.
       monadInv EQ.
       unfold encode_addrmode_aux in EQ0.
       destruct p.
       monadInv EQ0.
       destruct (ireg_eq i RSP) eqn:EQR; inversion EQ1.
       exists (bB[b[ "00"] ++ x ++ b[ "100"]]).
       split.
       +++ monadInv EQ1.
           simpl.
           replace 256 with (2^8).
           rewrite <- Z.shiftr_div_pow2.
      
           assert(length(encode_scale s ++ x1 ++  [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"] ) = 8%nat) as len. {
             repeat rewrite app_length.
             simpl.
             rewrite (encode_scale_length s).
             rewrite (encode_reg_length i);auto.
           }
           generalize (Z_shru_bits 8 (b["00"] ++ x ++ b["100"]) ( encode_scale s ++ x1 ++  [char_to_bool "1"; char_to_bool "0"; char_to_bool "1"]) len).
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
         assert ((length  (x++b["100"]) = 6)%nat) as len2. {
           rewrite app_length.
           simpl.
           rewrite (encode_reg_length rd).
           auto. auto.
         }
         generalize (byte_and_C0 b["00"] (x++b["100"]) len len2).
         intros H.
         unfold not.
         intros H11.
         rewrite H in H11.
         inversion H11.
    ++ unfold encode_addrmode in EQ.
       unfold encode_addrmode_aux in EQ.
       monadInv EQ.
       monadInv EQ0.
       exists (bB[ b[ "00"] ++ x ++ b[ "101"]]).
       simpl.
       split.
       +++ auto.
       +++
         assert((length b["00"] <=2)%nat) as len by (simpl; auto).
         assert ((length  (x++b["101"]) = 6)%nat) as len2. {
           rewrite app_length.
           simpl.
           rewrite (encode_reg_length rd).
           auto. auto.
         }
         generalize(byte_and_C0 b["00"] (x++b["101"]) len len2).
         intros H.
         unfold not.
         intros H10.
         simpl in H.
         rewrite H in H10.
         inversion H10.
Qed.



(** Reflexivity between the encoding and decoding of instructions*) 
Lemma encode_decode_refl : forall i bytes,
    fmc_instr_encode i = OK bytes
    -> forall l, exists i', fmc_instr_decode (bytes ++ l) = OK (i', l) /\ instr_eq i i'.
  intros i bytes H_encode l.
  unfold fmc_instr_encode in H_encode.
  destruct i.
  - (* Fjmp_l ofs *)
    exists (Fjmp_l  ofs). split.
    assert (H_tmp: bytes = HB["E9"]::(FlatBingen.encode_int32(Ptrofs.unsigned ofs))). {
      inversion H_encode.
      reflexivity.
    }
    unfold fmc_instr_decode.
    rewrite H_tmp.
    simpl.
    branch_byte_eq.
    ++ unfold decode_jmp_l.
       assert(H_de: (decode_int_n (FlatBingen.encode_int32 (Ptrofs.unsigned ofs) ++ l) 4)=Ptrofs.unsigned ofs). {
         apply (encode_decode_int32_same_prefix (Ptrofs.unsigned ofs) l).
         apply Ptrofs.unsigned_range.
       }
         rewrite -> H_de.
         generalize (remove_prefix_byte l ofs). intro H_lst.
            rewrite -> H_lst.
            assert(H_ptrofs: Ptrofs.repr (Ptrofs.unsigned ofs)=ofs). {
              apply Ptrofs.repr_unsigned.
            }
            rewrite -> H_ptrofs.
            reflexivity.
      ++ unfold instr_eq. auto.
  (* Fjcc cc ofs *)
  - exists (Fjcc c ofs). split.
    *
    unfold fmc_instr_decode.
    assert(H_nn: forall l,  bytes++l <> nil). {
      inversion H_encode.
      unfold encode_testcond.
      destruct c;
      intuition; inversion H.
    }
    destruct (bytes++l) eqn:EQ.
    + apply (H_nn l) in EQ. inversion EQ.
    + inversion H_encode.
      unfold encode_testcond in H_encode.
      destruct c eqn: H_cond.
      ++ assert(H_bytesEQ: [HB[ "0F"]; HB[ "84"]] ++ FlatBingen.encode_int32 (Ptrofs.unsigned ofs) = bytes). {
           inversion H_encode. reflexivity.
         }
         rewrite <- H_bytesEQ in EQ.
         assert(H_iEQ: i = HB["0F"]). {
           inversion EQ.
           reflexivity.
         }
         rewrite -> H_iEQ. simpl.
         branch_byte_eq.
         inversion EQ. unfold decode_0f. simpl.
         destruct ( Byte.eq_dec (Byte.repr 132) (Byte.repr 175)) eqn: EQb; inversion EQb.
         unfold decode_jcc. simpl.
         branch_byte_eq. simpl. rewrite (encode_decode_int32_same_prefix).
         rewrite (Ptrofs.repr_unsigned). f_equal. apply Ptrofs.unsigned_range.
        
      ++ rewrite <- H10 in EQ; inversion EQ. simpl.
         branch_byte_eq.
         inversion EQ. unfold decode_0f. simpl.
         destruct ( Byte.eq_dec (Byte.repr 133) (Byte.repr 175)) eqn: EQB3; inversion EQB3.
         simpl. unfold decode_jcc. simpl.
         branch_byte_eq.
         f_equal. f_equal. rewrite(encode_decode_int32_same_prefix).
         rewrite (Ptrofs.repr_unsigned). auto. apply Ptrofs.unsigned_range.
      ++  rewrite <- H10 in EQ; inversion EQ. simpl.
          branch_byte_eq.
          inversion EQ. unfold decode_0f. simpl.
          destruct ( Byte.eq_dec (Byte.repr 130) (Byte.repr 175)) eqn: EQB3; inversion EQB3.
          simpl. unfold decode_jcc. simpl.
          branch_byte_eq.
          f_equal. f_equal. rewrite(encode_decode_int32_same_prefix).
          rewrite (Ptrofs.repr_unsigned). auto. apply Ptrofs.unsigned_range.
      ++  rewrite <- H10 in EQ; inversion EQ. simpl.
          branch_byte_eq.
          inversion EQ. unfold decode_0f. simpl.
          destruct ( Byte.eq_dec (Byte.repr 134) (Byte.repr 175)) eqn: EQB3; inversion EQB3.
          simpl. unfold decode_jcc. simpl.
          branch_byte_eq.
          f_equal. f_equal. rewrite(encode_decode_int32_same_prefix).
          rewrite (Ptrofs.repr_unsigned). auto. apply Ptrofs.unsigned_range.
      ++  rewrite <- H10 in EQ; inversion EQ. simpl.
          branch_byte_eq.
          inversion EQ. unfold decode_0f. simpl.
          destruct ( Byte.eq_dec (Byte.repr 131) (Byte.repr 175)) eqn: EQB3; inversion EQB3.
          simpl. unfold decode_jcc. simpl.
          branch_byte_eq.
          f_equal. f_equal. rewrite(encode_decode_int32_same_prefix).
          rewrite (Ptrofs.repr_unsigned). auto. apply Ptrofs.unsigned_range.
      ++  rewrite <- H10 in EQ; inversion EQ. simpl.
          branch_byte_eq.
          inversion EQ. unfold decode_0f. simpl.
          destruct ( Byte.eq_dec (Byte.repr 135) (Byte.repr 175)) eqn: EQB3; inversion EQB3.
          simpl. unfold decode_jcc. simpl.
          branch_byte_eq.
          f_equal. f_equal. rewrite(encode_decode_int32_same_prefix).
          rewrite (Ptrofs.repr_unsigned). auto. apply Ptrofs.unsigned_range.
      ++ rewrite <- H10 in EQ; inversion EQ. simpl.
         branch_byte_eq.
         inversion EQ. unfold decode_0f. simpl.
         destruct ( Byte.eq_dec (Byte.repr 140) (Byte.repr 175)) eqn: EQB3; inversion EQB3.
         simpl. unfold decode_jcc. simpl.
         branch_byte_eq.
         f_equal. f_equal. rewrite(encode_decode_int32_same_prefix).
         rewrite (Ptrofs.repr_unsigned). auto. apply Ptrofs.unsigned_range.
      ++ rewrite <- H10 in EQ; inversion EQ. simpl.
         branch_byte_eq.
         inversion EQ. unfold decode_0f. simpl.
         destruct ( Byte.eq_dec (Byte.repr 142) (Byte.repr 175)) eqn: EQB3; inversion EQB3.
         simpl. unfold decode_jcc. simpl.
         branch_byte_eq.
         f_equal. f_equal. rewrite(encode_decode_int32_same_prefix).
         rewrite (Ptrofs.repr_unsigned). auto. apply Ptrofs.unsigned_range.
      ++ rewrite <- H10 in EQ; inversion EQ. simpl.
         branch_byte_eq.
         inversion EQ. unfold decode_0f. simpl.
         destruct ( Byte.eq_dec (Byte.repr 141) (Byte.repr 175)) eqn: EQB3; inversion EQB3.
         simpl. unfold decode_jcc. simpl.
         branch_byte_eq.
         f_equal. f_equal. rewrite(encode_decode_int32_same_prefix).
         rewrite (Ptrofs.repr_unsigned). auto. apply Ptrofs.unsigned_range.
      ++ rewrite <- H10 in EQ; inversion EQ. simpl.
         branch_byte_eq.
         inversion EQ. unfold decode_0f. simpl.
         destruct ( Byte.eq_dec (Byte.repr 143) (Byte.repr 175)) eqn: EQB3; inversion EQB3.
         simpl. unfold decode_jcc. simpl.
         branch_byte_eq.
         f_equal. f_equal. rewrite(encode_decode_int32_same_prefix).
         rewrite (Ptrofs.repr_unsigned). auto. apply Ptrofs.unsigned_range.
      ++ rewrite <- H10 in EQ; inversion EQ. simpl.
         branch_byte_eq.
         inversion EQ. unfold decode_0f. simpl.
         destruct ( Byte.eq_dec (Byte.repr 138) (Byte.repr 175)) eqn: EQB3; inversion EQB3.
         simpl. unfold decode_jcc. simpl.
         branch_byte_eq.
         f_equal. f_equal. rewrite(encode_decode_int32_same_prefix).
         rewrite (Ptrofs.repr_unsigned). auto. apply Ptrofs.unsigned_range.   
      ++ rewrite <- H10 in EQ; inversion EQ.
         branch_byte_eq.
         inversion EQ. unfold decode_0f. simpl.
         destruct ( Byte.eq_dec (Byte.repr 139) (Byte.repr 175)) eqn: EQB3; inversion EQB3.
         simpl. unfold decode_jcc. simpl.
         branch_byte_eq.
         f_equal.
         f_equal.
         rewrite(encode_decode_int32_same_prefix).
         rewrite (Ptrofs.repr_unsigned). auto. apply Ptrofs.unsigned_range.
      * unfold instr_eq. auto.
  (* Fshortcall ofs sg *)
  - exists (Fshortcall ofs (mksignature [] None (mkcallconv false false false))).
    split.
    * unfold fmc_instr_decode. monadInv H_encode. simpl.
      branch_byte_eq.
      unfold decode_shortcall. f_equal. f_equal. rewrite(encode_decode_int32_same_prefix).
      rewrite (Ptrofs.repr_unsigned). auto. apply Ptrofs.unsigned_range.
    * unfold instr_eq. auto.
  (* Fleal rd a *)
  - exists (Fleal rd a). split.
    * monadInv H_encode.
      simpl.      
      branch_byte_eq.
      unfold decode_leal.
      generalize (encode_decode_addrmode_refl _ _ _ l EQ).
      intro DC. rewrite DC. simpl. auto.
    * unfold instr_eq. auto.
  (* Fxorl_r rd *)
  - exists (Fxorl_r rd).
    (* replace (b[ "11"] ++ rdbits ++ rdbits )with(  (b[ "11"] ++ rdbits) ++ rdbits) in H_encode. *)
    split.
    * monadInv H_encode.
      simpl. branch_byte_eq. unfold decode_xorl_r.
      simpl.
      setoid_rewrite(and7 (b["11"] ++ x) x).
      rewrite (encode_parse_reg_refl rd x EQ).
      simpl.
      auto.
    + repeat rewrite app_length.
      simpl.
      repeat rewrite (encode_reg_length rd); auto.
    + rewrite (encode_reg_length rd); auto.
      * unfold instr_eq. auto.
  (* Faddl_ri rd n *)
  - exists(Faddl_ri rd n).
    split.
    +
      (* set (X:= b[ "11"] ++ b[ "000"] ++ rdbits) in H_encode. *)
      monadInv H_encode.
      unfold fmc_instr_decode.
      simpl.
      branch_byte_eq.
      unfold decode_81.
      simpl.
      rewrite <- Byte.and_shru.
      rewrite shru563.
      repeat fold (bits_to_Z  (b[ "11"] ++ b[ "000"])).
      assert(Byte.shru bB[ b[ "11"] ++ b[ "000"] ++ x ] (Byte.repr 3) = Byte.repr 24) as shruValue by admit.
      unfold bits_to_Z in shruValue.
      simpl in shruValue.
      rewrite shruValue.
      assert(Byte.and (Byte.repr 24) (Byte.repr 7) = Byte.repr 0). {
        unfold Byte.and. f_equal.
      }
      rewrite H.
      branch_byte_eq.
      unfold decode_addl_ri.
      simpl.
      assert(Byte.and  bB[ b[ "11"] ++ b[ "000"] ++ x ] (Byte.repr 7) = bB[x]) as regValue by admit.
      setoid_rewrite regValue.
      rewrite (encode_parse_reg_refl rd).
      simpl.
      generalize (encode_int32_size_Z (Int.unsigned n)).
      intros H10.
      assert(exists e1 e2 e3 e4, (encode_int32 (Int.unsigned n))=[e1;e2;e3;e4]). {
        generalize (list_len_gt1 _ (encode_int32 (Int.unsigned n)) 3 H10).
        intros (l' & t & H11).
        admit.
      }
      destruct H11 as (e1 & e2 & e3 & e4 & H12).
      rewrite H12.
      ++ repeat f_equal.
         rewrite <- H12.         
         rewrite (encode_decode_int32_same_prefix (Int.unsigned n) l).
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
    + unfold instr_eq. auto.
  (* Fsubl_ri rd n *)    
  - exists(Fsubl_ri rd n).
    (* (HB[ "81"] :: bB[ b[ "11"] ++ b[ "101"] ++ rdbits] :: encode_int32 (Int.unsigned n) *)
    split.
    + monadInv H_encode.
      unfold fmc_instr_decode. simpl.
      branch_byte_eq.
      unfold decode_81.
      simpl.
      rewrite <- Byte.and_shru.
      rewrite shru563.
      assert(Byte.shru (bB[b[ "11"] ++ b[ "101"] ++ x]) (Byte.repr 3) = (bB[b[ "11"] ++ b[ "101"]])) as shruValue by admit.
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
    + unfold instr_eq. auto.
  (* Fsubl_rr rd r1 *)
  - exists(Fsubl_rr rd r1).
    unfold fmc_instr_decode.
    (* [HB[ "2B"]; bB[ b[ "11"] ++ rdbits ++ r1bits]] *)
    simpl.
    split.
    + monadInv H_encode.
      simpl. 
      branch_byte_eq.
      unfold decode_subl_rr.
      simpl.
      rewrite <- Byte.and_shru.
      rewrite shru563.
      assert(Byte.shru  bB[ b[ "11"] ++ x ++ x0] (Byte.repr 3) =  bB[ b[ "11"] ++ x]) as shruValue by admit.
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
      rewrite (encode_reg_length r1); auto.
      rewrite (encode_reg_length r1); auto.
      auto.
      repeat rewrite app_length.
      simpl.
      rewrite (encode_reg_length rd); auto.
      rewrite (encode_reg_length rd); auto.
    + auto.
  (* Fmovl_ri rd n *)
  - exists(Fmovl_ri rd n).
    split.
    + unfold fmc_instr_decode.
      (*  (bB[ b[ "10111"] ++ rdbits] :: encode_int32 (Int.unsigned n)) *)
      monadInv H_encode.
      simpl.      
      branch_byte_eq'.
      assert (Byte.and bB[ b[ "10111"] ++ x] HB["F0"] =  HB["B0"]) as opcode. {
        
        setoid_rewrite (andf0 b["1011"] (b["1"]++x)).
        simpl. auto.
        admit. admit.
      }
      unfold bits_to_Z in opcode.
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
      apply Int.repr_unsigned.
      generalize (Int.unsigned_range n). intros H.
      unfold valid_int32.
      unfold Int.modulus in H.
      unfold two_power_nat in H.
      simpl in H.
      unfold two_power_pos.
      simpl. omega.
      repeat rewrite app_length.
      simpl.
      rewrite (encode_reg_length rd).
      auto. auto.
      rewrite (encode_reg_length rd);auto.
    + unfold instr_eq.
      auto.
  - exists (Fmov_rr rd r1).
    (* [HB[ "8B"]; bB[ b[ "11"] ++ rdbits ++ r1bits]] *)
    split.
    + monadInv H_encode.
      simpl.
      branch_byte_eq'.
      unfold decode_8b.
      simpl.
     
      assert(Byte.and  bB[ b[ "11"] ++ x ++ x0] HB["C0"] = HB["C0"]) as opValue. {
        rewrite byte_and_C0.
        simpl. auto. auto. rewrite app_length. rewrite (encode_reg_length rd),(encode_reg_length r1);auto.
      }
      unfold bits_to_Z in opValue.
      simpl in opValue.
      rewrite opValue.
      rewrite byte_eq_true.
      unfold decode_mov_rr.
      simpl.
      
      setoid_rewrite (decode_encode_rr_operand_refl b["11"] rd r1 x x0);auto.
    + unfold instr_eq. auto.
  - exists (Fmovl_rm rd a).
    split.
    + monadInv H_encode.
      simpl.
      branch_byte_eq'.
      unfold decode_8b.
      
      generalize (encode_addr_neq_c0 _ _ _ l EQ).
      intros (modrm & H1 & H2).
      inversion H1.
      simpl.
      rewrite H10.
      simpl.
      rewrite byte_eq_false.
      ++
        unfold decode_movl_rm.
        generalize (encode_decode_addrmode_refl _ _ _ l EQ).
        intros H.
        rewrite H.
        simpl.
        auto.
        
      ++ apply H2.         

    + simpl. auto.
  - exists (Fmovl_mr a rs).
    split.
    (* (HB[ "89"] :: abytes) *)
    + monadInv H_encode.
      simpl.
      branch_byte_eq'.
      unfold decode_movl_mr.
      simpl.
      generalize (encode_decode_addrmode_refl a rs x l EQ).
      intros H.
      rewrite H.
      simpl. auto.
    + unfold instr_eq.
      auto.
  - exists (Fmovl_rm rd a).
    split.
    + monadInv H_encode.
      simpl.
      branch_byte_eq'.
      unfold decode_8b.
      generalize(encode_addr_neq_c0 a rd x l EQ).
      intros (modrm & H & Hneq).
      rewrite H.
      simpl.
      rewrite byte_eq_false.
      ++ unfold decode_movl_rm.
         rewrite (encode_decode_addrmode_refl a rd).
         simpl. auto.
         auto.
      ++ apply Hneq.
    + unfold instr_eq.
      split; auto.
  - exists (Fmovl_mr a r1).
    split.
    + monadInv H_encode.
      unfold fmc_instr_decode.
      simpl.
      branch_byte_eq'.
      unfold decode_movl_mr.
      rewrite (encode_decode_addrmode_refl a r1).
      simpl. auto. auto.
    + simpl. auto.
  - exists (Ftestl_rr r2 r1).
    split.
    + monadInv H_encode.
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
    + simpl. auto.
  - exists (Fret).
    split.
    inversion H_encode.
    simpl.
    branch_byte_eq'.
    auto.
    simpl.
    auto.
  - exists (Fimull_rr rd r1).
    split.
    + monadInv H_encode.
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
    + simpl. auto.
  - exists (Fimull_ri rd n).
    split.
    + monadInv H_encode.
      simpl.
      branch_byte_eq'.
      unfold decode_imull_ri.
      simpl.      
      setoid_rewrite (and7 (b["11"]++x) x).
      rewrite (encode_parse_reg_refl rd).
      simpl.
      repeat f_equal.
      rewrite (encode_decode_int32_same_prefix (Int.unsigned n) l).
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
    + simpl. auto.
  - exists (Fcmpl_rr r1 r2).
    split.
    + monadInv H_encode.
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
    + simpl. auto.
  - exists (Fcmpl_ri r1 n).
    split.
    (* bB[ b[ "11"] ++ b[ "111"] ++ r1bits] :: encode_int32 (Int.unsigned n) *)
    + monadInv H_encode.
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
      rewrite (encode_reg_length r1).
      auto. auto.
      rewrite (encode_reg_length r1);auto.
    + simpl. auto.
  - exists(Fcltd).
    split.
    inversion H_encode.
    simpl. branch_byte_eq'.
    auto.
    simpl. auto.
  - exists (Fidivl r1).
    split.
    (*  bB[ b[ "11"] ++ b[ "110"] ++ r1bits] *)
    + monadInv H_encode.
      simpl. branch_byte_eq'.
      unfold decode_idivl.
      simpl.
      setoid_rewrite(and7 (b["11"]++b["110"]) x).
      rewrite (encode_parse_reg_refl r1).
      simpl.
      auto.
      auto.
      repeat rewrite app_length.
      simpl.
      rewrite(encode_reg_length r1);auto.
      rewrite(encode_reg_length r1);auto.
    + simpl. auto.
  - exists(Fsall_ri rd n).
    split.
    (* bB[ b[ "11"] ++ b[ "100"] ++ rdbits] *)
    + monadInv H_encode.
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
      
      admit.
      
      auto.
      
      repeat rewrite length_app. simpl.
      rewrite (encode_reg_length rd);auto.
      rewrite (encode_reg_length rd);auto.
    + simpl. auto.
  - exists (Fnop).
    inversion H_encode.
    split.
    + simpl. branch_byte_eq'.
      auto.
    + simpl. auto.            
      
  
Admitted.


(* Lemma encode_decode_same : forall i bytes,
    fmc_instr_encode i = OK bytes -> fmc_instr_decode bytes = OK i.
Proof.
  induction i.
  - intro bytes.
    unfold fmc_instr_encode.
    intro H.
    inversion H.
    unfold fmc_instr_decode.
    
    

Admitted. *)

(** * Decoder pass *)
Fixpoint transl_code_aux (n:nat) (c:FlatBinary.code_type) : res (list instr_with_info) :=
  match n with
  | O => Error (msg "Not enough fuel")
  | S n' =>
    match c with
    | nil => OK nil
    | _ =>
      do (i, c') <- fmc_instr_decode c;
      do ii <- transl_code_aux n' c';
      let sz := Ptrofs.repr (Z.of_nat (length c - length c')) in
      OK ((i,sz) :: ii)
    end
  end.

Fixpoint transl_code (c:FlatBinary.code_type) : res (list instr_with_info) :=
  transl_code_aux (length c + 1) c.

Set Printing All.
Definition transl_fun (f:FlatBinary.function) : res FlatAsm.function :=
  do code' <- transl_code (FlatProgram.fn_code f);
  OK (mkfunction (FlatProgram.fn_sig f) code' (fn_start f) (fn_size f)).

Definition transl_globdef (def: (ident * option FlatBinary.gdef))
  : res (ident * option FlatAsm.gdef) :=
  let '(id,def) := def in
  match def with
  | Some (AST.Gfun (Internal f)) =>
    do f' <- transl_fun f;
      OK (id, Some (AST.Gfun (Internal f')))
  | Some (AST.Gfun (External f)) => 
    OK (id, Some (AST.Gfun (External f)))
  | Some (AST.Gvar v) =>
    OK (id, Some (AST.Gvar v))
  | None => OK (id, None)
  end.

Fixpoint transl_globdefs defs :=
  match defs with
  | nil => OK nil
  | def::defs' =>
    do tdef <- transl_globdef def;
    do tdefs' <- transl_globdefs defs';
    OK (tdef :: tdefs')
  end.


(** Translation of a program *)
Definition transf_program (p:FlatBinary.program) : res FlatAsm.program := 
  do defs <- transl_globdefs (FlatProgram.prog_defs p);
  OK (Build_program
        defs
        (prog_public p)
        (prog_main p)
        (prog_main_ofs p)
        (prog_data_addr p)
        (prog_data_size p)
        (prog_code_addr p)
        (prog_code_size p))
      .
