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
    decode_imull_rr (sublist mc 1)
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
      OK(Faddl_ri rd (Int.repr n), remove_first_n mc 5).
  
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
     OK(Fcmpl_rr (fst rds) (snd rds), remove_first_n mc 1).

Definition decode_idivl  (mc: list byte): res(FlatAsm.instruction * list byte):=
  do modrm <- get_n mc 0;
    do rd <- addrmode_parse_reg (Byte.and modrm HB["7"]);
    OK(Fidivl rd, remove_first_n mc 1).

Definition decode_sall_ri (mc: list byte): res(FlatAsm.instruction * list byte):=
  do modrm <- get_n mc 0;
     do rd <- addrmode_parse_reg (Byte.and modrm HB["7"]);
      let n := decode_int_n (remove_first_n mc 1) 4 in
      OK(Fsall_ri rd (Int.repr n), remove_first_n mc 5).

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
              else Error(msg "Unknown opcode!")
    end.

Check Fjcc = Fjcc.


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

Ltac reg_eq reg :=
  match goal with
    | [|-  (exists reg1 : ireg, addrmode_parse_reg bB[ _] = OK reg1 /\ reg1 = reg)  ] =>
      intros;inversion H; unfold addrmode_parse_reg; exists reg; split; branch_byte_eq; auto
  end.

Lemma encode_decode_ireg_refl: forall reg l,
    encode_ireg reg = OK l ->
    exists reg1,  addrmode_parse_reg bB[l] = OK reg1 /\ reg1 = reg.
Proof.
  intros. subst. unfold encode_ireg in H.
  case reg eqn:EQR.
  - branch_byte_eq RAX. intros. inversion H. unfold addrmode_parse_reg. exists RAX. split.
    + branch_byte_eq. auto. + auto.
                              


(** Reflexivity between the encoding and decoding of addressing modes *) 
Lemma encode_decode_addrmode_refl: forall a rd x l,
    encode_addrmode a rd = OK x ->
    decode_addrmode (x ++ l) = OK (rd, a, l).
Proof.
  intros. subst. unfold encode_addrmode in H. destruct a eqn:EQA in H.
  monadInv H.
  unfold decode_addrmode.

  unfold encode_addrmode_aux in EQ. monadInv EQ.
  destruct index eqn:EQ_index in EQ1. destruct p eqn:EQp in EQ1.
  destruct base eqn:EQ_base in EQ1. monadInv EQ1.
  - simpl.
 Admitted.

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
      
      
                  
(*                   
                  assert (Hl0 = [HB["84"]]++FlatBingen.encode_int32(Ptrofs.unsigned ofs)) ++ l).
        
         
    induction ((encode_testcond c ++ FlatBingen.encode_int32 (Ptrofs.unsigned ofs)) ++ l).
    + admit.
    + simpl.
    inversion H_encode. *)

    
    
    
            
    

  
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

