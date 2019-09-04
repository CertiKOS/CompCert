Require Import String Coqlib Maps.
Require Import AST Integers Floats Values Memory Events Smallstep.
Require Import Locations Stacklayout Conventions EraseArgs.
Require Import Num.
Require Import SegAsm Asm FlatProgram.
Require Globalenvs.

Require Import Globalenvs Smallstep.



Inductive scale : Type :=
| Scale1 | Scale2 | Scale4 | Scale8.

Inductive addrmode: Type :=
| Addrmode (base: option ireg)
           (index: option (ireg * scale))
           (disp: ptrofs).
            
Inductive instruction : Type :=
  | Fjmp_l (ofs: ptrofs)
  | Fjcc (c: testcond) (ofs: ptrofs)
  | Fshortcall (ofs: ptrofs) (sg: signature) 
  | Fleal (rd: ireg) (a:addrmode)
  | Fxorl_r (rd: ireg)
  | Faddl_ri (rd: ireg) (n:int)
  | Fsubl_ri (rd: ireg) (n:int)
  | Fsubl_rr (rd r1: ireg)
  | Fmovl_ri (rd: ireg) (n:int)
  | Fmov_rr (rd r1: ireg)
  | Fmovl_rm (rd: ireg) (a: addrmode)
  | Fmovl_mr (a: addrmode) (rs: ireg)
  | Fmov_rm_a (rd: ireg) (a: addrmode)
  | Fmov_mr_a (a: addrmode) (r1: ireg)
  | Ftestl_rr (r1 r2: ireg)
  | Fret
  | Fimull_rr (rd r1: ireg)
  | Fimull_ri (rd: ireg) (n: int)
  | Fcmpl_rr (r1 r2: ireg)
  | Fcmpl_ri (r1:ireg) (n:int)
  | Fcltd
  | Fidivl (r1: ireg)
  | Fsall_ri (rd:ireg) (n:int)
  | Fnop.

Definition instr_with_info: Type := instruction * ptrofs.
Definition code_type := list instr_with_info.
Definition function := @FlatProgram.function code_type.
Definition gdef := @FlatProgram.gdef code_type data_info.

(* The Flat Machine Code Program *)
Definition program := @FlatProgram.program code_type data_info.

Open Scope asm.


Definition addrmode_size_aux (a:addrmode) : Z :=
  let '(Addrmode base ofs const) := a in
  match ofs, base with
  | None, None => 1
  | None, Some rb =>
    if ireg_eq rb RSP then 2 else 1
  | Some _, _ => 2
  end.

Lemma addrmode_size_aux_pos: forall a, addrmode_size_aux a > 0.
Proof.
  intros. unfold addrmode_size_aux. destruct a.
  destruct index. omega. destruct base.
  destr; omega. omega.
Qed.

Lemma addrmode_size_aux_upper_bound: forall a, addrmode_size_aux a <= 2.
Proof.
  intros. destruct a. simpl.
  destruct index; try omega.
  destruct base; try omega.
  destr; omega.
Qed.

Definition addrmode_size (a:addrmode) : Z :=
  addrmode_size_aux a + 4.


Definition instr_size (i: instruction) : Z :=
  match i with
  | Fjmp_l _ => 5
  | Fjcc _ _ => 6
  | Fshortcall _ _ => 5
  | Fleal _ a => 1 + addrmode_size a
  | Fxorl_r _ => 2
  | Faddl_ri _ _=> 6
  | Fsubl_ri _ _=> 6
  | Fsubl_rr _ _=> 2
  | Fmovl_ri _ _=> 5
  | Fmov_rr _ _=> 2
  | Fmovl_rm _ a=> 1 + addrmode_size a
  | Fmovl_mr a _ => 1 + addrmode_size a
  | Fmov_rm_a _ a => 1 + addrmode_size a
  | Fmov_mr_a a _ => 1 + addrmode_size a
  | Ftestl_rr _ _ => 2
  | Fret => 1
  | Fimull_rr _ _ => 3
  | Fimull_ri _ _=> 6
  | Fcmpl_rr _ _ => 2
  | Fcmpl_ri _ _ => 6
  | Fcltd => 1
  | Fidivl _ => 2
  | Fsall_ri _ _ => 6
  | Fnop => 1
  end.

Definition scale_to_Z (s:scale):Z :=
  match s with
  |Scale1 => 1
  |Scale2 => 2
  |Scale4 => 4
  |Scale8 => 8
  end.
             

Definition eval_addrmode (a: addrmode) (rs: regset) : val :=
  let '(Addrmode base ss ofs) := a in
  Val.add  (match base with
             | None => Vint Int.zero
             | Some r => rs r
            end)
  (Val.add  (Vint (Int.repr( Ptrofs.unsigned ofs))) (* TBD *)
            (match ss with
             | None => Vint Int.zero
             | Some (idx, scale) =>
               Val.mul (rs idx) (Vint (Int.repr (scale_to_Z scale)))
             end
            )).

Section WITHEXTERNALCALLS.
  Context `{external_calls_prf: ExternalCalls}.

  Definition eval_testcond (c: testcond) (rs: regset) : option bool :=
    match c with
    | Cond_e =>
      match rs ZF with
      | Vint n => Some (Int.eq n Int.one)
      | _ => None
      end
    | Cond_ne =>
      match rs ZF with
      | Vint n => Some (Int.eq n Int.zero)
      | _ => None
      end
    | Cond_b =>
      match rs CF with
      | Vint n => Some (Int.eq n Int.one)
      | _ => None
      end
    | Cond_be =>
      match rs CF, rs ZF with
      | Vint c, Vint z => Some (Int.eq c Int.one || Int.eq z Int.one)
      | _, _ => None
      end
    | Cond_ae =>
      match rs CF with
      | Vint n => Some (Int.eq n Int.zero)
      | _ => None
      end
    | Cond_a =>
      match rs CF, rs ZF with
      | Vint c, Vint z => Some (Int.eq c Int.zero && Int.eq z Int.zero)
      | _, _ => None
      end
    | Cond_l =>
      match rs OF, rs SF with
      | Vint o, Vint s => Some (Int.eq (Int.xor o s) Int.one)
      | _, _ => None
      end
    | Cond_le =>
      match rs OF, rs SF, rs ZF with
      | Vint o, Vint s, Vint z => Some (Int.eq (Int.xor o s) Int.one || Int.eq z Int.one)
      | _, _, _ => None
      end
    | Cond_ge =>
      match rs OF, rs SF with
      | Vint o, Vint s => Some (Int.eq (Int.xor o s) Int.zero)
      | _, _ => None
      end
    | Cond_g =>
      match rs OF, rs SF, rs ZF with
      | Vint o, Vint s, Vint z => Some (Int.eq (Int.xor o s) Int.zero && Int.eq z Int.zero)
      | _, _, _ => None
      end
    | Cond_p =>
      match rs PF with
      | Vint n => Some (Int.eq n Int.one)
      | _ => None
      end
    | Cond_np =>
      match rs PF with
      | Vint n => Some (Int.eq n Int.zero)
      | _ => None
      end
    end.

  Definition exec_instr {exec_load exec_store} `{!MemAccessors exec_load exec_store}
             (i: instruction) (rs: regset) (m: mem): outcome:=
    let sz :=Ptrofs.repr (instr_size i) in 
    match i with
    | Fjmp_l ofs =>                                                      (* TBD *)
      Next (nextinstr (rs#PC <- (Val.add (rs#PC)  (Vint (Int.repr (Ptrofs.unsigned ofs))))) sz) m
    | Fjcc c ofs =>
      match eval_testcond c rs with
      |Some b =>
       if b then
         Next (nextinstr (rs#PC <- (Val.add (rs#PC)  (Vint (Int.repr (Ptrofs.unsigned ofs))))) sz) m
       else
         Next (nextinstr rs sz) m 
      |None => Stuck
      end
    | Fshortcall ofs sg =>
      Next (nextinstr (rs#PC <- (Val.add (rs#PC)  (Vint (Int.repr (Ptrofs.unsigned ofs))))) sz) m
    | Fleal rd a =>
      Next (nextinstr (rs # rd <- (eval_addrmode a rs)) sz) m   
    | Fxorl_r rd =>
      Next (nextinstr (rs # rd <- Vzero) sz) m   
    | Faddl_ri rd n =>
      Next (nextinstr (rs # rd <- (Val.add (rs rd) (Vint n))) sz) m
    | Fsubl_ri rd n =>
      Next (nextinstr (rs # rd <- (Val.sub (rs rd) (Vint n))) sz) m
    | Fsubl_rr rd r1 =>
      Next (nextinstr (rs # rd <- (Val.sub (rs rd) (rs r1))) sz) m
    | Fmovl_ri rd n =>
      Next (nextinstr (rs # rd <- (Vint n)) sz) m               
    | Fmov_rr rd r1 =>
      Next (nextinstr (rs # rd <- (rs r1)) sz ) m
    (* | Fmovl_rm (rd: ireg) (a: addrmode) *)
    (* | Fmovl_mr (a: addrmode) (rs: ireg) *)
    (* | Fmov_rm_a (rd: ireg) (a: addrmode) *)
    (* | Fmov_mr_a (a: addrmode) (r1: ireg) *)
    | Ftestl_rr r1 r2 =>
      Next (nextinstr (compare_ints (Val.and (rs r1) (rs r2)) Vzero rs m) sz) m
    (* | Fret *)
    | Fimull_rr rd r1 =>
      Next (nextinstr (rs # rd <- (Val.mul (rs rd) (rs r1))) sz) m
    | Fimull_ri rd n =>
      Next (nextinstr (rs # rd <- (Val.mul (rs rd) (Vint n))) sz) m
    | Fcmpl_rr r1 r2 =>
      Next (nextinstr (compare_ints (rs r1) (rs r2) rs m) sz) m
    | Fcmpl_ri r1 n =>
      Next (nextinstr (compare_ints (rs r1) (Vint n) rs m) sz) m
    | Fcltd =>
      Next (nextinstr (rs#RDX <- (Val.shr rs#RAX (Vint (Int.repr 31)))) sz) m
    | Fidivl r1  =>
      match rs#RDX, rs#RAX, rs#r1 with
      | Vint nh, Vint nl, Vint d =>
          match Int.divmodu2 nh nl d with
          | Some(q, r) => Next (nextinstr_nf (rs#RAX <- (Vint q) #RDX <- (Vint r)) sz) m
          | None => Stuck
          end
      | _, _, _ => Stuck
      end
    | Fsall_ri rd n =>
      Next (nextinstr (rs # rd <- (Val.shl (rs rd) (Vint n))) sz) m
    | Fnop =>
      Next (nextinstr rs  sz) m
    | _ => Stuck
    end.
