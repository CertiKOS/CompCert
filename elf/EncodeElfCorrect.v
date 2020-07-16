Require Import ElfBytesSemantics.
Require Import Smallstep.
Require Import EncodeRelocElf DecodeRelocElf.
Require Import RelocElf.
Require Import Coqlib Errors.

Require Import Linking.
Require Import RelocElfgenproof.


Definition match_prog : elf_file -> (list Integers.Byte.int * Asm.program * Globalenvs.Senv.t) -> Prop :=
  fun p p' => encode_elf_file p = OK p'.

Section PRES.

Variable prog: elf_file.
Variable tprog_bytes: list Integers.Byte.int.
Variable tprog_prog: Asm.program.
Variable tprog_senv: Globalenvs.Senv.t.

Hypothesis TRANSF: match_prog prog (tprog_bytes, tprog_prog, tprog_senv).

Context `{external_calls_prf: Events.ExternalCalls}.

Lemma encode_elf_correct:
  forall rs, forward_simulation (RelocElfSemantics.semantics prog rs)
                                (ElfBytesSemantics.semantics tprog_bytes tprog_prog tprog_senv rs).
Proof.
  unfold match_prog in TRANSF.
  unfold ElfBytesSemantics.semantics. intros.
  erewrite decode_encode_elf_file; eauto.
  apply forward_simulation_step with (match_states := eq); intuition subst; eauto.
Qed.

End PRES.

Definition link (p1 p2: list Integers.Byte.int * Asm.program * Globalenvs.Senv.t) :=
  let '(b1, p1, s1) := p1 in let '(b2, p2, s2) := p2 in
  match decode_elf_file b1 p1 s1, decode_elf_file b2 p2 s2 with
  | OK e1, OK e2 =>
    match link_reloc_elf_gen e1 e2 with
    | Some e =>
      match encode_elf_file e with
        OK r => Some r
      | _ => None
      end
    | None => None
    end
  | _, _ => None
  end.

Instance linker : Linker (list Integers.Byte.int * Asm.program * Globalenvs.Senv.t).
Proof.
  eapply Build_Linker with (link := link) (linkorder := fun _ _ => True).
  auto. auto. auto.
Defined.

(***** Remove Proofs By Chris Start ******)
(* Instance tl : Linking.TransfLink match_prog.
Proof.
  red. simpl.
  unfold match_prog.
  intros.
  unfold link. repeat (destr; [idtac]).
  erewrite decode_encode_elf_file. 2: eauto.
  erewrite decode_encode_elf_file. 2: eauto. rewrite H.
  cut (exists tp, encode_elf_file p = OK tp).
  intros (tp & ENC). rewrite ENC; eauto. subst.
  unfold encode_elf_file in *. autoinv.
  rewrite pred_dec_true. eauto.
  unfold link_reloc_elf_gen in H. autoinv.
  unfold TablesEncodeproof.link_reloc_decode_tables in Heqo. autoinv.
  unfold TablesEncode.transf_program in Heqr2. autoinv.
  eapply RelocElfgen.gen_reloc_elf_valid; eauto.
  simpl. rewrite in_app. right. simpl. auto.
  rewrite TablesEncode.dump_reloctables_error in H0; congruence.
Defined. *)
(***** Remove Proofs By Chris End ******)

