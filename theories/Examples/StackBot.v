(** * The stack language on both faces

    [Examples.StackExample] gives the stack language a big-step semantics
    ([sexec]) and proves its encoding [senc] preserves terminating runs.
    This file completes the language:

    - [sdivS]: divergence, coinductive, in the same style as Imp's;
    - [senc_diverges]: the encoding preserves divergence;
    - [Stack] and [StackB]: the language on the top and bottom faces;
    - [senc_cvalid] and [senc_cvalid_bot]: every validity at all sixteen
      corners transfers between a stack program and its encoding;
    - [triangle_terminates]: the example program never diverges, stated
      for the stack language itself.

    All of it is axiom-free. *)

From Stdlib Require Import Arith Lia List.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Relational.
From LogicTransformers.Core Require Import Kernel KernelBot.
From LogicTransformers.Examples Require Import StackExample.
Import ListNotations.

CoInductive sdivS : scom -> stack -> Prop :=
  | D_SeqL : forall p q s, sdivS p s -> sdivS (SSeq p q) s
  | D_SeqR : forall p q s s1, sexec p s s1 -> sdivS q s1 -> sdivS (SSeq p q) s
  | D_LoopBody : forall p s, nz s -> sdivS p s -> sdivS (SLoop p) s
  | D_LoopIter : forall p s s1,
      nz s -> sexec p s s1 -> sdivS (SLoop p) s1 -> sdivS (SLoop p) s.

Notation kdivS := (kdiv sinstr_sem).

Lemma senc_diverges_1 : forall p s, sdivS p s -> kdivS (senc p) s.
Proof.
  induction p; intros s H; simpl.
  - inversion H.
  - inversion H; subst.
    + apply KD_SeqL, IHp1. assumption.
    + eapply KD_SeqR;
        [apply senc_correct; eassumption | apply IHp2; assumption].
  - apply KD_SeqL. revert s H. cofix G. intros s H. inversion H; subst.
    + apply KD_StarBody. eapply KD_SeqR; [apply KE_Assume; assumption |].
      apply IHp. assumption.
    + eapply KD_StarIter.
      * eapply KE_Seq; [apply KE_Assume; eassumption |].
        apply senc_correct. eassumption.
      * apply G. assumption.
Qed.

Lemma senc_diverges_2 : forall p s, kdivS (senc p) s -> sdivS p s.
Proof.
  induction p; intros s H; simpl in H.
  - inversion H.
  - inversion H; subst.
    + apply D_SeqL, IHp1. assumption.
    + eapply D_SeqR; [apply senc_correct; eassumption | apply IHp2; assumption].
  - inversion H; subst;
      [| match goal with H' : kdivS (KAssume _) _ |- _ => inversion H' end].
    match goal with
    | H' : kdivS (KStar _) _ |- _ => clear H; rename H' into H
    end.
    revert s H. cofix G. intros s H. inversion H; subst.
    + match goal with H' : kdivS (KSeq _ _) _ |- _ => inversion H'; subst end;
        [match goal with H' : kdivS (KAssume _) _ |- _ => inversion H' end |].
      match goal with H' : kev sinstr_sem (KAssume _) _ _ |- _ =>
        inversion H'; subst end.
      apply D_LoopBody; [assumption | apply IHp; assumption].
    + match goal with H' : kev sinstr_sem (KSeq _ _) _ _ |- _ =>
        inversion H'; subst end.
      match goal with H' : kev sinstr_sem (KAssume _) _ _ |- _ =>
        inversion H'; subst end.
      eapply D_LoopIter; [assumption | apply senc_correct; eassumption |].
      apply G. assumption.
Qed.

Theorem senc_diverges : forall p s, sdivS p s <-> kdivS (senc p) s.
Proof. split; [apply senc_diverges_1 | apply senc_diverges_2]. Qed.

(** ** The language on both faces, and validity transfer *)

Definition Stack : Language := mkLanguage scom stack sexec.

Definition semBS (p : scom) (o o' : option stack) : Prop :=
  match o, o' with
  | None, None => True
  | None, Some _ => False
  | Some s, Some s' => sexec p s s'
  | Some s, None => sdivS p s
  end.

Definition StackB : Language := mkLanguage scom (option stack) semBS.

Theorem senc_cvalid : forall d pl a (P Q : stack -> Prop) p,
    cvalid d pl a (@mkTriple Stack P p Q) <->
    cvalid d pl a (@mkTriple (KLang sinstr_sem) P (senc p) Q).
Proof.
  intros d pl a P Q p. rewrite !cvalid_cvr. simpl.
  split; apply cvr_transfer; intros s s'; rewrite senc_correct; tauto.
Qed.

Theorem senc_cvalid_bot : forall d pl a (P Q : option stack -> Prop) p,
    cvalid d pl a (@mkTriple StackB P p Q) <->
    cvalid d pl a (@mkTriple (KLangB sinstr_sem) P (senc p) Q).
Proof.
  intros d pl a P Q p. rewrite !cvalid_cvr. simpl.
  assert (E : forall o o', semBS p o o' <-> semKB sinstr_sem (senc p) o o').
  { intros [s|] [s'|]; simpl;
      [apply senc_correct | apply senc_diverges | tauto | tauto]. }
  split; apply cvr_transfer; intros o o'; rewrite E; tauto.
Qed.

(** The triangle program never diverges, in the stack language itself. *)
Corollary triangle_terminates : forall s, ~ sdivS triangle s.
Proof.
  intros s H. apply senc_diverges in H. exact (triangle_no_div s H).
Qed.
