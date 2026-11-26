(** * Negation is outside the cube

    Cousot (2024): "incorrectness logic is not Hoare incorrectness
    logic. It is sufficient but not necessary." The falsity of a Hoare
    triple is not an incorrectness triple. His counterexample, for
    [x := 0] from [true]:

    - the Hoare triple [{true} x := 0 {x ≠ 0 ∧ x ≠ 1}] is false
      ([hoare_false]), so Hoare incorrectness holds;
    - but the incorrectness triple with the complementary postcondition,
      [[true] x := 0 [x = 0 ∨ x = 1]], is not valid either
      ([il_false]): [x = 1] is never reached.

    So "the Hoare triple fails" is not the IL triple one might read off
    it ([negation_not_il]). Constructive. *)

From Stdlib Require Import String.
From LogicTransformers.Imp Require Import Syntax BigStep Lang.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Relational.

Local Open Scope string_scope.
Local Notation X := "x".

Definition zero : com := CAsgn X (ANum 0).

Lemma hoare_false :
  ~ cvalid Forward Plain Over
      (@mkTriple Imp (fun _ => True) zero (fun s => s X <> 0 /\ s X <> 1)).
Proof.
  rewrite cvalid_cvr. simpl. intros H.
  destruct (H empty_state (update empty_state X 0) I (E_Asgn _ _ _)) as [H0 _].
  apply H0. apply update_eq.
Qed.

Lemma il_false :
  ~ cvalid Forward Plain Under
      (@mkTriple Imp (fun _ => True) zero (fun s => s X = 0 \/ s X = 1)).
Proof.
  rewrite cvalid_cvr. simpl. intros H.
  destruct (H (update empty_state X 1) (or_intror (update_eq _ _ _)))
    as [s [_ Hc]].
  inversion Hc; subst.
  match goal with E : update _ _ _ = update _ _ _ |- _ =>
    apply (f_equal (fun st => st X)) in E; rewrite !update_eq in E end.
  discriminate.
Qed.

Theorem negation_not_il : exists (P : state -> Prop) c (Q : state -> Prop),
    ~ cvalid Forward Plain Over (@mkTriple Imp P c Q) /\
    ~ cvalid Forward Plain Under
        (@mkTriple Imp P c (fun s => ~ Q s)).
Proof.
  exists (fun _ => True), zero, (fun s => s X <> 0 /\ s X <> 1).
  split; [exact hoare_false |].
  intros H. apply il_false. rewrite cvalid_cvr in *. simpl in *.
  intros s' Hs. apply H. intros [H0 H1]. destruct Hs; contradiction.
Qed.
