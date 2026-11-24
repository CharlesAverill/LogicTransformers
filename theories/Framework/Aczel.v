(** * Aczel's correspondence between rules and fixpoints

    Cousot designs proof systems by calculating a logic's theory as a
    least fixpoint and then reading off rules with Aczel's correspondence
    (Aczel 1977; Cousot POPL'24 §II.5). For a deductive system [R] on a
    universe [U]:

    - its proof-theoretic meaning is the inductive closure [deriv R];
    - its model-theoretic meaning is [lfp] of the consequence operator
      [conseq R X = {c | ∃ P ⊆ X. (P, c) ∈ R}].

    [aczel_rules_lfp]: they coincide. [aczel_op_lfp]: conversely, any
    monotone [F] is the consequence operator of the rules [{P/c | c ∈ F P}],
    so [lfp F] is exactly what those rules derive. Premise sets may be
    infinite (transfinite proofs). Constructive. *)

From Stdlib Require Import Setoid.
From LogicTransformers.Framework Require Import Fixpoints.

Section Aczel.

Context {U : Type}.

Definition rules := (U -> Prop) -> U -> Prop.

Inductive deriv (R : rules) : U -> Prop :=
  | deriv_rule : forall ps c,
      R ps c -> (forall t, ps t -> deriv R t) -> deriv R c.

Definition conseq (R : rules) (X : @pset U) : @pset U :=
  fun c => exists ps, R ps c /\ sub ps X.

Lemma conseq_monotone : forall R, monotone (conseq R).
Proof.
  intros R X Y HXY c [ps [HR Hps]]. exists ps. split; [exact HR |].
  intros t Ht. apply HXY, Hps, Ht.
Qed.

Theorem aczel_rules_lfp : forall R c, deriv R c <-> lfp (conseq R) c.
Proof.
  intros R c. split.
  - intros D. induction D as [ps c HR Hps IH].
    apply lfp_prefix; [apply conseq_monotone |].
    exists ps. split; [exact HR | exact IH].
  - revert c. apply lfp_least.
    intros c [ps [HR Hps]]. apply (deriv_rule R ps c HR Hps).
Qed.

(** The rules of an operator: [c] follows from [P] whenever [c ∈ F P]. *)
Definition aczel (F : @pset U -> @pset U) : rules := fun ps c => F ps c.

Theorem aczel_op_lfp : forall F, monotone F ->
    forall c, deriv (aczel F) c <-> lfp F c.
Proof.
  intros F HF c. rewrite aczel_rules_lfp. split.
  - revert c. apply lfp_least. intros c [ps [HR Hps]].
    apply lfp_prefix; [exact HF |]. apply (HF ps); [| exact HR].
    intros t Ht. apply Hps, Ht.
  - revert c. apply lfp_least. intros c Hc.
    apply lfp_prefix; [apply conseq_monotone |].
    exists (lfp (conseq (aczel F))). split; [exact Hc | intros t Ht; exact Ht].
Qed.

End Aczel.
