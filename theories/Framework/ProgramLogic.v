(** * Program logics

    A program logic over a language consists of

    - a semantic notion of validity for triples, and
    - a proof system, given as data: a set of rule instances
      [(premises, conclusion)]. Premises form a set, possibly infinite,
      so rules like the iteration-indexed loop rule with one premise per
      [n] can be expressed.

    Derivability is the inductive closure of the rules, plus one
    structural rule shared by every logic: triples whose assertions are
    pointwise equivalent are interchangeable. Every logic in the cube
    respects this rule, since validity only depends on assertions as sets
    of states.

    Because rules are data, a transformer can act on a proof system rule
    by rule. It is not limited to rewriting the validity predicate. *)

From LogicTransformers.Framework Require Import Language.

Section ProgramLogic.

Context {L : Language}.

Definition assertion := lstate L -> Prop.

Definition aimpl (P Q : assertion) : Prop := forall s, P s -> Q s.
Definition aequiv (P Q : assertion) : Prop := forall s, P s <-> Q s.

Record triple := mkTriple {
  pre : assertion;
  cmd : prog L;
  post : assertion
}.

Definition triple_equiv (t1 t2 : triple) : Prop :=
  aequiv (pre t1) (pre t2) /\ cmd t1 = cmd t2 /\ aequiv (post t1) (post t2).

Lemma triple_equiv_refl : forall t, triple_equiv t t.
Proof. intros t. repeat split; auto. Qed.

Lemma triple_equiv_sym : forall t1 t2,
    triple_equiv t1 t2 -> triple_equiv t2 t1.
Proof.
  intros t1 t2 [HP [Hc HQ]].
  repeat split; auto; try apply HP; try apply HQ.
Qed.

Lemma triple_equiv_trans : forall t1 t2 t3,
    triple_equiv t1 t2 -> triple_equiv t2 t3 -> triple_equiv t1 t3.
Proof.
  intros t1 t2 t3 [HP1 [Hc1 HQ1]] [HP2 [Hc2 HQ2]].
  repeat split; try congruence;
    try (intros H; apply HP2, HP1, H);
    try (intros H; apply HP1, HP2, H);
    try (intros H; apply HQ2, HQ1, H);
    try (intros H; apply HQ1, HQ2, H).
Qed.

(** A rule set: which [(premises, conclusion)] pairs are rule instances.
    Side conditions such as the implications in the consequence rule
    belong to the rule instance. *)
Definition ruleset := (triple -> Prop) -> triple -> Prop.

Inductive derivable (R : ruleset) : triple -> Prop :=
  | D_Rule : forall ps c,
      R ps c ->
      (forall t, ps t -> derivable R t) ->
      derivable R c
  | D_Equiv : forall t t',
      derivable R t ->
      triple_equiv t t' ->
      derivable R t'.

Lemma derivable_mono : forall (R1 R2 : ruleset),
    (forall ps c, R1 ps c -> R2 ps c) ->
    forall t, derivable R1 t -> derivable R2 t.
Proof.
  intros R1 R2 Hsub t D.
  induction D.
  - eapply D_Rule; eauto.
  - eapply D_Equiv; eauto.
Qed.

Definition proper_validity (V : triple -> Prop) : Prop :=
  forall t t', triple_equiv t t' -> V t -> V t'.

Record ProgramLogic := mkLogic {
  valid : triple -> Prop;
  valid_proper : proper_validity valid;
  rules : ruleset
}.

Definition sound (Lg : ProgramLogic) : Prop :=
  forall t, derivable (rules Lg) t -> valid Lg t.

Definition complete (Lg : ProgramLogic) : Prop :=
  forall t, valid Lg t -> derivable (rules Lg) t.

(** Local soundness: every rule preserves validity. This is stronger
    than soundness and is the property that transformers carry over. *)
Definition locally_sound (Lg : ProgramLogic) : Prop :=
  forall ps c,
    rules Lg ps c -> (forall t, ps t -> valid Lg t) -> valid Lg c.

Theorem locally_sound_sound : forall Lg, locally_sound Lg -> sound Lg.
Proof.
  intros Lg HS t D.
  induction D.
  - eapply HS; eauto.
  - eapply valid_proper; eauto.
Qed.

End ProgramLogic.

Arguments assertion L : clear implicits.
Arguments triple L : clear implicits.
Arguments ruleset L : clear implicits.
Arguments ProgramLogic L : clear implicits.
