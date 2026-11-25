(** * Cousot's definitions, by abstraction

    Cousot (POPL 2024) defines each logic's theory in two abstraction
    steps:
    1. the semantics, a relation [R], is abstracted to a predicate
       transformer: [post R] (image), [pre R] (preimage), or their
       complement duals [p̃ost R = ¬ ∘ post R ∘ ¬] and
       [p̃re R = ¬ ∘ pre R ∘ ¬];
    2. the transformer [f] is abstracted to the set of pairs [⟨P, Q⟩]
       with [f P ⊆ Q] or [Q ⊆ f P] (forward), [f Q ⊆ P] or [P ⊆ f Q]
       (backward).

    This file states those definitions as he gives them ([apost],
    [apre], [adpost], [adpre], [transformer], [theory]), and proves:
    - [galois_post]: [post] is the lower adjoint of a Galois connection
      between relations and monotone transformers, with upper adjoint
      [gpost f = {⟨s, s'⟩ | s' ∈ f {s}}]; [gpost_apost]: the
      abstraction loses nothing, since [gpost (post R) = R];
    - [theory_iff_cvr]: the theory at every corner is exactly this
      project's validity [cvr], and so [cvalid_iff_theory] for any
      language. This replaces the earlier "by inspection" link with
      Cousot's definitions;
    - the commutation equations his calculational design reads rules
      from: [post] maps composition to composition ([apost_comp]), union
      to union ([apost_union]), and reflexive-transitive closure to the
      union of iterates ([apost_rtc]); [pre] likewise, reversed.
      [Core.Calculational] specializes them to the core language's
      constructs, which are the equations behind [Core.Generate].

    The dual transformers are defined with negation, as Cousot does, so
    relating them to [cvr] uses [classic]. Everything else is
    constructive. *)

From Stdlib Require Import Classical.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Relational.

Section Abstraction.

Context {St : Type}.

Definition rel := St -> St -> Prop.
Definition pred := St -> Prop.

Definition sub (P Q : pred) : Prop := forall s, P s -> Q s.
Definition peq (P Q : pred) : Prop := forall s, P s <-> Q s.
Definition neg (P : pred) : pred := fun s => ~ P s.

(** ** Step 1: from relations to transformers *)

Definition apost (R : rel) (P : pred) : pred :=
  fun s' => exists s, P s /\ R s s'.
Definition apre (R : rel) (Q : pred) : pred :=
  fun s => exists s', R s s' /\ Q s'.
Definition adpost (R : rel) (P : pred) : pred := neg (apost R (neg P)).
Definition adpre (R : rel) (Q : pred) : pred := neg (apre R (neg Q)).

Definition mono_tr (f : pred -> pred) : Prop :=
  forall P P', sub P P' -> sub (f P) (f P').

Definition gpost (f : pred -> pred) : rel :=
  fun s s' => f (fun x => x = s) s'.

Theorem galois_post : forall (R : rel) (f : pred -> pred), mono_tr f ->
    (forall P, sub (apost R P) (f P)) <->
    (forall s s', R s s' -> gpost f s s').
Proof.
  intros R f Hm. split.
  - intros H s s' Hr. apply H. exists s. split; [reflexivity | exact Hr].
  - intros H P s' [s [HP Hr]].
    apply (Hm (fun x => x = s) P); [intros x ->; exact HP | exact (H s s' Hr)].
Qed.

Lemma apost_mono : forall R, mono_tr (apost R).
Proof. intros R P P' H s' [s [HP Hr]]. exists s. auto. Qed.

Theorem gpost_apost : forall R s s', gpost (apost R) s s' <-> R s s'.
Proof.
  intros R s s'. unfold gpost, apost. split.
  - intros [x [-> Hr]]. exact Hr.
  - intros Hr. exists s. auto.
Qed.

(** ** Step 2: from transformers to theories *)

Definition transformer (d : direction) (p : polarity) : rel -> pred -> pred :=
  match p, d with
  | Plain, Forward => apost
  | Plain, Backward => apre
  | Dual, Forward => adpost
  | Dual, Backward => adpre
  end.

Definition theory d p a (R : rel) (P Q : pred) : Prop :=
  match d, a with
  | Forward, Over => sub (transformer d p R P) Q
  | Forward, Under => sub Q (transformer d p R P)
  | Backward, Over => sub (transformer d p R Q) P
  | Backward, Under => sub P (transformer d p R Q)
  end.

Theorem theory_iff_cvr : forall d p a (R : rel) (P Q : pred),
    theory d p a R P Q <-> cvr P Q d p a R.
Proof.
  intros d p a R P Q.
  destruct p, d, a; simpl; unfold sub, apost, apre, adpost, adpre, neg.
  - split.
    + intros H s s' HP Hr. apply H. exists s. auto.
    + intros H s' [s [HP Hr]]. exact (H s s' HP Hr).
  - split; intros H s' HQ; exact (H s' HQ).
  - split.
    + intros H s s' Hr HQ. apply H. exists s'. auto.
    + intros H s [s' [Hr HQ]]. exact (H s s' Hr HQ).
  - split; intros H s HP; exact (H s HP).
  - split.
    + intros H s' Hall. apply H. intros [s [HnP Hr]]. exact (HnP (Hall s Hr)).
    + intros H s' Hn. apply H. intros s Hr. apply NNPP. intros HnP.
      exact (Hn (ex_intro _ s (conj HnP Hr))).
  - split.
    + intros H s' HQ s Hr. apply NNPP. intros HnP.
      exact (H s' HQ (ex_intro _ s (conj HnP Hr))).
    + intros H s' HQ [s [HnP Hr]]. exact (HnP (H s' HQ s Hr)).
  - split.
    + intros H s Hall. apply H. intros [s' [Hr HnQ]]. exact (HnQ (Hall s' Hr)).
    + intros H s Hn. apply H. intros s' Hr. apply NNPP. intros HnQ.
      exact (Hn (ex_intro _ s' (conj Hr HnQ))).
  - split.
    + intros H s HP s' Hr. apply NNPP. intros HnQ.
      exact (H s HP (ex_intro _ s' (conj Hr HnQ))).
    + intros H s HP [s' [Hr HnQ]]. exact (HnQ (H s HP s' Hr)).
Qed.

(** ** Commutation equations *)

Definition rcomp (R1 R2 : rel) : rel :=
  fun s s'' => exists s', R1 s s' /\ R2 s' s''.
Definition runion (R1 R2 : rel) : rel := fun s s' => R1 s s' \/ R2 s s'.

Inductive rtc (R : rel) : rel :=
  | rtc_refl : forall s, rtc R s s
  | rtc_step : forall s s1 s2, R s s1 -> rtc R s1 s2 -> rtc R s s2.

Fixpoint iter (f : pred -> pred) (n : nat) (P : pred) : pred :=
  match n with
  | 0 => P
  | S m => f (iter f m P)
  end.

Lemma apost_comp : forall R1 R2 P,
    peq (apost (rcomp R1 R2) P) (apost R2 (apost R1 P)).
Proof.
  intros R1 R2 P s''. unfold apost, rcomp. split.
  - intros [s [HP [s' [H1 H2]]]]. exists s'. split; [exists s; auto | exact H2].
  - intros [s' [[s [HP H1]] H2]]. exists s. split; [exact HP | exists s'; auto].
Qed.

Lemma apost_union : forall R1 R2 P,
    peq (apost (runion R1 R2) P) (fun s => apost R1 P s \/ apost R2 P s).
Proof.
  intros R1 R2 P s'. unfold apost, runion. split.
  - intros [s [HP [H | H]]]; [left | right]; exists s; auto.
  - intros [[s [HP H]] | [s [HP H]]]; exists s; auto.
Qed.

Lemma apost_rtc : forall R P,
    peq (apost (rtc R) P) (fun s => exists n, iter (apost R) n P s).
Proof.
  intros R P s'. split.
  - intros [s [HP Hr]].
    assert (G : forall s s', rtc R s s' -> forall n, iter (apost R) n P s ->
                exists m, iter (apost R) m P s').
    { intros x x' Hx.
      induction Hx as [x | x x1 x2 Hr1 _ IH]; intros n Hn; [eauto |].
      apply (IH (S n)). exists x. split; assumption. }
    exact (G s s' Hr 0 HP).
  - intros [n Hn]. revert s' Hn. induction n as [|n IH]; intros s' Hn.
    + exists s'. split; [exact Hn | apply rtc_refl].
    + destruct Hn as [s1 [H1 Hr]]. destruct (IH s1 H1) as [s [HP Hs]].
      exists s. split; [exact HP |].
      clear -Hs Hr. induction Hs as [x | x x1 x2 Hx _ IHs].
      * apply (rtc_step R x s' s'); [exact Hr | apply rtc_refl].
      * apply (rtc_step R x x1 s'); [exact Hx | apply IHs, Hr].
Qed.

Lemma apre_comp : forall R1 R2 Q,
    peq (apre (rcomp R1 R2) Q) (apre R1 (apre R2 Q)).
Proof.
  intros R1 R2 Q s. unfold apre, rcomp. split.
  - intros [s'' [[s' [H1 H2]] HQ]]. exists s'.
    split; [exact H1 | exists s''; auto].
  - intros [s' [H1 [s'' [H2 HQ]]]]. exists s''.
    split; [exists s'; auto | exact HQ].
Qed.

Lemma apre_union : forall R1 R2 Q,
    peq (apre (runion R1 R2) Q) (fun s => apre R1 Q s \/ apre R2 Q s).
Proof.
  intros R1 R2 Q s. unfold apre, runion. split.
  - intros [s' [[H | H] HQ]]; [left | right]; exists s'; auto.
  - intros [[s' [H HQ]] | [s' [H HQ]]]; exists s'; auto.
Qed.

Lemma apre_rtc : forall R Q,
    peq (apre (rtc R) Q) (fun s => exists n, iter (apre R) n Q s).
Proof.
  intros R Q s. split.
  - intros [s' [Hr HQ]]. revert HQ.
    induction Hr; intros HQ; [exists 0; exact HQ |].
    destruct (IHHr HQ) as [n Hn]. exists (S n). exists s1. auto.
  - intros [n Hn]. revert s Hn. induction n as [|n IH]; intros s Hn.
    + exists s. split; [apply rtc_refl | exact Hn].
    + destruct Hn as [s1 [Hr H1]]. destruct (IH s1 H1) as [s' [Hs HQ]].
      exists s'. split; [apply (rtc_step R s s1 s'); assumption | exact HQ].
Qed.

End Abstraction.

(** Every language's cube validity is Cousot's theory of its semantics. *)
Corollary cvalid_iff_theory : forall (L : Language) d p a
    (P Q : lstate L -> Prop) c,
    cvalid d p a (@mkTriple L P c Q) <-> theory d p a (sem L c) P Q.
Proof.
  intros L d p a P Q c. rewrite cvalid_cvr. symmetry. apply theory_iff_cvr.
Qed.
