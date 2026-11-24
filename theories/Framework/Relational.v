(** * Cube validity as a property of a relation

    [cvr P Q d p a R]: validity at node [(d, p, a)] of [{P} R {Q}], for
    any relation [R]. [cvalid_cvr]: in any language, cube validity of a
    triple only depends on the program's input/output relation.

    Two ways to move validity between relations:
    - [cvr_transfer]: between relations that agree;
    - [cvr_proj]: from a relation [R] on [S] to a relation [R'] on a
      richer state space [S'], when [R'] is [R] seen through a projection
      [pi : S' -> S] and ends only in states satisfying [fin]. This is
      the situation of an encoding that keeps extra control information
      in its states (e.g. the program still to run): preconditions are
      read through [pi], postconditions through [liftG]. *)

From Stdlib Require Import Setoid.
From LogicTransformers.Framework Require Import Language ProgramLogic Cube.

Definition cvr {S : Type} (P Q : S -> Prop) d p a (R : S -> S -> Prop)
  : Prop :=
  match p with
  | Plain =>
      match d, a with
      | Forward, Over => forall s s', P s -> R s s' -> Q s'
      | Forward, Under => forall s', Q s' -> exists s, P s /\ R s s'
      | Backward, Over => forall s s', R s s' -> Q s' -> P s
      | Backward, Under => forall s, P s -> exists s', R s s' /\ Q s'
      end
  | Dual =>
      match d, a with
      | Forward, Over => forall s', (forall s, R s s' -> P s) -> Q s'
      | Forward, Under => forall s', Q s' -> forall s, R s s' -> P s
      | Backward, Over => forall s, (forall s', R s s' -> Q s') -> P s
      | Backward, Under => forall s, P s -> forall s', R s s' -> Q s'
      end
  end.

Lemma cvalid_cvr : forall (L : Language) (P Q : lstate L -> Prop) c d p a,
    cvalid d p a (@mkTriple L P c Q) <-> cvr P Q d p a (sem L c).
Proof.
  intros L P Q c d [] a; destruct d, a; simpl;
    unfold aimpl, img, preimg, dimg, wlp; simpl; firstorder.
Qed.

Lemma cvr_transfer : forall {S : Type} (R1 R2 : S -> S -> Prop) P Q d p a,
    (forall s s', R1 s s' <-> R2 s s') ->
    cvr P Q d p a R1 -> cvr P Q d p a R2.
Proof.
  intros S R1 R2 P Q d p a HR H. destruct p, d, a; simpl in *.
  - intros s s' HP Hr. apply (H s s' HP), HR, Hr.
  - intros s' HQ. destruct (H s' HQ) as [s [HP Hr]].
    exists s. split; [exact HP | apply HR, Hr].
  - intros s s' Hr HQ. apply (H s s'); [apply HR, Hr | exact HQ].
  - intros s HP. destruct (H s HP) as [s' [Hr HQ]].
    exists s'. split; [apply HR, Hr | exact HQ].
  - intros s' Hall. apply H. intros s Hr. apply Hall, HR, Hr.
  - intros s' HQ s Hr. apply (H s' HQ s), HR, Hr.
  - intros s Hall. apply H. intros s' Hr. apply Hall, HR, Hr.
  - intros s HP s' Hr. apply (H s HP s'), HR, Hr.
Qed.

(** ** Projections *)

(** A postcondition on [S] read on [S']: final and [Q]. At the node
    p̃ost ⊆ (forward, dual, over) the reading is "final implies [Q]",
    since there a state no run can reach must satisfy the post. *)
Definition liftG {S S' : Type} (pi : S' -> S) (fin : S' -> Prop)
    d p a (Q : S -> Prop) : S' -> Prop :=
  match p, d, a with
  | Dual, Forward, Over => fun k => fin k -> Q (pi k)
  | _, _, _ => fun k => fin k /\ Q (pi k)
  end.

Lemma cvr_proj : forall {S S' : Type} (pi : S' -> S) (fin : S' -> Prop)
    (R : S -> S -> Prop) (R' : S' -> S' -> Prop) (P Q : S -> Prop) d p a,
    (forall s, exists k, fin k /\ pi k = s) ->
    (forall k k', R' k k' <-> fin k' /\ R (pi k) (pi k')) ->
    cvr P Q d p a R <->
    cvr (fun k => P (pi k)) (liftG pi fin d p a Q) d p a R'.
Proof.
  intros S S' pi fin R R' P Q d p a Hs HR.
  destruct p, d, a; simpl; setoid_rewrite HR; split.
  - intros H k k' HP [Hf Hr]. split; [exact Hf | exact (H _ _ HP Hr)].
  - intros H s s' HP Hr. destruct (Hs s) as [k [_ <-]].
    destruct (Hs s') as [k' [Hf <-]]. exact (proj2 (H k k' HP (conj Hf Hr))).
  - intros H k' [Hf HQ]. destruct (H _ HQ) as [s [HP Hr]].
    destruct (Hs s) as [k [_ <-]]. exists k. auto.
  - intros H s' HQ. destruct (Hs s') as [k' [Hf <-]].
    destruct (H k' (conj Hf HQ)) as [k [HP [_ Hr]]]. exists (pi k). auto.
  - intros H k k' [_ Hr] [_ HQ]. eauto.
  - intros H s s' Hr HQ. destruct (Hs s) as [k [_ <-]].
    destruct (Hs s') as [k' [Hf <-]]. eapply H; split; eauto.
  - intros H k HP. destruct (H _ HP) as [s' [Hr HQ]].
    destruct (Hs s') as [k' [Hf <-]]. exists k'. auto.
  - intros H s HP. destruct (Hs s) as [k [_ <-]].
    destruct (H k HP) as [k' [[_ Hr] [_ HQ]]]. eauto.
  - intros H k' Hall Hf. apply H. intros s Hr.
    destruct (Hs s) as [k [_ <-]]. apply Hall. auto.
  - intros H s' Hall. destruct (Hs s') as [k' [Hf <-]].
    apply (H k'); [intros k [_ Hr]; apply Hall, Hr | exact Hf].
  - intros H k' [_ HQ] k [_ Hr]. eauto.
  - intros H s' HQ s Hr. destruct (Hs s') as [k' [Hf <-]].
    destruct (Hs s) as [k [_ <-]]. eapply H; split; eauto.
  - intros H k Hall. apply H. intros s' Hr.
    destruct (Hs s') as [k' [Hf <-]]. exact (proj2 (Hall k' (conj Hf Hr))).
  - intros H s Hall. destruct (Hs s) as [k [_ <-]]. apply H.
    intros k' [Hf Hr]. auto.
  - intros H k HP k' [Hf Hr]. split; [exact Hf | exact (H _ HP _ Hr)].
  - intros H s HP s' Hr. destruct (Hs s) as [k [_ <-]].
    destruct (Hs s') as [k' [Hf <-]]. exact (proj2 (H k HP k' (conj Hf Hr))).
Qed.
