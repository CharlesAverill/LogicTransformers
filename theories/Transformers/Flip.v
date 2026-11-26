(** * Restricting and flipping cube logics

    - [restrict C keep] keeps only the rules of [C] that satisfy [keep].
    - [flip C] keeps the vertex's direction and the kept rules, but flips
      over-approximation to under-approximation (or back). The consequence
      rule is the only one that changes.

    The flip keeps triples and rules as they are and changes their
    meaning, so soundness is not inherited. Every kept rule has to be
    sound at the new vertex ([base_sound (flip C)]). Completeness, on the
    other hand, transfers for free whenever the kept rules are exact
    ([flip_complete]).

    [flip_works_iff]: for exact kept rules, the flip gives sound and
    complete logics at both approximations exactly when every kept rule
    is sound at both. [ImpCube.FlipPresentation] shows that this depends on
    how the rules are written, not on what they prove. *)

From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube CubeLogic.

Section Flip.

Context {L : Language}.

Definition restrict (C : CubeLogic L) (keep : cl_rule C -> Prop)
  : CubeLogic L :=
  mkCubeLogic (cl_dir C) (cl_approx C) (cl_rule C) (cl_pool C)
    (fun r => cl_keep C r /\ keep r).

Definition flip (C : CubeLogic L) : CubeLogic L :=
  mkCubeLogic (cl_dir C) (flip_approx (cl_approx C)) (cl_rule C)
    (cl_pool C) (cl_keep C).

Lemma restrict_base : forall C keep ps c,
    cl_base (restrict C keep) ps c -> cl_base C ps c.
Proof. intros C keep ps c [r [[Hk _] Hr]]. exists r. auto. Qed.

(** Restriction preserves soundness. Completeness has to be re-proved,
    since the dropped rules may have been needed. *)
Theorem restrict_base_sound : forall C keep,
    base_sound C -> base_sound (restrict C keep).
Proof.
  intros C keep HB ps c Hb Hprem.
  exact (HB ps c (restrict_base C keep ps c Hb) Hprem).
Qed.

Lemma flip_flip_approx : forall a, flip_approx (flip_approx a) = a.
Proof. destruct a; reflexivity. Qed.

(** If the kept rules are sound under both approximations, both logics
    are locally sound. *)
Theorem flip_locally_sound : forall C,
    base_sound C -> base_sound (flip C) ->
    locally_sound (to_logic C) /\ locally_sound (to_logic (flip C)).
Proof. intros C H1 H2. split; apply cl_locally_sound; assumption. Qed.

(** Exactness doesn't depend on the approximation, so it makes both
    sides of the flip complete. *)
Theorem flip_complete : forall C,
    exact (cl_dir C) (cl_base C) ->
    complete (to_logic C) /\ complete (to_logic (flip C)).
Proof. intros C Hex. split; apply exact_complete; exact Hex. Qed.

(** ** When flipping works, exactly

    A flipped logic is locally sound exactly when its kept rules are
    sound at the new corner: the consequence rule is always sound. *)
Theorem flip_sound_iff : forall C,
    locally_sound (to_logic (flip C)) <-> base_sound (flip C).
Proof.
  intros C. split; [apply locally_sound_base | apply cl_locally_sound].
Qed.

(** A rule is sound at both approximations of its direction. *)
Definition bisound (d : direction) (R : @ruleset L) : Prop :=
  forall ps c, R ps c ->
    ((forall t, ps t -> cube_valid d Over t) -> cube_valid d Over c) /\
    ((forall t, ps t -> cube_valid d Under t) -> cube_valid d Under c).

Definition tri_exact (d : direction) (t : @triple L) : Prop :=
  cube_valid d Over t /\ cube_valid d Under t.

(** Such a rule maps exact premises to an exact conclusion. *)
Lemma bisound_exact_preserving : forall d R ps c,
    bisound d R -> R ps c ->
    (forall t, ps t -> tri_exact d t) -> tri_exact d c.
Proof.
  intros d R ps c HB HR Hps. destruct (HB ps c HR) as [Ho Hu].
  split; [apply Ho | apply Hu]; intros t Ht; apply Hps, Ht.
Qed.

(** For an exact rule set, flipping gives sound and complete logics at
    both approximations if and only if every kept rule is sound at both. *)
Theorem flip_works_iff : forall C,
    exact (cl_dir C) (cl_base C) ->
    (locally_sound (to_logic C) /\ complete (to_logic C) /\
     locally_sound (to_logic (flip C)) /\ complete (to_logic (flip C)))
    <-> (base_sound C /\ base_sound (flip C)).
Proof.
  intros C Hex. split.
  - intros [H1 [_ [H3 _]]].
    split; apply locally_sound_base; assumption.
  - intros [H1 H2]. destruct (flip_complete C Hex) as [Hc1 Hc2].
    repeat split; try assumption; apply cl_locally_sound; assumption.
Qed.

End Flip.
