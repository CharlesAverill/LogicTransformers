(** * Restricting and flipping cube logics

    - [restrict C keep] keeps only the rules of [C] that satisfy [keep].
    - [flip C] keeps the vertex's direction and the kept rules, but flips
      over-approximation to under-approximation (or back). The consequence
      rule is the only one that changes.

    The flip keeps triples and rules as they are and changes their
    meaning, so soundness is not inherited. Every kept rule has to be
    sound at the new vertex ([base_sound (flip C)]). Completeness, on the
    other hand, transfers for free whenever the kept rules are exact
    ([flip_complete]). *)

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

End Flip.
