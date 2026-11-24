(** * Adding rules to a logic

    [augment C pool] keeps [C]'s rules and adds [pool]. It is the edge kind
    that the IL ⟷ SIL transformations need: those nodes cannot be reached by
    mapping or selecting rules, because each presentation lacks the rules
    the other needs.

    - Soundness: preserved if the new rules are sound at [C]'s vertex.
    - Completeness: always preserved, since the rules only grow. *)

From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube CubeLogic.

Section Augment.

Context {L : Language}.

Definition augment (C : CubeLogic L) {N : Type} (pool : N -> ruleset L)
  : CubeLogic L :=
  mkCubeLogic (cl_dir C) (cl_approx C) (cl_rule C + N)%type
    (fun r => match r with inl r => cl_pool C r | inr n => pool n end)
    (fun r => match r with inl r => cl_keep C r | inr _ => True end).

(** Restrict an augmented logic to the added rules only. *)
Definition only_new {C : CubeLogic L} {N : Type} (r : cl_rule C + N) : Prop :=
  match r with inl _ => False | inr _ => True end.

Theorem augment_base_sound : forall C N (pool : N -> ruleset L),
    base_sound C ->
    (forall n ps c, pool n ps c ->
       (forall t, ps t -> cube_valid (cl_dir C) (cl_approx C) t) ->
       cube_valid (cl_dir C) (cl_approx C) c) ->
    base_sound (augment C pool).
Proof.
  intros C N pool HB HP ps c [[r|n] [Hk HR]] Hprem.
  - apply (HB ps c); [exists r; auto | exact Hprem].
  - exact (HP n ps c HR Hprem).
Qed.

Theorem augment_complete : forall C N (pool : N -> ruleset L),
    complete (to_logic C) -> complete (to_logic (augment C pool)).
Proof.
  intros C N pool HC t V. apply derivable_mono with (R1 := cl_rules C).
  - intros ps c [[r [Hk HR]] | Hc].
    + left. exists (inl r). auto.
    + right. exact Hc.
  - apply HC, V.
Qed.

End Augment.
