(** * Cube logics: a vertex, a rule pool, and a selection

    A [CubeLogic] is a vertex of the cube (direction × approximation), a
    named pool of language-specific rules, and the subset of the pool it
    keeps. Its proof system is the kept rules plus the vertex's
    consequence rule. The consequence rule is generic: it is the only
    rule that depends on the vertex. Transformers such as [flip] can
    therefore swap it without inspecting the language's rules.

    The main generic result is [exact_complete]: if the kept rules derive
    the exact triples (strongest postconditions going forward, weakest
    "possible" preconditions going backward) without consequence, the
    logic is complete. Exactness doesn't depend on the approximation knob,
    which is what makes the flip preserve completeness. *)

From LogicTransformers.Framework Require Import Language ProgramLogic Cube.

Section CubeLogic.

Context {L : Language}.

(** ** Consequence, per vertex

    The side conditions for deriving [(P, c, Q)] from [(P', c, Q')]. HL and
    SIL may strengthen the pre and weaken the post; IL and NC are the
    other way round. *)

Definition cons_side (d : direction) (a : approximation)
    (P P' Q Q' : assertion L) : Prop :=
  match d, a with
  | Forward, Over | Backward, Under => aimpl P P' /\ aimpl Q' Q
  | Forward, Under | Backward, Over => aimpl P' P /\ aimpl Q Q'
  end.

Definition cons_rule (d : direction) (a : approximation) : ruleset L :=
  fun ps c => exists P P' Q Q' cm,
    cons_side d a P P' Q Q' /\
    ps = (fun t => t = mkTriple P' cm Q') /\
    c = mkTriple P cm Q.

Lemma cons_rule_sound : forall d a ps c,
    cons_rule d a ps c ->
    (forall t, ps t -> cube_valid d a t) -> cube_valid d a c.
Proof.
  intros d a ps c [P [P' [Q [Q' [cm [Hside [-> ->]]]]]]] Hprem.
  specialize (Hprem _ eq_refl).
  destruct d, a; destruct Hside as [H1 H2]; simpl in *;
    unfold aimpl, img, preimg in *.
  - intros s' [s [Hs Hr]]. apply H2, Hprem. exists s. auto.
  - intros s' Hs'. destruct (Hprem s' (H2 s' Hs')) as [s [Hs Hr]].
    exists s. auto.
  - intros s [s' [Hr Hs']]. apply H1, Hprem. exists s'. auto.
  - intros s Hs. destruct (Hprem s (H1 s Hs)) as [s' [Hr Hs']].
    exists s'. auto.
Qed.

(** ** Cube logics *)

Record CubeLogic := mkCubeLogic {
  cl_dir : direction;
  cl_approx : approximation;
  cl_rule : Type;
  cl_pool : cl_rule -> ruleset L;
  cl_keep : cl_rule -> Prop
}.

(** The kept language-specific rules, without consequence. *)
Definition cl_base (C : CubeLogic) : ruleset L :=
  fun ps c => exists r, cl_keep C r /\ cl_pool C r ps c.

Definition cl_rules (C : CubeLogic) : ruleset L :=
  fun ps c => cl_base C ps c \/ cons_rule (cl_dir C) (cl_approx C) ps c.

Definition to_logic (C : CubeLogic) : ProgramLogic L :=
  mkLogic (cube_valid (cl_dir C) (cl_approx C)) (cube_valid_proper _ _)
    (cl_rules C).

(** Local soundness of the kept rules at the logic's own vertex. *)
Definition base_sound (C : CubeLogic) : Prop :=
  forall ps c,
    cl_base C ps c ->
    (forall t, ps t -> cube_valid (cl_dir C) (cl_approx C) t) ->
    cube_valid (cl_dir C) (cl_approx C) c.

Theorem cl_locally_sound : forall C,
    base_sound C -> locally_sound (to_logic C).
Proof.
  intros C HB ps c [Hb | Hc] Hprem.
  - exact (HB ps c Hb Hprem).
  - exact (cons_rule_sound _ _ ps c Hc Hprem).
Qed.

Lemma locally_sound_base : forall C,
    locally_sound (to_logic C) -> base_sound C.
Proof. intros C H ps c Hb Hprem. exact (H ps c (or_introl Hb) Hprem). Qed.

(** Derivations from the kept rules alone are valid. *)
Lemma base_derivable_valid : forall C, base_sound C ->
    forall t, derivable (cl_base C) t -> cube_valid (cl_dir C) (cl_approx C) t.
Proof.
  intros C HB t D. induction D.
  - eapply HB; eauto.
  - eapply cube_valid_proper; eauto.
Qed.

(** ** Exactness and completeness *)

Definition exact (d : direction) (base : ruleset L) : Prop :=
  match d with
  | Forward => forall P c, derivable base (mkTriple P c (img c P))
  | Backward => forall Q c, derivable base (mkTriple (preimg c Q) c Q)
  end.

Lemma exact_mono : forall d (R1 R2 : ruleset L),
    (forall ps c, R1 ps c -> R2 ps c) -> exact d R1 -> exact d R2.
Proof.
  intros d R1 R2 H Hex.
  destruct d; simpl in *; intros; eapply derivable_mono; eauto.
Qed.

Theorem exact_complete : forall C,
    exact (cl_dir C) (cl_base C) -> complete (to_logic C).
Proof.
  intros C Hex [P c Q] V.
  assert (Hlift : forall t, derivable (cl_base C) t ->
                            derivable (cl_rules C) t)
    by (apply derivable_mono; intros; left; assumption).
  simpl in *.
  destruct C as [d a N pool keep]; simpl in *.
  destruct d; simpl in Hex.
  - apply D_Rule with (ps := fun t => t = mkTriple P c (img c P)).
    + right. exists P, P, Q, (img c P), c.
      split; [| split; reflexivity].
      destruct a; split; try exact V; intros s Hs; exact Hs.
    + intros t ->. apply Hlift, Hex.
  - apply D_Rule with (ps := fun t => t = mkTriple (preimg c Q) c Q).
    + right. exists P, (preimg c Q), Q, Q, c.
      split; [| split; reflexivity].
      destruct a; split; try exact V; intros s Hs; exact Hs.
    + intros t ->. apply Hlift, Hex.
Qed.

End CubeLogic.

Arguments CubeLogic L : clear implicits.
