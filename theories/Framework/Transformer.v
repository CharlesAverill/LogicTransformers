(** * Logic transformers

    An [Edge V1 V2] is a verified way of turning a logic with validity
    [V1] into one with validity [V2]. It is a map [emap] on triples that

    - respects assertion equivalence,
    - is a validity correspondence: [V1 t <-> V2 (emap t)], and
    - is onto [V2]-valid triples, up to equivalence.

    [run_edge E Lg] keeps [V2] as the semantics and maps every rule of
    [Lg] through [emap]. The new proof system is the image of the old one.
    Local soundness and completeness carry over along every edge. *)

From Stdlib Require Import Setoid.
From LogicTransformers.Framework Require Import Language ProgramLogic.

(** ** Mapping rules along a map on triples

    The map may change the language, as inversion does. *)

Section MapRules.

Context {L1 L2 : Language}.

(** The image of a premise set. *)
Definition image (f : triple L1 -> triple L2) (ps : triple L1 -> Prop)
  : triple L2 -> Prop :=
  fun t => exists t0, ps t0 /\ t = f t0.

Definition map_rules (f : triple L1 -> triple L2) (R : ruleset L1)
  : ruleset L2 :=
  fun ps c => exists ps0 c0,
    R ps0 c0 /\ c = f c0 /\ (forall t, ps t <-> image f ps0 t).

Definition respects_equiv (f : triple L1 -> triple L2) : Prop :=
  forall t t', triple_equiv t t' -> triple_equiv (f t) (f t').

Lemma map_rules_ext : forall (f g : triple L1 -> triple L2) R ps c,
    (forall t, f t = g t) ->
    map_rules f R ps c <-> map_rules g R ps c.
Proof.
  intros f g R ps c Hfg. unfold map_rules, image.
  split; intros [ps0 [c0 [HR [-> Hps]]]]; exists ps0, c0;
    (split; [exact HR |]); rewrite Hfg; (split; [reflexivity |]);
    intros t; rewrite Hps; split; intros [t0 [H0 ->]]; exists t0;
    rewrite ?Hfg; auto.
Qed.

Lemma derivable_map : forall f R,
    respects_equiv f ->
    forall t, derivable R t -> derivable (map_rules f R) (f t).
Proof.
  intros f R Hf t D.
  induction D as [ps c HR Hps IH | t t' D IH He].
  - apply D_Rule with (ps := image f ps).
    + exists ps, c. repeat split; auto.
    + intros t' [t0 [Hin ->]]. auto.
  - eapply D_Equiv; [exact IH | apply Hf; exact He].
Qed.

End MapRules.

Lemma map_rules_compose : forall {L1 L2 L3 : Language}
    (f : triple L1 -> triple L2) (g : triple L2 -> triple L3) R ps c,
    map_rules g (map_rules f R) ps c <->
    map_rules (fun t => g (f t)) R ps c.
Proof.
  intros L1 L2 L3 f g R ps c. unfold map_rules, image. split.
  - intros [ps1 [c1 [[ps0 [c0 [HR [-> Hps1]]]] [-> Hps]]]].
    exists ps0, c0. split; [exact HR |]. split; [reflexivity |].
    intros t. rewrite Hps. split.
    + intros [t1 [H1 ->]]. apply Hps1 in H1 as [t0 [H0 ->]]. eauto.
    + intros [t0 [H0 ->]]. exists (f t0).
      split; [apply Hps1; exists t0; auto | reflexivity].
  - intros [ps0 [c0 [HR [-> Hps]]]].
    exists (fun t => exists t0, ps0 t0 /\ t = f t0), (f c0).
    split; [exists ps0, c0; repeat split; auto |].
    split; [reflexivity |].
    intros t. rewrite Hps. split.
    + intros [t0 [H0 ->]]. exists (f t0). eauto.
    + intros [t1 [[t0 [H0 ->]] ->]]. eauto.
Qed.

Section Transformer.

Context {L : Language}.

Record Edge (V1 V2 : triple L -> Prop) := mkEdge {
  emap : triple L -> triple L;
  emap_proper : respects_equiv emap;
  edge_tgt_proper : proper_validity V2;
  emap_valid : forall t, V1 t <-> V2 (emap t);
  emap_onto : forall t',
    V2 t' -> exists t, V1 t /\ triple_equiv (emap t) t'
}.

Arguments emap {V1 V2}.
Arguments emap_proper {V1 V2}.
Arguments edge_tgt_proper {V1 V2}.
Arguments emap_valid {V1 V2}.
Arguments emap_onto {V1 V2}.

Definition run_edge {V1 V2} (E : Edge V1 V2) (Lg : ProgramLogic L)
  : ProgramLogic L :=
  mkLogic V2 (edge_tgt_proper E) (map_rules (emap E) (rules Lg)).

Section RunEdge.

Context {V1 V2 : triple L -> Prop} (E : Edge V1 V2) (Lg : ProgramLogic L).
Hypothesis Hsrc : forall t, valid Lg t <-> V1 t.

Theorem run_edge_locally_sound :
  locally_sound Lg -> locally_sound (run_edge E Lg).
Proof.
  intros HS ps c [ps0 [c0 [HR [-> Hps]]]] Hprem. simpl in *.
  apply (emap_valid E), Hsrc, (HS ps0 c0 HR).
  intros t Hin. apply Hsrc, (emap_valid E), Hprem, Hps.
  exists t. auto.
Qed.

Theorem run_edge_sound : locally_sound Lg -> sound (run_edge E Lg).
Proof.
  intros HS. apply locally_sound_sound, run_edge_locally_sound, HS.
Qed.

Theorem run_edge_complete : complete Lg -> complete (run_edge E Lg).
Proof.
  intros HC t' Ht'. simpl in Ht'.
  destruct (emap_onto E t' Ht') as [t [Ht He]].
  eapply D_Equiv; [| exact He].
  apply derivable_map; [apply (emap_proper E) |].
  apply HC, Hsrc, Ht.
Qed.

End RunEdge.

(** ** Composition of edges *)

Definition compose_edge {V1 V2 V3}
    (E1 : Edge V1 V2) (E2 : Edge V2 V3) : Edge V1 V3.
Proof.
  refine (mkEdge V1 V3 (fun t => emap E2 (emap E1 t)) _
            (edge_tgt_proper E2) _ _).
  - intros t t' He. apply (emap_proper E2), (emap_proper E1), He.
  - intros t. rewrite (emap_valid E1). apply (emap_valid E2).
  - intros t3 H3.
    destruct (emap_onto E2 t3 H3) as [t2 [H2 He2]].
    destruct (emap_onto E1 t2 H2) as [t1 [H1 He1]].
    exists t1. split; [exact H1 |].
    eapply triple_equiv_trans; [apply (emap_proper E2), He1 | exact He2].
Defined.

(** Running a composite edge gives the same proof system as running the
    two edges one after the other. *)
Theorem run_compose_edge : forall {V1 V2 V3}
    (E1 : Edge V1 V2) (E2 : Edge V2 V3) Lg t,
    derivable (rules (run_edge (compose_edge E1 E2) Lg)) t <->
    derivable (rules (run_edge E2 (run_edge E1 Lg))) t.
Proof.
  intros V1 V2 V3 E1 E2 Lg t. simpl.
  split; apply derivable_mono; clear t; intros ps c.
  - intros [ps0 [c0 [HR [-> Hps]]]].
    exists (image (emap E1) ps0), (emap E1 c0).
    split; [exists ps0, c0; repeat split; auto |].
    split; [reflexivity |].
    intros t. rewrite Hps. unfold image. split.
    + intros [t0 [H0 ->]]. exists (emap E1 t0). eauto.
    + intros [t1 [[t0 [H0 ->]] ->]]. eauto.
  - intros [ps1 [c1 [[ps0 [c0 [HR [-> Hps1]]]] [-> Hps]]]].
    exists ps0, c0. split; [exact HR |]. split; [reflexivity |].
    intros t. rewrite Hps. unfold image. split.
    + intros [t1 [H1 ->]]. apply Hps1 in H1 as [t0 [H0 ->]]. eauto.
    + intros [t0 [H0 ->]]. exists (emap E1 t0).
      split; [apply Hps1; exists t0; auto | reflexivity].
Qed.

End Transformer.

Arguments Edge {L} V1 V2.
Arguments emap {L V1 V2}.
Arguments emap_proper {L V1 V2}.
Arguments edge_tgt_proper {L V1 V2}.
Arguments emap_valid {L V1 V2}.
Arguments emap_onto {L V1 V2}.
