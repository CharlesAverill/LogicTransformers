(** * Sufficient incorrectness logic, two ways

    A SIL triple [(P, c, Q)] says: from every state in [P], some run of
    [c] ends in [Q]. Two routes from [HL] reach it:

<<
    Route A:  HL ──complement──▶ NC ──restrict bwd, flip──▶ SIL
    Route B:  HL ──invert, complement──▶ HL(Imp⁻¹)
                 ──restrict bwd, flip──▶ IL(Imp⁻¹) ──invert──▶ SIL
>>

    [SIL_routes_agree]: the two routes give the same vertex and the same
    rule set, so this face of the cube commutes. Route A is proved sound
    and complete, and route B inherits both through the agreement.

    Along the way, [NC_C] (NC built as a cube logic by complementing the
    pool) is shown to derive the same triples as [NC.NC] (built with the
    complement edge). *)

From Stdlib Require Import Classical.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube CubeLogic Transformer.
From LogicTransformers.Transformers Require Import Flip Complement Invert.
From LogicTransformers.Imp Require Import Syntax BigStep Lang.
From LogicTransformers.Imp Require Import Hoare.
From LogicTransformers.ImpCube Require Import ImpRules HoareLogic NC.

(** ** The two routes *)

Definition NC_C : CubeLogic Imp := complement_cl HL_C.

Definition SIL_A : CubeLogic Imp := flip (restrict NC_C bwd).

(** Hoare logic over the inverse language, then IL over it. *)
Definition HL_inv : CubeLogic (inv Imp) := complement_cl (inv_cl HL_C).
Definition IL_inv : CubeLogic (inv Imp) := flip (restrict HL_inv bwd).

(** [inv (inv Imp)] is [Imp] up to conversion. *)
Definition SIL_B : CubeLogic Imp := inv_cl IL_inv.

(** ** The face commutes *)

Theorem SIL_routes_agree :
  cl_dir SIL_A = cl_dir SIL_B /\
  cl_approx SIL_A = cl_approx SIL_B /\
  (forall ps c, cl_rules SIL_A ps c <-> cl_rules SIL_B ps c).
Proof.
  split; [reflexivity |]. split; [reflexivity |].
  intros ps c.
  assert (Hpool : forall r,
    map_rules swap (map_rules complement (map_rules swap (imp_rule r))) ps c
    <-> map_rules complement (imp_rule r) ps c).
  { intros r. rewrite !map_rules_compose. apply map_rules_ext.
    intros [P c' Q]. reflexivity. }
  split; intros [[r [Hk Hr]] | Hc].
  - left. exists r. split; [exact Hk | apply Hpool, Hr].
  - right. exact Hc.
  - left. exists r. split; [exact Hk | apply Hpool, Hr].
  - right. exact Hc.
Qed.

Corollary SIL_routes_same_logic : forall t,
    (valid (to_logic SIL_A) t <-> valid (to_logic SIL_B) t) /\
    (derivable (rules (to_logic SIL_A)) t <->
     derivable (rules (to_logic SIL_B)) t).
Proof.
  intros t. destruct SIL_routes_agree as [_ [_ H]].
  split; [reflexivity |].
  split; apply derivable_mono; intros ps c; apply H.
Qed.

(** ** Route A is sound and complete *)

Lemma SIL_valid_iff : forall P c Q,
    valid (to_logic SIL_A) (ht P c Q) <->
    (forall st, P st -> exists st', ceval c st st' /\ Q st').
Proof. intros P c Q. exact (sil_valid_iff (ht P c Q)). Qed.

Theorem SIL_A_locally_sound : locally_sound (to_logic SIL_A).
Proof.
  apply cl_locally_sound.
  intros ps c [r [[_ Hb] [ps0 [c0 [HR [-> Hps]]]]]] Hprem.
  change (cube_valid Backward Under (complement c0)).
  apply dual_sil_duality, (imp_rule_dual_sound r ps0 c0 Hb HR).
  intros t Ht. apply dual_sil_duality, Hprem, Hps. exists t. auto.
Qed.

Theorem SIL_A_complete : complete (to_logic SIL_A).
Proof.
  apply exact_complete.
  change (exact Backward (cl_base SIL_A)).
  eapply exact_mono; [| apply (complement_wlp_exact bwd_base bwd_exact)].
  intros ps c [ps0 [c0 [[r [Hb HR]] [-> Hps]]]].
  exists r. split; [split; [exact I | exact Hb] |].
  exists ps0, c0. auto.
Qed.

(** ** Route B inherits both *)

Theorem SIL_B_sound : sound (to_logic SIL_B).
Proof.
  intros t D. apply SIL_routes_same_logic.
  apply (locally_sound_sound _ SIL_A_locally_sound).
  apply SIL_routes_same_logic, D.
Qed.

Theorem SIL_B_complete : complete (to_logic SIL_B).
Proof.
  intros t V. apply SIL_routes_same_logic.
  apply SIL_A_complete, SIL_routes_same_logic, V.
Qed.

(** ** NC as a cube logic agrees with NC from the edge *)

Lemma HL_base_sound : base_sound HL_C.
Proof.
  intros ps c [r [_ HR]] Hprem. exact (imp_rule_over_sound r ps c HR Hprem).
Qed.

Theorem NC_C_locally_sound : locally_sound (to_logic NC_C).
Proof.
  apply cl_locally_sound, complement_cl_base_sound;
    [reflexivity | reflexivity | apply HL_base_sound].
Qed.

Theorem NC_C_complete : complete (to_logic NC_C).
Proof.
  apply exact_complete.
  change (exact Backward (cl_base NC_C)).
  eapply exact_mono; [| apply (complement_wlp_exact bwd_base bwd_exact)].
  intros ps c [ps0 [c0 [[r [_ HR]] [-> Hps]]]].
  exists r. split; [exact I |]. exists ps0, c0. auto.
Qed.

Theorem NC_C_agrees_NC : forall t,
    derivable (rules (to_logic NC_C)) t <-> derivable (rules NC) t.
Proof.
  intros t. split; intros D.
  - apply NC_complete.
    exact (locally_sound_sound _ NC_C_locally_sound t D).
  - apply NC_C_complete. exact (NC_sound t D).
Qed.

(** ** Inversion carries soundness and completeness

    Inverting HL gives a sound and complete logic at the NC vertex of the
    inverse language. *)

Theorem HL_inverted_sound_complete :
  locally_sound (to_logic (inv_cl HL_C)) /\ complete (to_logic (inv_cl HL_C)).
Proof.
  split; [apply inv_cl_locally_sound, HL_base_sound |].
  apply inv_cl_complete, HL_complete.
Qed.
