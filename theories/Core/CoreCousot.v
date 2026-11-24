(** * The whole Cousot cube, generated, for any core language

    For any states and atomic actions, all 16 nodes of the cube are sound
    and complete program logics, with no hand-written rules:

    - top face (partial correctness, [KLang]): HL, IL, SIL from the
      generated pools ([Core.CoreCube]); NC by complementing HL's pool; the
      four [Dual] nodes by complement and Galois edges;
    - bottom face (with ⊥, [KLangB]): the same construction from the
      bottom-face generator ([Core.GenerateBot]).

    [core_cousot_cube_top] and [core_cousot_cube_bottom] state the result. *)

From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube CubeLogic Transformer.
From LogicTransformers.Transformers Require Import Flip Complement Galois.
From LogicTransformers.Core Require Import
  Kernel KernelBot Generate GenerateBot CoreCube.

Section CoreCousot.

Context {Σ Act : Type} (act_sem : Act -> Σ -> Σ -> Prop).

Lemma rel_refl : forall a s s', act_sem a s s' <-> act_sem a s s'.
Proof. intros. split; auto. Qed.

Definition sound_complete {L : Language} (Lg : ProgramLogic L) : Prop :=
  sound Lg /\ complete Lg.

Lemma sc_of_cl : forall {L : Language} (C : CubeLogic L),
    base_sound C -> complete (to_logic C) -> sound_complete (to_logic C).
Proof.
  intros L C HB HC. split; [apply locally_sound_sound, cl_locally_sound, HB
                          | exact HC].
Qed.

Lemma sc_of_edge : forall {L : Language} V1 V2 (E : Edge V1 V2)
    (Lg : ProgramLogic L),
    (forall t, valid Lg t <-> V1 t) ->
    locally_sound Lg -> complete Lg -> sound_complete (run_edge E Lg).
Proof.
  intros L V1 V2 E Lg Hv HS HC. split.
  - apply run_edge_sound; assumption.
  - apply run_edge_complete; assumption.
Qed.

(** ** Top face *)

Notation T := (KLang act_sem).

Definition tHL : CubeLogic T := GHL act_sem act_sem.
Definition tIL : CubeLogic T := GIL act_sem act_sem.
Definition tSIL : CubeLogic T := GSIL act_sem act_sem.
Definition tNC : CubeLogic T := complement_cl tHL.

Lemma tNC_base_sound : base_sound tNC.
Proof.
  apply complement_cl_base_sound; [reflexivity | reflexivity |].
  apply GHL_base_sound, rel_refl.
Qed.

Lemma tNC_complete : complete (to_logic tNC).
Proof.
  apply exact_complete. change (exact Backward (cl_base tNC)).
  eapply exact_mono;
    [| apply (complement_wlp_exact _ (bwd_exact act_sem act_sem rel_refl))].
  intros ps c [ps0 [c0 [[g HR] [-> Hps]]]].
  exists (inr g). split; [exact I |]. exists ps0, c0. auto.
Qed.

Lemma tHL_ls : locally_sound (to_logic tHL).
Proof. apply cl_locally_sound, GHL_base_sound, rel_refl. Qed.
Lemma tIL_ls : locally_sound (to_logic tIL).
Proof. apply cl_locally_sound, GIL_base_sound, rel_refl. Qed.
Lemma tSIL_ls : locally_sound (to_logic tSIL).
Proof. apply cl_locally_sound, GSIL_base_sound, rel_refl. Qed.

Theorem core_cousot_cube_top :
  sound_complete (to_logic tHL) /\ sound_complete (to_logic tIL) /\
  sound_complete (to_logic tNC) /\ sound_complete (to_logic tSIL) /\
  sound_complete (run_edge (complement_edge Forward Plain Under)
                           (to_logic tIL)) /\
  sound_complete (run_edge (complement_edge Forward Plain Over)
                           (to_logic tHL)) /\
  sound_complete (run_edge (complement_edge Backward Plain Under)
                           (to_logic tSIL)) /\
  sound_complete (run_edge galois_hl_wlp (to_logic tHL)).
Proof.
  pose proof (GHL_complete act_sem act_sem rel_refl) as CHL.
  pose proof (GIL_complete act_sem act_sem rel_refl) as CIL.
  pose proof (GSIL_complete act_sem act_sem rel_refl) as CSIL.
  pose proof tHL_ls. pose proof tIL_ls. pose proof tSIL_ls.
  pose proof (cl_locally_sound _ tNC_base_sound). pose proof tNC_complete.
  repeat split;
    try (apply run_edge_sound; [intros; reflexivity | assumption]);
    try (apply run_edge_complete; [intros; reflexivity | assumption]);
    try (apply locally_sound_sound; assumption);
    try assumption.
Qed.

(** ** Bottom face *)

Notation B := (KLangB act_sem).

Definition bpool (r : cname) : ruleset B :=
  match r with
  | inl g => @fwdB_rule Σ Act act_sem act_sem g
  | inr g => @bwdB_rule Σ Act act_sem act_sem g
  end.

Definition bHL : CubeLogic B :=
  mkCubeLogic Forward Over cname bpool (fun _ => True).
Definition bIL : CubeLogic B := flip (restrict bHL is_fwd).
Definition bSIL : CubeLogic B := flip (restrict (complement_cl bHL) is_bwd).
Definition bNC : CubeLogic B := complement_cl bHL.

Lemma bHL_base_sound : base_sound bHL.
Proof.
  intros ps c [[g|g] [_ HR]] Hprem.
  - exact (fwdB_over_sound act_sem act_sem rel_refl g ps c HR Hprem).
  - exact (bwdB_over_sound act_sem act_sem rel_refl g ps c HR Hprem).
Qed.

Lemma bHL_fwd_exact : exact Forward (cl_base (restrict bHL is_fwd)).
Proof.
  intros P c.
  eapply derivable_mono; [| apply (fwdB_exact act_sem act_sem rel_refl)].
  intros ps c' [g HR]. exists (inl g). split; [split; exact I | exact HR].
Qed.

Lemma bHL_complete : complete (to_logic bHL).
Proof.
  apply exact_complete. eapply exact_mono; [| apply bHL_fwd_exact].
  intros ps c [r [_ HR]]. exists r. split; [exact I | exact HR].
Qed.

Lemma bIL_base_sound : base_sound bIL.
Proof.
  intros ps c [[g|g] [[_ Hk] HR]] Hprem; [| contradiction].
  exact (fwdB_under_sound act_sem act_sem rel_refl g ps c HR Hprem).
Qed.

Lemma bIL_complete : complete (to_logic bIL).
Proof. apply (flip_complete (restrict bHL is_fwd)), bHL_fwd_exact. Qed.

Lemma bwd_exact_compl : exact Backward
    (map_rules complement (@bwdB_base Σ Act act_sem act_sem)).
Proof.
  apply complement_wlp_exact. intros c Q.
  apply (bwdB_exact act_sem act_sem rel_refl).
Qed.

Lemma bSIL_base_sound : base_sound bSIL.
Proof.
  intros ps c [[g|g] [[_ Hk] [ps0 [c0 [HR [-> Hps]]]]]] Hprem;
    [contradiction |].
  change (cube_valid Backward Under (complement c0)).
  apply dual_sil_duality,
        (bwdB_dual_sound act_sem act_sem rel_refl g ps0 c0 HR).
  intros t Ht. apply dual_sil_duality, Hprem, Hps. exists t. auto.
Qed.

Lemma bSIL_complete : complete (to_logic bSIL).
Proof.
  apply exact_complete. change (exact Backward (cl_base bSIL)).
  eapply exact_mono; [| apply bwd_exact_compl].
  intros ps c [ps0 [c0 [[g HR] [-> Hps]]]].
  exists (inr g). split; [split; exact I |]. exists ps0, c0. auto.
Qed.

Lemma bNC_base_sound : base_sound bNC.
Proof.
  apply complement_cl_base_sound; [reflexivity | reflexivity |].
  apply bHL_base_sound.
Qed.

Lemma bNC_complete : complete (to_logic bNC).
Proof.
  apply exact_complete. change (exact Backward (cl_base bNC)).
  eapply exact_mono; [| apply bwd_exact_compl].
  intros ps c [ps0 [c0 [[g HR] [-> Hps]]]].
  exists (inr g). split; [exact I |]. exists ps0, c0. auto.
Qed.

Theorem core_cousot_cube_bottom :
  sound_complete (to_logic bHL) /\ sound_complete (to_logic bIL) /\
  sound_complete (to_logic bNC) /\ sound_complete (to_logic bSIL) /\
  sound_complete (run_edge (complement_edge Forward Plain Under)
                           (to_logic bIL)) /\
  sound_complete (run_edge (complement_edge Forward Plain Over)
                           (to_logic bHL)) /\
  sound_complete (run_edge (complement_edge Backward Plain Under)
                           (to_logic bSIL)) /\
  sound_complete (run_edge galois_hl_wlp (to_logic bHL)).
Proof.
  pose proof (cl_locally_sound _ bHL_base_sound) as SHL.
  pose proof (cl_locally_sound _ bIL_base_sound) as SIL.
  pose proof (cl_locally_sound _ bSIL_base_sound) as SSIL.
  pose proof bHL_complete. pose proof bIL_complete. pose proof bSIL_complete.
  pose proof (cl_locally_sound _ bNC_base_sound). pose proof bNC_complete.
  repeat split;
    try (apply run_edge_sound; [intros; reflexivity | assumption]);
    try (apply run_edge_complete; [intros; reflexivity | assumption]);
    try (apply locally_sound_sound; assumption);
    try assumption.
Qed.

End CoreCousot.
