(** * The bottom face of the Cousot cube for Imp

    The bottom face is the cube over [ImpBot], where postconditions can
    mention nontermination ⊥ ([None]). Its nodes are [cvalid d p a] over
    [ImpBot]. Here:

    - [HLB] (post ⊆): HL⊥, from the whole pool (forward rules [brule]
      and backward rules [wrule], all HL⊥-sound). On triples whose
      post excludes ⊥ it is total correctness ([HLB_total_iff]). On triples
      whose post includes ⊥ it is partial correctness, i.e. the top-face
      Hoare logic ([HLB_partial_iff]).
    - [ILB] (post ⊇): the flip of HLB restricted to the forward rules,
      sound and complete for free because those rules are two-sided sound
      and exact.
    - [SILB] (pre ⊇): complement HLB, restrict to the backward rules,
      flip, exactly as for SIL on the top face. [preDB_over] (p̃re ⊆) is
      its complement.
    - By edges from HLB and ILB: [postDB_under] (p̃ost ⊇, complement),
      [preDB_under] (p̃re ⊇, Galois), [NCB] (pre ⊆, Galois from
      [postDB_under]) and [postDB_over] (p̃ost ⊆, complement of ILB).

    [termination_not_recoverable] is the obstruction for the vertical
    edges. Two programs with the same top-face theory at every node can
    differ on the bottom face, so no transformer that only sees the
    top-face theory can produce a bottom-face logic. The top face is an
    abstraction of the bottom one (Cousot's termination abstraction), not
    an isomorphic copy. *)

From Stdlib Require Import Classical.
From LogicTransformers.Imp Require Import Syntax BigStep Diverge Lang LangBot.
From LogicTransformers.Logics Require Import Hoare BotRules BotWlpRules.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube CubeLogic Transformer.
From LogicTransformers.Transformers Require Import Flip Complement Galois.

(** ** HL⊥ and IL⊥ *)

(** The bottom-face pool: forward and backward rules, with selections. *)
Definition bot_name : Type := (brule_name + wrule_name)%type.

Definition bot_rule (r : bot_name) : ruleset ImpBot :=
  match r with inl r => brule r | inr r => wrule r end.

Definition fwdB (r : bot_name) : Prop :=
  match r with inl _ => True | inr _ => False end.
Definition bwdB (r : bot_name) : Prop :=
  match r with inl _ => False | inr _ => True end.

Definition HLB_C : CubeLogic ImpBot :=
  mkCubeLogic Forward Over bot_name bot_rule (fun _ => True).

Definition HLB : ProgramLogic ImpBot := to_logic HLB_C.
Definition ILB : ProgramLogic ImpBot := to_logic (flip (restrict HLB_C fwdB)).

Lemma fwd_exact : exact Forward (cl_base (restrict HLB_C fwdB)).
Proof.
  intros P c. eapply derivable_mono; [| apply bexact].
  intros ps c' [r HR]. exists (inl r).
  split; [split; exact I | exact HR].
Qed.

Theorem HLB_locally_sound : locally_sound HLB.
Proof.
  apply cl_locally_sound. intros ps c [[r|r] [_ HR]] Hprem.
  - exact (brule_over_sound r ps c HR Hprem).
  - exact (wrule_over_sound r ps c HR Hprem).
Qed.

Theorem HLB_complete : complete HLB.
Proof.
  apply exact_complete. eapply exact_mono; [| apply fwd_exact].
  intros ps c [r [_ HR]]. exists r. split; [exact I | exact HR].
Qed.

Theorem ILB_locally_sound : locally_sound ILB.
Proof.
  apply cl_locally_sound. intros ps c [[r|r] [[_ Hk] HR]] Hprem;
    [| contradiction].
  exact (brule_under_sound r ps c HR Hprem).
Qed.

Theorem ILB_complete : complete ILB.
Proof. apply (flip_complete (restrict HLB_C fwdB)), fwd_exact. Qed.

(** ** SIL⊥: complement, restrict to backward rules, flip *)

Definition SILB_C : CubeLogic ImpBot :=
  flip (restrict (complement_cl HLB_C) bwdB).
Definition SILB : ProgramLogic ImpBot := to_logic SILB_C.

Theorem SILB_locally_sound : locally_sound SILB.
Proof.
  apply cl_locally_sound.
  intros ps c [[r|r] [[_ Hk] [ps0 [c0 [HR [-> Hps]]]]]] Hprem;
    [contradiction |].
  change (cube_valid Backward Under (complement c0)).
  apply dual_sil_duality, (wrule_dual_sound r ps0 c0 HR).
  intros t Ht. apply dual_sil_duality, Hprem, Hps. exists t. auto.
Qed.

Theorem SILB_complete : complete SILB.
Proof.
  apply exact_complete.
  change (exact Backward (cl_base SILB_C)).
  eapply exact_mono; [| apply (complement_wlp_exact wbase wexactB)].
  intros ps c [ps0 [c0 [[r HR] [-> Hps]]]].
  exists (inr r). split; [split; exact I |].
  exists ps0, c0. auto.
Qed.

(** ** The other forward-reachable nodes *)

Definition postDB_under : ProgramLogic ImpBot :=
  run_edge (complement_edge Forward Plain Over) HLB.
Definition preDB_under : ProgramLogic ImpBot :=
  run_edge galois_hl_wlp HLB.
Definition NCB : ProgramLogic ImpBot :=
  run_edge galois_dimg_nc postDB_under.
Definition postDB_over : ProgramLogic ImpBot :=
  run_edge (complement_edge Forward Plain Under) ILB.
Definition preDB_over : ProgramLogic ImpBot :=
  run_edge (complement_edge Backward Plain Under) SILB.

Ltac edge_sound H :=
  apply run_edge_locally_sound; [intros; reflexivity | apply H].
Ltac edge_complete H :=
  apply run_edge_complete; [intros; reflexivity | apply H].

Theorem postDB_under_locally_sound : locally_sound postDB_under.
Proof. edge_sound HLB_locally_sound. Qed.
Theorem postDB_under_complete : complete postDB_under.
Proof. edge_complete HLB_complete. Qed.

Theorem preDB_under_locally_sound : locally_sound preDB_under.
Proof. edge_sound HLB_locally_sound. Qed.
Theorem preDB_under_complete : complete preDB_under.
Proof. edge_complete HLB_complete. Qed.

Theorem NCB_locally_sound : locally_sound NCB.
Proof. edge_sound postDB_under_locally_sound. Qed.
Theorem NCB_complete : complete NCB.
Proof. edge_complete postDB_under_complete. Qed.

Theorem postDB_over_locally_sound : locally_sound postDB_over.
Proof. edge_sound ILB_locally_sound. Qed.
Theorem postDB_over_complete : complete postDB_over.
Proof. edge_complete ILB_complete. Qed.

Theorem preDB_over_locally_sound : locally_sound preDB_over.
Proof. edge_sound SILB_locally_sound. Qed.
Theorem preDB_over_complete : complete preDB_over.
Proof. edge_complete SILB_complete. Qed.

(** Each bottom-face node's validity is the corresponding [cvalid] over
    [ImpBot]. *)
Lemma bottom_face_validity :
  (forall t, valid HLB t <-> cvalid Forward Plain Over t) /\
  (forall t, valid ILB t <-> cvalid Forward Plain Under t) /\
  (forall t, valid NCB t <-> cvalid Backward Plain Over t) /\
  (forall t, valid SILB t <-> cvalid Backward Plain Under t) /\
  (forall t, valid postDB_over t <-> cvalid Forward Dual Over t) /\
  (forall t, valid postDB_under t <-> cvalid Forward Dual Under t) /\
  (forall t, valid preDB_over t <-> cvalid Backward Dual Over t) /\
  (forall t, valid preDB_under t <-> cvalid Backward Dual Under t).
Proof. repeat split; intros; assumption. Qed.

(** ** Reading HL⊥: total and partial correctness *)

(** Lift a state predicate, excluding ⊥ or including it. *)
Definition onlyS (P : state -> Prop) : assertion ImpBot :=
  fun o => match o with Some s => P s | None => False end.
Definition orBot (Q : state -> Prop) : assertion ImpBot :=
  fun o => match o with Some s => Q s | None => True end.

Theorem HLB_total_iff : forall P c Q,
    valid HLB (hb (onlyS P) c (onlyS Q)) <->
    (forall s, P s -> (forall s', ceval c s s' -> Q s') /\ ~ diverges c s).
Proof.
  intros P c Q.
  change (valid HLB (hb (onlyS P) c (onlyS Q)))
    with (cube_valid Forward Over (hb (onlyS P) c (onlyS Q))).
  rewrite hl_valid_iff. split.
  - intros H s HP. split.
    + intros s' Hc. exact (H (Some s) (Some s') HP Hc).
    + intros Hd. exact (H (Some s) None HP Hd).
  - intros H [s|] [s'|] HP Hc; simpl in *;
      try contradiction; try (apply (proj1 (H s HP)); exact Hc).
    exact (proj2 (H s HP) Hc).
Qed.

Theorem HLB_partial_iff : forall P c Q,
    valid HLB (hb (onlyS P) c (orBot Q)) <-> hoare_valid P c Q.
Proof.
  intros P c Q.
  change (valid HLB (hb (onlyS P) c (orBot Q)))
    with (cube_valid Forward Over (hb (onlyS P) c (orBot Q))).
  rewrite hl_valid_iff. unfold hoare_valid. split.
  - intros H s s' HP Hc. exact (H (Some s) (Some s') HP Hc).
  - intros H [s|] [s'|] HP Hc; simpl in *; try contradiction; auto.
    exact (H s s' HP Hc).
Qed.

(** ** The top face cannot recover termination *)

Lemma while_true_no_exit : forall c s s', ~ ceval (CWhile BTrue c) s s'.
Proof.
  intros c s s' H. remember (CWhile BTrue c) as w eqn:Ew.
  induction H; inversion Ew; subst; [discriminate | auto].
Qed.

Definition maybe_loop : com := CChoice CSkip (CWhile BTrue CSkip).

Lemma maybe_loop_ceval : forall s s',
    ceval maybe_loop s s' <-> ceval CSkip s s'.
Proof.
  intros s s'. split; intros H.
  - inversion H; subst; [assumption |].
    exfalso. eapply while_true_no_exit; eassumption.
  - apply E_ChoiceL, H.
Qed.

Theorem termination_not_recoverable :
  (forall d p a (P Q : assertion Imp),
     cvalid d p a (@mkTriple Imp P CSkip Q) <->
     cvalid d p a (@mkTriple Imp P maybe_loop Q)) /\
  valid HLB (hb (onlyS (fun _ => True)) CSkip (onlyS (fun _ => True))) /\
  ~ valid HLB (hb (onlyS (fun _ => True)) maybe_loop
                  (onlyS (fun _ => True))).
Proof.
  split; [| split].
  - intros d p a P Q. apply cvalid_sem_ext.
    intros s s'. simpl. split; apply maybe_loop_ceval.
  - apply HLB_total_iff. intros s _. split; [auto | apply diverges_skip].
  - rewrite HLB_total_iff. intros H.
    apply (proj2 (H empty_state I)).
    apply Dv_ChoiceR, loop_forever.
Qed.
