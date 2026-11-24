(** * Verified logic records for core languages: any node to any node

    For a core language (atoms with relation [act_sem]):

    - [gen_top rel Hrel d p a] and [gen_bot rel Hrel d p a] build a
      [VLogic] at any node of either face from a relation [rel] for the
      atoms that agrees with the semantics ([Hrel]). They use the
      generated HL/IL/SIL and the generic edges.
    - [rel_top V] and [rel_bot V] read the atoms' relation off the
      *derivations* of any record [V], at any node. For example, at IL
      [a] relates [s] to [s'] iff [V] derives [[{s}] a [{s'}]].
      [rel_top_correct] and [rel_bot_correct] show it is the semantics.
    - [vto V d p a] (top to top), [vto_bot] (top to bottom), [vfrom_bot]
      (bottom to top) and [vbot_to] (bottom to bottom): verified
      transformers from any record to a record at any node. They
      regenerate rules from the relation recovered from [V].

    Top to bottom is possible here despite [termination_not_recoverable]:
    that result concerns the theory of *individual programs*. For a
    structural language, the theory of the *atoms* plus the language's
    known structure determines every program's divergence. *)

From Stdlib Require Import Classical.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube CubeLogic Transformer Verified.
From LogicTransformers.Transformers Require Import Flip Complement Galois.
From LogicTransformers.Core Require Import
  Kernel KernelBot Generate GenerateBot CoreCube.

Section VCore.

Context {Σ Act : Type} (act_sem : Act -> Σ -> Σ -> Prop).

Notation T := (KLang act_sem).
Notation B := (KLangB act_sem).
Notation REL := (Act -> Σ -> Σ -> Prop).

Definition agrees (rel : REL) : Prop :=
  forall a s s', rel a s s' <-> act_sem a s s'.

(** ** Generated base records, top face *)

Definition vgenHL (rel : REL) (H : agrees rel) : VLogic T Forward Plain Over :=
  @mkVLogic T Forward Plain Over
    (to_logic (GHL act_sem rel)) (fun t => iff_refl _)
    (cl_locally_sound _ (GHL_base_sound act_sem rel H))
    (GHL_complete act_sem rel H).

Definition vgenIL (rel : REL) (H : agrees rel) : VLogic T Forward Plain Under :=
  @mkVLogic T Forward Plain Under
    (to_logic (GIL act_sem rel)) (fun t => iff_refl _)
    (cl_locally_sound _ (GIL_base_sound act_sem rel H))
    (GIL_complete act_sem rel H).

Definition vgenSIL (rel : REL) (H : agrees rel)
  : VLogic T Backward Plain Under :=
  @mkVLogic T Backward Plain Under
    (to_logic (GSIL act_sem rel)) (fun t => iff_refl _)
    (cl_locally_sound _ (GSIL_base_sound act_sem rel H))
    (GSIL_complete act_sem rel H).

(** ** Generated base records, bottom face *)

Definition bpoolR (rel : REL) (r : cname) : ruleset B :=
  match r with
  | inl g => @fwdB_rule Σ Act act_sem rel g
  | inr g => @bwdB_rule Σ Act act_sem rel g
  end.

Definition bHLR rel : CubeLogic B :=
  mkCubeLogic Forward Over cname (bpoolR rel) (fun _ => True).
Definition bILR rel : CubeLogic B := flip (restrict (bHLR rel) is_fwd).
Definition bSILR rel : CubeLogic B :=
  flip (restrict (complement_cl (bHLR rel)) is_bwd).

Section BotRel.

Variable rel : REL.
Hypothesis H : agrees rel.

Lemma bHLR_base_sound : base_sound (bHLR rel).
Proof.
  intros ps c [[g|g] [_ HR]] Hprem.
  - exact (fwdB_over_sound act_sem rel H g ps c HR Hprem).
  - exact (bwdB_over_sound act_sem rel H g ps c HR Hprem).
Qed.

Lemma bHLR_fwd_exact : exact Forward (cl_base (restrict (bHLR rel) is_fwd)).
Proof.
  intros P c. eapply derivable_mono; [| apply (fwdB_exact act_sem rel H)].
  intros ps c' [g HR]. exists (inl g). split; [split; exact I | exact HR].
Qed.

Lemma bHLR_complete : complete (to_logic (bHLR rel)).
Proof.
  apply exact_complete. eapply exact_mono; [| apply bHLR_fwd_exact].
  intros ps c [r [_ HR]]. exists r. split; [exact I | exact HR].
Qed.

Lemma bILR_base_sound : base_sound (bILR rel).
Proof.
  intros ps c [[g|g] [[_ Hk] HR]] Hprem; [| contradiction].
  exact (fwdB_under_sound act_sem rel H g ps c HR Hprem).
Qed.

Lemma bILR_complete : complete (to_logic (bILR rel)).
Proof. apply (flip_complete (restrict (bHLR rel) is_fwd)), bHLR_fwd_exact. Qed.

Lemma bSILR_base_sound : base_sound (bSILR rel).
Proof.
  intros ps c [[g|g] [[_ Hk] [ps0 [c0 [HR [-> Hps]]]]]] Hprem;
    [contradiction |].
  change (cube_valid Backward Under (complement c0)).
  apply dual_sil_duality, (bwdB_dual_sound act_sem rel H g ps0 c0 HR).
  intros t Ht. apply dual_sil_duality, Hprem, Hps. exists t. auto.
Qed.

Lemma bSILR_complete : complete (to_logic (bSILR rel)).
Proof.
  apply exact_complete. change (exact Backward (cl_base (bSILR rel))).
  eapply exact_mono;
    [| apply complement_wlp_exact; intros c Q;
       apply (bwdB_exact act_sem rel H)].
  intros ps c [ps0 [c0 [[g HR] [-> Hps]]]].
  exists (inr g). split; [split; exact I |]. exists ps0, c0. auto.
Qed.

End BotRel.

Definition vgenHLb (rel : REL) (H : agrees rel)
  : VLogic B Forward Plain Over :=
  @mkVLogic B Forward Plain Over (to_logic (bHLR rel)) (fun t => iff_refl _)
    (cl_locally_sound _ (bHLR_base_sound rel H)) (bHLR_complete rel H).

Definition vgenILb (rel : REL) (H : agrees rel)
  : VLogic B Forward Plain Under :=
  @mkVLogic B Forward Plain Under (to_logic (bILR rel)) (fun t => iff_refl _)
    (cl_locally_sound _ (bILR_base_sound rel H)) (bILR_complete rel H).

Definition vgenSILb (rel : REL) (H : agrees rel)
  : VLogic B Backward Plain Under :=
  @mkVLogic B Backward Plain Under (to_logic (bSILR rel)) (fun t => iff_refl _)
    (cl_locally_sound _ (bSILR_base_sound rel H)) (bSILR_complete rel H).

(** ** Any node from a base: generation plus edges *)

Definition gen_any {L} (vHL : VLogic L Forward Plain Over)
    (vIL : VLogic L Forward Plain Under)
    (vSIL : VLogic L Backward Plain Under) d p a : VLogic L d p a :=
  match d as d0, p as p0, a as a0 return VLogic L d0 p0 a0 with
  | Forward, Plain, Over => vHL
  | Forward, Dual, Under => vcomplement_FPO vHL
  | Backward, Plain, Over => vgalois_dimg_nc (vcomplement_FPO vHL)
  | Backward, Dual, Under => vgalois_hl vHL
  | Forward, Plain, Under => vIL
  | Forward, Dual, Over => vcomplement_FPU vIL
  | Backward, Plain, Under => vSIL
  | Backward, Dual, Over => vcomplement_BPU vSIL
  end.

Definition gen_top rel (H : agrees rel) d p a : VLogic T d p a :=
  gen_any (vgenHL rel H) (vgenIL rel H) (vgenSIL rel H) d p a.

Definition gen_bot rel (H : agrees rel) d p a : VLogic B d p a :=
  gen_any (vgenHLb rel H) (vgenILb rel H) (vgenSILb rel H) d p a.

(** ** Reading the atoms off any record *)

Notation kt := (@mkTriple T).
Notation kbt := (@mkTriple B).

(** From a record at each class's representative node. *)
Definition relHL (V : VLogic T Forward Plain Over) : REL := fun a s s' =>
  ~ derivable (rules (vl_logic V))
      (kt (fun x => x = s) (KAct a) (fun y => y <> s')).
Definition relIL (V : VLogic T Forward Plain Under) : REL := fun a s s' =>
  derivable (rules (vl_logic V))
    (kt (fun x => x = s) (KAct a) (fun y => y = s')).
Definition relSIL (V : VLogic T Backward Plain Under) : REL := fun a s s' =>
  derivable (rules (vl_logic V))
    (kt (fun x => x = s) (KAct a) (fun y => y = s')).

Lemma relHL_ok : forall V, agrees (relHL V).
Proof.
  intros V a s s'. unfold relHL. rewrite (vl_theory V).
  cbn [cvalid].
  rewrite hl_valid_iff. simpl. split.
  - intros Hn. apply NNPP. intros Hna. apply Hn.
    intros x y -> Hc Heq. subst. inversion Hc; subst. contradiction.
  - intros Ha Hall. exact (Hall s s' eq_refl (KE_Act _ _ _ _ Ha) eq_refl).
Qed.

Lemma relIL_ok : forall V, agrees (relIL V).
Proof.
  intros V a s s'. unfold relIL. rewrite (vl_theory V).
  cbn [cvalid].
  rewrite il_valid_iff. simpl. split.
  - intros Hv. destruct (Hv s' eq_refl) as [x [-> Hc]].
    inversion Hc; subst. assumption.
  - intros Ha y ->. exists s. split; [reflexivity | apply KE_Act, Ha].
Qed.

Lemma relSIL_ok : forall V, agrees (relSIL V).
Proof.
  intros V a s s'. unfold relSIL. rewrite (vl_theory V).
  cbn [cvalid].
  rewrite sil_valid_iff. simpl. split.
  - intros Hv. destruct (Hv s eq_refl) as [y [Hc ->]].
    inversion Hc; subst. assumption.
  - intros Ha x ->. exists s'. split; [apply KE_Act, Ha | reflexivity].
Qed.

Definition relHLb (V : VLogic B Forward Plain Over) : REL := fun a s s' =>
  ~ derivable (rules (vl_logic V))
      (kbt (fun o => o = Some s) (KAct a) (fun o => o <> Some s')).
Definition relILb (V : VLogic B Forward Plain Under) : REL := fun a s s' =>
  derivable (rules (vl_logic V))
    (kbt (fun o => o = Some s) (KAct a) (fun o => o = Some s')).
Definition relSILb (V : VLogic B Backward Plain Under) : REL := fun a s s' =>
  derivable (rules (vl_logic V))
    (kbt (fun o => o = Some s) (KAct a) (fun o => o = Some s')).

Lemma relHLb_ok : forall V, agrees (relHLb V).
Proof.
  intros V a s s'. unfold relHLb. rewrite (vl_theory V).
  cbn [cvalid].
  rewrite hl_valid_iff. simpl. split.
  - intros Hn. apply NNPP. intros Hna. apply Hn.
    intros o o' -> Hc Heq. subst. apply semKB_act in Hc. contradiction.
  - intros Ha Hall.
    exact (Hall (Some s) (Some s') eq_refl (KE_Act _ _ _ _ Ha) eq_refl).
Qed.

Lemma relILb_ok : forall V, agrees (relILb V).
Proof.
  intros V a s s'. unfold relILb. rewrite (vl_theory V).
  cbn [cvalid].
  rewrite il_valid_iff. simpl. split.
  - intros Hv. destruct (Hv (Some s') eq_refl) as [o [-> Hc]].
    apply semKB_act in Hc. exact Hc.
  - intros Ha o ->. exists (Some s). split; [reflexivity |].
    apply semKB_act. exact Ha.
Qed.

Lemma relSILb_ok : forall V, agrees (relSILb V).
Proof.
  intros V a s s'. unfold relSILb. rewrite (vl_theory V).
  cbn [cvalid].
  rewrite sil_valid_iff. simpl. split.
  - intros Hv. destruct (Hv (Some s) eq_refl) as [o [Hc ->]].
    apply semKB_act in Hc. exact Hc.
  - intros Ha o ->. exists (Some s'). split; [| reflexivity].
    apply semKB_act. exact Ha.
Qed.

(** From a record at any node: move to the class representative with
    the generic edges, then read off. *)
Definition rel_any {L} (rHL : VLogic L Forward Plain Over -> REL)
    (rIL : VLogic L Forward Plain Under -> REL)
    (rSIL : VLogic L Backward Plain Under -> REL)
    d p a : VLogic L d p a -> REL :=
  match d as d0, p as p0, a as a0 return VLogic L d0 p0 a0 -> REL with
  | Forward, Plain, Over => fun V => rHL V
  | Forward, Dual, Under => fun V =>
      rHL (vgalois_wlp_hl (vcomplement (vgalois_dimg_nc V)))
  | Backward, Plain, Over => fun V =>
      rHL (vgalois_wlp_hl (vcomplement V))
  | Backward, Dual, Under => fun V => rHL (vgalois_wlp_hl V)
  | Forward, Plain, Under => fun V => rIL V
  | Forward, Dual, Over => fun V => rIL (vcomplement_FDO V)
  | Backward, Plain, Under => fun V => rSIL V
  | Backward, Dual, Over => fun V => rSIL (vcomplement_BDO V)
  end.

Definition rel_top {d p a} (V : VLogic T d p a) : REL :=
  rel_any relHL relIL relSIL d p a V.
Definition rel_bot {d p a} (V : VLogic B d p a) : REL :=
  rel_any relHLb relILb relSILb d p a V.

Lemma rel_top_correct : forall d p a (V : VLogic T d p a), agrees (rel_top V).
Proof.
  intros [] [] [] V; unfold rel_top; simpl;
    first [apply relHL_ok | apply relIL_ok | apply relSIL_ok].
Qed.

Lemma rel_bot_correct : forall d p a (V : VLogic B d p a), agrees (rel_bot V).
Proof.
  intros [] [] [] V; unfold rel_bot; simpl;
    first [apply relHLb_ok | apply relILb_ok | apply relSILb_ok].
Qed.

(** ** Any node to any node *)

Definition vto {d p a} (V : VLogic T d p a) d' p' a' : VLogic T d' p' a' :=
  gen_top (rel_top V) (rel_top_correct d p a V) d' p' a'.

Definition vto_bot {d p a} (V : VLogic T d p a) d' p' a' : VLogic B d' p' a' :=
  gen_bot (rel_top V) (rel_top_correct d p a V) d' p' a'.

Definition vfrom_bot {d p a} (V : VLogic B d p a) d' p' a'
  : VLogic T d' p' a' :=
  gen_top (rel_bot V) (rel_bot_correct d p a V) d' p' a'.

Definition vbot_to {d p a} (V : VLogic B d p a) d' p' a'
  : VLogic B d' p' a' :=
  gen_bot (rel_bot V) (rel_bot_correct d p a V) d' p' a'.

(** A starting record: HL generated from the semantics itself. *)
Lemma agrees_sem : agrees act_sem.
Proof. intros a s s'. split; auto. Qed.

Definition start_HL : VLogic T Forward Plain Over :=
  vgenHL act_sem agrees_sem.

End VCore.
