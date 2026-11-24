(** * The vertical edge: forgetting nontermination (bottom → top)

    [forget] restricts a bottom-face triple (over [ImpBot]) to proper
    states, giving a top-face triple (over [Imp]). This is Cousot's
    termination abstraction applied to triples.

    - [forget_reflects]: bottom validity implies top validity of the
      forgotten triple at six of the eight nodes, including every
      [Plain] node except SIL. [forget_not_reflecting_SIL] fails at SIL:
      "some run from P reaches Q" can be witnessed by divergence, which
      forgetting throws away. (The same happens at p̃re ⊆, its
      complement.)
    - [forget_cl] maps a cube logic's rules through [forget], keeping only
      instances whose premises are ⊥-determined (their bottom validity
      follows from the top validity of their forgotten form). For a sound
      source no derivation is lost ([derivable_filtered]).
    - At reflecting nodes [forget_cl] preserves soundness
      ([forget_cl_base_sound]). At forward nodes it preserves completeness
      when the source is exact ([forget_cl_complete]). Instances: HL and IL
      on the top face are obtained from HL⊥ and IL⊥.
    - [forget_SIL_unsound]: at SIL the transformer is unsound. *)

From Stdlib Require Import Classical.
From LogicTransformers.Imp Require Import Syntax BigStep Diverge Lang LangBot.
From LogicTransformers.Logics Require Import Hoare BotRules BotWlpRules
  BottomFace.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube CubeLogic Transformer.
From LogicTransformers.Transformers Require Import Flip Complement.

Definition down (P : assertion ImpBot) : assertion Imp := fun s => P (Some s).

Definition forget (t : triple ImpBot) : triple Imp :=
  @mkTriple Imp (down (pre t)) (cmd t) (down (post t)).

Lemma forget_proper : respects_equiv forget.
Proof.
  intros [P c Q] [P' c' Q'] [HP [Hc HQ]]. simpl in *.
  split; [intros s; apply HP | split; [exact Hc | intros s; apply HQ]].
Qed.

(** ** Which nodes forgetting respects *)

Definition reflecting (d : direction) (a : approximation) : Prop :=
  match d, a with Backward, Under => False | _, _ => True end.

Theorem forget_reflects : forall d a t,
    reflecting d a -> cube_valid d a t -> cube_valid d a (forget t).
Proof.
  intros d a [P c Q] Hr V.
  destruct d, a; simpl in *; try contradiction;
    unfold aimpl, img, preimg, down in *; simpl in *.
  - intros s' [s [HP Hc]]. apply (V (Some s')). exists (Some s). auto.
  - intros s' HQ. destruct (V (Some s') HQ) as [[s|] [HP Hc]];
      [exists s; auto | contradiction].
  - intros s [s' [Hc HQ]]. apply (V (Some s)). exists (Some s'). auto.
Qed.

Theorem forget_not_reflecting_SIL :
  exists t, cube_valid Backward Under t /\
            ~ cube_valid Backward Under (forget t).
Proof.
  exists (hb (fun o => exists s, o = Some s) (CWhile BTrue CSkip)
             (fun o => o = None)).
  split.
  - apply sil_valid_iff. intros [s|] [s0 Hs]; [| discriminate].
    exists None. split; [apply loop_forever | reflexivity].
  - intros H. apply sil_valid_iff in H.
    destruct (H empty_state (ex_intro _ empty_state eq_refl))
      as [s' [_ Hs']].
    discriminate.
Qed.

(** ** The transformer *)

Definition determined (d : direction) (a : approximation)
    (t : triple ImpBot) : Prop :=
  cube_valid d a (forget t) -> cube_valid d a t.

Definition kept_det (C : CubeLogic ImpBot) (r : cl_rule C) : ruleset ImpBot :=
  fun ps c => cl_pool C r ps c /\
              forall t, ps t -> determined (cl_dir C) (cl_approx C) t.

Definition forget_cl (C : CubeLogic ImpBot) : CubeLogic Imp :=
  mkCubeLogic (cl_dir C) (cl_approx C) (cl_rule C)
    (fun r => map_rules forget (kept_det C r)) (cl_keep C).

Theorem forget_cl_base_sound : forall C,
    reflecting (cl_dir C) (cl_approx C) ->
    base_sound C -> base_sound (forget_cl C).
Proof.
  intros C Hr HB ps c [r [Hk [ps0 [c0 [[HR Hdet] [-> Hps]]]]]] Hprem.
  simpl in *. apply forget_reflects; [exact Hr |].
  apply (HB ps0 c0); [exists r; auto |].
  intros t Ht. apply Hdet; [exact Ht |].
  apply Hprem, Hps. exists t. auto.
Qed.

(** For a sound source, filtering to ⊥-determined premises loses no
    derivation: every premise in a derivation is derivable, hence valid,
    hence determined. *)
Lemma derivable_filtered : forall C, base_sound C ->
    forall t, derivable (cl_base C) t ->
    derivable (fun ps c => exists r, cl_keep C r /\ kept_det C r ps c) t.
Proof.
  intros C HB t D.
  induction D as [ps c [r [Hk HR]] Hps IH | t t' D IH He].
  - apply D_Rule with ps; [| exact IH].
    exists r. split; [exact Hk |]. split; [exact HR |].
    intros t Ht _. exact (base_derivable_valid C HB t (Hps t Ht)).
  - eapply D_Equiv; eauto.
Qed.

Lemma forget_cl_derivable : forall C, base_sound C ->
    forall t, derivable (cl_base C) t ->
    derivable (cl_base (forget_cl C)) (forget t).
Proof.
  intros C HB t D.
  pose proof (derivable_map forget _ forget_proper _
                (derivable_filtered C HB t D)) as D'.
  eapply derivable_mono; [| exact D'].
  intros ps c [ps0 [c0 [[r [Hk HK]] [-> Hps]]]].
  exists r. split; [exact Hk |]. exists ps0, c0. auto.
Qed.

Theorem forget_cl_complete : forall C,
    cl_dir C = Forward -> base_sound C -> exact Forward (cl_base C) ->
    complete (to_logic (forget_cl C)).
Proof.
  intros C Hd HB Hex. apply exact_complete.
  change (exact (cl_dir C) (cl_base (forget_cl C))). rewrite Hd.
  intros P c.
  set (P0 := fun o : ostate => match o with Some s => P s | None => False end).
  eapply D_Equiv; [apply (forget_cl_derivable C HB), (Hex P0 c) |].
  simpl. split; [| split; [reflexivity |]]; intros s; unfold down; simpl.
  - split; auto.
  - unfold img. simpl. split.
    + intros [[s0|] [HP Hc]]; [exists s0; auto | contradiction].
    + intros [s0 [HP Hc]]. exists (Some s0). auto.
Qed.

(** ** Instances: the top face's HL and IL from the bottom face *)

Lemma HLB_base_sound : base_sound HLB_C.
Proof. apply locally_sound_base, HLB_locally_sound. Qed.

Lemma ILB_base_sound : base_sound (flip (restrict HLB_C fwdB)).
Proof. apply locally_sound_base, ILB_locally_sound. Qed.

Lemma HLB_base_exact : exact Forward (cl_base HLB_C).
Proof.
  eapply exact_mono; [| apply fwd_exact].
  intros ps c [r [_ HR]]. exists r. split; [exact I | exact HR].
Qed.

Definition HL_from_bot : ProgramLogic Imp := to_logic (forget_cl HLB_C).
Definition IL_from_bot : ProgramLogic Imp :=
  to_logic (forget_cl (flip (restrict HLB_C fwdB))).

Theorem HL_from_bot_locally_sound : locally_sound HL_from_bot.
Proof.
  apply cl_locally_sound, forget_cl_base_sound, HLB_base_sound. exact I.
Qed.

Theorem HL_from_bot_complete : complete HL_from_bot.
Proof.
  apply forget_cl_complete; [reflexivity | apply HLB_base_sound |].
  apply HLB_base_exact.
Qed.

Theorem IL_from_bot_locally_sound : locally_sound IL_from_bot.
Proof.
  apply cl_locally_sound, forget_cl_base_sound, ILB_base_sound. exact I.
Qed.

Theorem IL_from_bot_complete : complete IL_from_bot.
Proof.
  apply forget_cl_complete; [reflexivity | apply ILB_base_sound |].
  apply fwd_exact.
Qed.

(** NC is also a reflecting node, so forgetting the bottom NC is sound. *)
Theorem NC_from_bot_locally_sound :
  locally_sound (to_logic (forget_cl (complement_cl HLB_C))).
Proof.
  apply cl_locally_sound, forget_cl_base_sound; [exact I |].
  apply complement_cl_base_sound; [reflexivity | reflexivity |].
  apply HLB_base_sound.
Qed.

(** ** At SIL the transformer is unsound *)

Theorem forget_SIL_unsound : ~ sound (to_logic (forget_cl SILB_C)).
Proof.
  intros Hs.
  assert (Hex : exact Backward (cl_base SILB_C)).
  { eapply exact_mono; [| apply (complement_wlp_exact wbase wexactB)].
    intros ps c [ps0 [c0 [[r HR] [-> Hps]]]].
    exists (inr r). split; [split; exact I |]. exists ps0, c0. auto. }
  set (c := CWhile BTrue CSkip).
  set (Q := fun o : ostate => o = None).
  pose proof (forget_cl_derivable SILB_C
                (locally_sound_base _ SILB_locally_sound) _ (Hex Q c)) as D.
  assert (V := Hs _ (derivable_mono _ _ (fun ps c Hb => or_introl Hb) _ D)).
  change (cube_valid Backward Under
            (forget (hb (@preimg ImpBot c Q) c Q))) in V.
  apply sil_valid_iff in V.
  destruct (V empty_state) as [s' [_ Hs']].
  - exists None. split; [apply loop_forever | reflexivity].
  - discriminate.
Qed.
