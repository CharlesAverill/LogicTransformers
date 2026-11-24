(** * Crossing IL ⟷ SIL by regenerating rules

    IL and SIL sit in different classes of the cube: no mapping or selection
    of rules connects them, because IL's forward rules and SIL's (complements
    of) backward rules are each missing from the other presentation. These
    transformers cross anyway, in three steps:

    1. read the atoms' relation off the *source logic's derivations*:
       [a] relates [s] to [s'] iff the source derives [{s} a {s'}]
       ([rel_of]);
    2. generate the missing rules from that relation ([Core.Generate]) and
       add them ([augment]);
    3. move with the existing edges (flip, complement, restrict).

    [il_to_sil_correct] and [sil_to_il_correct]: from any sound and
    complete IL (resp. SIL) logic on the core language, the result is a
    sound and complete SIL (resp. IL) logic.

    The transformers use the source only through its derivable singleton
    triples: the restriction to the generated rules discards all of the
    source's own rules. That is forced here. Complemented IL rules (forward
    assignment) are not SIL-sound, so they cannot be kept, and the
    information that crosses is the source's theory, not its rules. *)

From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube CubeLogic Transformer.
From LogicTransformers.Transformers Require Import Flip Complement Augment.
From LogicTransformers.Core Require Import Kernel Generate CoreCube.

Section Regenerate.

Context {Σ Act : Type} (act_sem : Act -> Σ -> Σ -> Prop).

Notation L := (KLang act_sem).
Notation kt := (@mkTriple L).

(** ** Reading the atoms off a logic *)

Definition rel_of (C : CubeLogic L) : Act -> Σ -> Σ -> Prop :=
  fun a s s' =>
    derivable (cl_rules C) (kt (fun x => x = s) (KAct a) (fun y => y = s')).

Lemma singleton_IL : forall a s s',
    cube_valid Forward Under (kt (fun x => x = s) (KAct a) (fun y => y = s'))
    <-> act_sem a s s'.
Proof.
  intros a s s'. rewrite il_valid_iff. simpl. split.
  - intros H. destruct (H s' eq_refl) as [x [-> Hx]].
    inversion Hx; subst. assumption.
  - intros H y ->. exists s. split; [reflexivity | apply KE_Act, H].
Qed.

Lemma singleton_SIL : forall a s s',
    cube_valid Backward Under (kt (fun x => x = s) (KAct a) (fun y => y = s'))
    <-> act_sem a s s'.
Proof.
  intros a s s'. rewrite sil_valid_iff. simpl. split.
  - intros H. destruct (H s eq_refl) as [y [Hy ->]].
    inversion Hy; subst. assumption.
  - intros H x ->. exists s'. split; [apply KE_Act, H | reflexivity].
Qed.

Lemma rel_of_correct : forall C,
    (forall a s s',
       cube_valid (cl_dir C) (cl_approx C)
         (kt (fun x => x = s) (KAct a) (fun y => y = s')) <->
       act_sem a s s') ->
    sound (to_logic C) -> complete (to_logic C) ->
    forall a s s', rel_of C a s s' <-> act_sem a s s'.
Proof.
  intros C Hsing HS HC a s s'. unfold rel_of. rewrite <- Hsing. split.
  - apply HS.
  - apply HC.
Qed.

(** ** IL → SIL *)

Definition il_to_sil (C : CubeLogic L) : CubeLogic L :=
  flip (restrict
          (complement_cl
             (augment (flip C) (@bwd_rule Σ Act act_sem (rel_of C))))
          only_new).

Theorem il_to_sil_correct : forall C,
    cl_dir C = Forward -> cl_approx C = Under ->
    sound (to_logic C) -> complete (to_logic C) ->
    locally_sound (to_logic (il_to_sil C)) /\ complete (to_logic (il_to_sil C)).
Proof.
  intros C Hd Ha HS HC.
  assert (Hrel : forall a s s', rel_of C a s s' <-> act_sem a s s').
  { apply rel_of_correct; [| exact HS | exact HC].
    rewrite Hd, Ha. apply singleton_IL. }
  destruct C as [d a N pool keep]. simpl in Hd, Ha. subst.
  split.
  - apply cl_locally_sound.
    intros ps c [[r|g] [[_ Hk] [ps0 [c0 [HR [-> Hps]]]]]] Hprem;
      [contradiction |].
    change (cube_valid Backward Under (complement c0)).
    apply dual_sil_duality, (bwd_dual_sound act_sem _ Hrel g ps0 c0 HR).
    intros t Ht. apply dual_sil_duality, Hprem, Hps. exists t. auto.
  - apply exact_complete.
    eapply exact_mono;
      [| apply (complement_wlp_exact _ (bwd_exact act_sem _ Hrel))].
    intros ps c [ps0 [c0 [[g HR] [-> Hps]]]].
    exists (inr g). split; [split; exact I |]. exists ps0, c0. auto.
Qed.

(** ** SIL → IL *)

Definition sil_to_il (C : CubeLogic L) : CubeLogic L :=
  flip (restrict
          (augment (complement_cl (flip C))
             (@fwd_rule Σ Act act_sem (rel_of C)))
          only_new).

Theorem sil_to_il_correct : forall C,
    cl_dir C = Backward -> cl_approx C = Under ->
    sound (to_logic C) -> complete (to_logic C) ->
    locally_sound (to_logic (sil_to_il C)) /\ complete (to_logic (sil_to_il C)).
Proof.
  intros C Hd Ha HS HC.
  assert (Hrel : forall a s s', rel_of C a s s' <-> act_sem a s s').
  { apply rel_of_correct; [| exact HS | exact HC].
    rewrite Hd, Ha. apply singleton_SIL. }
  destruct C as [d a N pool keep]. simpl in Hd, Ha. subst.
  split.
  - apply cl_locally_sound.
    intros ps c [[r|g] [[_ Hk] HR]] Hprem; [contradiction |].
    exact (fwd_under_sound act_sem _ Hrel g ps c HR Hprem).
  - apply exact_complete.
    change (exact Forward
              (cl_base (sil_to_il (mkCubeLogic Backward Under N pool keep)))).
    eapply exact_mono; [| intros P c; apply (fwd_exact act_sem _ Hrel)].
    intros ps c [g HR]. exists (inr g). split; [split; exact I | exact HR].
Qed.

(** ** Round trip on the generated logics

    Starting from the generated IL, going to SIL and back gives a sound and
    complete IL again. *)
Corollary il_sil_il : forall rel,
    (forall a s s', rel a s s' <-> act_sem a s s') ->
    let C := sil_to_il (il_to_sil (GIL act_sem rel)) in
    locally_sound (to_logic C) /\ complete (to_logic C).
Proof.
  intros rel Hrel C.
  destruct (il_to_sil_correct (GIL act_sem rel) eq_refl eq_refl
              (locally_sound_sound _
                 (cl_locally_sound _ (GIL_base_sound act_sem rel Hrel)))
              (GIL_complete act_sem rel Hrel)) as [HS HC].
  apply sil_to_il_correct; [reflexivity | reflexivity | | exact HC].
  apply locally_sound_sound, HS.
Qed.

End Regenerate.
