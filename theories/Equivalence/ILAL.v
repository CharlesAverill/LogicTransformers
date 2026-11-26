(** * Interleaved adversarial logic: ILAL's rules and the generated logic

    ILAL proves victim-against-adversary judgments with an interleaved
    proof system. Its judgment [P |- (c1, c2) ~> (d1, d2) Q] says every
    [Q] state is reached from a [P] state by an interleaving run from
    residuals [(c1, c2)] to [(d1, d2)]. [ilal] states its rules over this
    development's single state record (both halves in one record, so no
    separate frame for the other side):

    - reflexivity, transitivity, consequence, infinitary disjunction;
    - a step of either side, by a single-thread one-step judgment
      [sderiv] whose atom and [assume] steps are Vanegue's single-thread
      rules ([Equivalence.Vanegue]);
    - a channel transfer.

    [ilal_sound], [ilal_complete]: sound and complete for interleaved
    adversarial validity. [ilal_iff_generated]: it proves exactly what
    the generated interleaved logic proves. Completeness follows each
    target state's run one step at a time and joins the runs by
    infinitary disjunction, as ILAL's proof does. *)

From Stdlib Require Import String List NArith Classical.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Verified.
From LogicTransformers.Core Require Import Kernel Rules StepCore.
From LogicTransformers.Adversarial Require Import AL Interleaving.
From LogicTransformers.Equivalence Require Import Vanegue.

(** ** One step of one thread *)

Inductive sderiv (m : mode) :
    (estate -> Prop) -> tcom -> tcom -> (estate -> Prop) -> Prop :=
  | SD_Atom : forall P a Q,
      van m P (TAtom a) Q -> sderiv m P (TAtom a) TSkip Q
  | SD_Assume : forall P B Q,
      van m P (TAssume B) Q -> sderiv m P (TAssume B) TSkip Q
  | SD_SeqSkip : forall P c, sderiv m P (TSeq TSkip c) c P
  | SD_SeqStep : forall P Q c1 c1' c2,
      sderiv m P c1 c1' Q -> sderiv m P (TSeq c1 c2) (TSeq c1' c2) Q
  | SD_ChoiceL : forall P c1 c2, sderiv m P (TChoice c1 c2) c1 P
  | SD_ChoiceR : forall P c1 c2, sderiv m P (TChoice c1 c2) c2 P
  | SD_Star0 : forall P c, sderiv m P (TStar c) TSkip P
  | SD_StarN : forall P c, sderiv m P (TStar c) (TSeq c (TStar c)) P
  | SD_Local : forall P x e c,
      sderiv m P (TLocal x e c)
        (TSeq (TAtom (AAsgn x e)) (TSeq c (TAtom (ARand x)))) P
  | SD_Cons : forall P P' Q Q' c c',
      (forall σ, P σ -> P' σ) -> (forall σ, Q' σ -> Q σ) ->
      sderiv m P c c' Q -> sderiv m P' c c' Q'.

Lemma sderiv_sound : forall m P c c' Q, sderiv m P c c' Q ->
    forall σ', Q σ' -> exists σ, P σ /\ tstep m (c, σ) (c', σ').
Proof.
  intros m P c c' Q H. induction H; intros σ' HQ.
  - destruct (van_sound _ _ _ _ H σ' HQ) as [σ [HP Hk]].
    inversion Hk; subst. exists σ.
    split; [exact HP | apply TS_Atom; assumption].
  - destruct (van_sound _ _ _ _ H σ' HQ) as [σ [HP Hk]].
    inversion Hk; subst. exists σ'.
    split; [exact HP | apply TS_Assume; assumption].
  - exists σ'. split; [exact HQ | apply TS_SeqSkip].
  - destruct (IHsderiv σ' HQ) as [σ [HP Hs]].
    exists σ. split; [exact HP | apply TS_Seq, Hs].
  - exists σ'. split; [exact HQ | apply TS_ChoiceL].
  - exists σ'. split; [exact HQ | apply TS_ChoiceR].
  - exists σ'. split; [exact HQ | apply TS_Star0].
  - exists σ'. split; [exact HQ | apply TS_StarN].
  - exists σ'. split; [exact HQ | apply TS_Local].
  - destruct (IHsderiv σ' (H0 σ' HQ)) as [σ [HP Hs]].
    exists σ. split; [apply H, HP | exact Hs].
Qed.

Ltac fix_pt :=
  match goal with |- sderiv ?m (only ?a) _ _ (only ?b) =>
    apply (SD_Cons m (only a) (only a) (only a) (only b));
    [auto | intros y E; unfold only in *; subst; reflexivity | ] end.

(** Every single step, from a single state. *)
Lemma sderiv_step : forall m c c' σ σ', tstep m (c, σ) (c', σ') ->
    sderiv m (only σ) c c' (only σ').
Proof.
  intros m c c' σ σ' H.
  remember (c, σ) as k eqn:Ek. remember (c', σ') as k' eqn:Ek'.
  revert c c' σ σ' Ek Ek'.
  induction H; intros c0 c0' σ0 σ0' Ek Ek';
    injection Ek; injection Ek'; intros; subst.
  - apply SD_Atom, van_complete. intros x E. unfold only in E. subst x.
    exists σ0. split; [reflexivity | apply KE_Act; assumption].
  - apply SD_Assume, van_complete. intros x E. unfold only in E. subst x.
    exists σ0. split; [reflexivity | apply KE_Assume; assumption].
  - fix_pt. apply SD_SeqSkip.
  - apply SD_SeqStep. eapply IHtstep; reflexivity.
  - fix_pt. apply SD_ChoiceL.
  - fix_pt. apply SD_ChoiceR.
  - fix_pt. apply SD_Star0.
  - fix_pt. apply SD_StarN.
  - fix_pt. apply SD_Local.
Qed.

(** ** The interleaved rules *)

Inductive ilal : (estate -> Prop) -> tcom * tcom -> tcom * tcom ->
                 (estate -> Prop) -> Prop :=
  | IL_Refl : forall P p, ilal P p p P
  | IL_Trans : forall P R Q p q r,
      ilal P p q R -> ilal R q r Q -> ilal P p r Q
  | IL_Cons : forall P P' Q Q' p q,
      (forall σ, P σ -> P' σ) -> (forall σ, Q' σ -> Q σ) ->
      ilal P p q Q -> ilal P' p q Q'
  | IL_DisjAll : forall (I : Type) P (Qi : I -> estate -> Prop) p q,
      (forall i, ilal P p q (Qi i)) -> ilal P p q (fun σ => exists i, Qi i σ)
  | IL_StepLeft : forall P Q c1 c1' c2,
      sderiv Victim P c1 c1' Q -> ilal P (c1, c2) (c1', c2) Q
  | IL_StepRight : forall P Q c1 c2 c2',
      sderiv Adversary P c2 c2' Q -> ilal P (c1, c2) (c1, c2') Q
  | IL_Com : forall P p, ilal P p p (fun σ' => exists σ, P σ /\ com σ σ').

Theorem ilal_sound : forall P p q Q, ilal P p q Q -> aval P p q Q.
Proof.
  intros P p q Q H. induction H; intros σ' HQ.
  - exists σ'. split; [exact HQ | apply ST_Refl].
  - destruct (IHilal2 σ' HQ) as [σ1 [HR K2]].
    destruct (IHilal1 σ1 HR) as [σ [HP K1]].
    exists σ. split; [exact HP | eapply steps_trans; eassumption].
  - destruct (IHilal σ' (H0 σ' HQ)) as [σ [HP Hs]].
    exists σ. split; [apply H, HP | exact Hs].
  - destruct HQ as [i HQ]. exact (H0 i σ' HQ).
  - destruct (sderiv_sound _ _ _ _ _ H σ' HQ) as [σ [HP Hs]].
    exists σ. split; [exact HP |].
    eapply ST_Step; [apply IS_L, Hs | apply ST_Refl].
  - destruct (sderiv_sound _ _ _ _ _ H σ' HQ) as [σ [HP Hs]].
    exists σ. split; [exact HP |].
    eapply ST_Step; [apply IS_R, Hs | apply ST_Refl].
  - destruct HQ as [σ [HP Hs]]. exists σ. split; [exact HP |].
    eapply ST_Step; [apply IS_Com, Hs | apply ST_Refl].
Qed.

Lemma ilal_run : forall k k', steps istep k k' ->
    forall p q σ σ', k = (p, σ) -> k' = (q, σ') ->
    ilal (only σ) p q (only σ').
Proof.
  intros k k' H. induction H as [k | k [p1 σ1] k2 Hs _ IH];
    intros p q σ σ' E E'; subst.
  - injection E'; intros; subst. apply IL_Refl.
  - apply (IL_Trans _ (only σ1) _ p p1 q); [| eapply IH; reflexivity].
    inversion Hs; subst.
    + apply IL_StepLeft, sderiv_step. assumption.
    + apply IL_StepRight, sderiv_step. assumption.
    + apply (IL_Cons (only σ) _ (fun σ' => exists x, only σ x /\ com x σ'));
        [auto | | apply IL_Com].
      intros x E. unfold only in E. subst x. exists σ.
      split; [reflexivity | assumption].
Qed.

Theorem ilal_complete : forall P p q Q, aval P p q Q -> ilal P p q Q.
Proof.
  intros P p q Q V.
  apply (IL_Cons P _ (fun t => exists i : {σ' | Q σ'}, t = proj1_sig i));
    [auto | intros σ' HQ; exists (exist _ σ' HQ); reflexivity |].
  apply (IL_DisjAll {σ' | Q σ'} P (fun i t => t = proj1_sig i)).
  intros [σ' HQ]. simpl. destruct (V σ' HQ) as [σ [HP Hr]].
  apply (IL_Cons (only σ) _ (only σ'));
    [intros x E; unfold only in E; subst x; exact HP | auto |].
  exact (ilal_run _ _ Hr p q σ σ' eq_refl eq_refl).
Qed.

Theorem ilal_iff_generated : forall P p q Q, ilal P p q Q <-> ail P p q Q.
Proof.
  intros P p q Q. rewrite ail_iff.
  split; [apply ilal_sound | apply ilal_complete].
Qed.
