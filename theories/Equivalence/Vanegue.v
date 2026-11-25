(** * Adversarial logic: Vanegue's rules and the generated logic

    [van m P c Q] is Vanegue's single-thread adversarial logic (SAS
    2022) for programs run in mode [m], with the rules as ILAL states
    them: empty postcondition, [skip], consequence, disjunction,
    sequencing, either branch of choice, iteration (zero times, one more
    time, backward variant), [assume], forward assignment, [rand],
    [read], [write], success and failure of [adv_assert] (adversary
    mode only), and [local]. (ILAL's single-thread [||] has choice's
    semantics and rules; the language here has no such construct.)

    - [van_sound], [van_complete]: sound and complete for adversarial
      validity ([AL.al_valid]); completeness by Cook's argument with
      strongest postconditions.
    - [van_iff_generated]: Vanegue's rules prove exactly the triples
      that the generated logic ([AL.ALv m]) proves.

    The atom rules state the pre-state through an update of the
    post-state, which uses [functional_extensionality]; completeness for
    [adv_assert] splits on whether the assertion holds ([classic]). *)

From Stdlib Require Import String List NArith Classical.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Verified.
From LogicTransformers.Core Require Import Kernel Rules.
From LogicTransformers.Adversarial Require Import AL.
Import ListNotations.

(** ** The rules *)

Inductive van : mode -> (estate -> Prop) -> tcom -> (estate -> Prop) -> Prop :=
  | DEmpty : forall m P c, van m P c (fun _ => False)
  | DUnit : forall m P, van m P TSkip P
  | DConsequence : forall m P P' Q Q' c,
      (forall σ, P σ -> P' σ) -> (forall σ, Q' σ -> Q σ) ->
      van m P c Q -> van m P' c Q'
  | DDisj : forall m P1 Q1 P2 Q2 c,
      van m P1 c Q1 -> van m P2 c Q2 ->
      van m (fun σ => P1 σ \/ P2 σ) c (fun σ => Q1 σ \/ Q2 σ)
  | DSeq : forall m P Q R c1 c2,
      van m P c1 Q -> van m Q c2 R -> van m P (TSeq c1 c2) R
  | DChoiceL : forall m P Q c1 c2,
      van m P c1 Q -> van m P (TChoice c1 c2) Q
  | DChoiceR : forall m P Q c1 c2,
      van m P c2 Q -> van m P (TChoice c1 c2) Q
  | DIterZero : forall m P c, van m P (TStar c) P
  | DIterNonzero : forall m P Q c,
      van m P (TSeq (TStar c) c) Q -> van m P (TStar c) Q
  | DBackwardVariant : forall m (X : nat -> estate -> Prop) c,
      (forall n, van m (X n) c (X (S n))) ->
      van m (X 0) (TStar c) (fun σ => exists n, X n σ)
  | DAssume : forall m P B,
      van m P (TAssume B) (fun σ => P σ /\ massume m B σ)
  | DAssign : forall m P x e,
      van m P (TAtom (AAsgn x e))
        (fun σ => exists x', P (mupd m σ x x') /\
                  mstore m σ x = e (mstore m (mupd m σ x x')))
  | DRand : forall m P x,
      van m P (TAtom (ARand x)) (fun σ => exists x', P (mupd m σ x x'))
  | DRead : forall m P c x,
      van m P (TAtom (ARead c x))
        (fun σ => exists v x' l,
           P (mchupd m (mupd m σ x x') c (v :: l)) /\
           mchan m σ c = l /\ mstore m σ x = v)
  | DWrite : forall m P c x,
      van m P (TAtom (AWrite c x))
        (fun σ => exists l,
           P (mchupd m σ c l) /\ mchan m σ c = l ++ [mstore m σ x])
  | DAdvAssertSuccess : forall Q B,
      van Adversary Q (TAtom (AAdvAssert B)) (fun σ => Q σ /\ B (avs σ))
  | DAdvAssertFailure : forall Q B,
      van Adversary Q (TAtom (AAdvAssert B)) (fun σ => Q σ /\ ~ B (avs σ))
  | DLocal : forall m P Q x e c,
      van m (fun σ => exists σ0, P σ0 /\
                       σ = mupd m σ0 x (e (mstore m σ0))) c Q ->
      van m P (TLocal x e c)
        (fun σ => exists σb x0, Q σb /\ σ = mupd m σb x x0).

(** ** Soundness: each rule holds in the generated logic *)

Theorem van_sound : forall m P c Q, van m P c Q -> al_valid m P c Q.
Proof.
  intros m P c Q H. apply al_valid_iff.
  induction H.
  - apply al_empty.
  - apply al_unit.
  - eapply al_cons; eassumption.
  - apply al_disj; assumption.
  - eapply al_seq; eassumption.
  - apply al_choice_l; assumption.
  - apply al_choice_r; assumption.
  - apply al_iter_zero.
  - apply al_iter_nonzero; assumption.
  - apply al_backward_variant; assumption.
  - apply al_assume.
  - apply al_assign.
  - apply al_rand.
  - apply al_read.
  - apply al_write.
  - apply al_adv_success.
  - apply al_adv_failure.
  - apply al_local; assumption.
Qed.

(** ** Completeness *)

Definition asp (m : mode) (c : tcom) (P : estate -> Prop) : estate -> Prop :=
  fun σ' => exists σ, P σ /\ kev (asem m) (tenc m c) σ σ'.

Fixpoint aiter (m : mode) (c : tcom) (P : estate -> Prop) (n : nat)
  : estate -> Prop :=
  match n with 0 => P | S n => asp m c (aiter m c P n) end.

Lemma star_aiter : forall m c σ σ', kev (asem m) (KStar (tenc m c)) σ σ' ->
    forall P n, aiter m c P n σ -> exists k, aiter m c P k σ'.
Proof.
  intros m c σ σ' H. remember (KStar (tenc m c)) as k eqn:Ek.
  induction H; inversion Ek; subst; intros P n Hn; [eauto |].
  apply (IHkev2 eq_refl P (S n)). exists s. split; assumption.
Qed.

Ltac post := intros ? ?; eassumption.

Lemma van_sp : forall m c P, van m P c (asp m c P).
Proof.
  intros m c. induction c as [| a | B | c1 IH1 c2 IH2 | c1 IH1 c2 IH2
                             | c IH | x e c IH]; intros P.
  - eapply DConsequence; [| | apply DUnit]; [post |].
    intros σ' [σ [HP Hk]]. inversion Hk; subst. exact HP.
  - destruct a as [x e | x | ch x | ch x | B].
    + eapply DConsequence; [| | apply DAssign]; [post |].
      intros σ' [σ [HP Hk]]. inversion Hk; subst. simpl in *. subst.
      exists (mstore m σ x).
      rewrite mupd_mupd, mupd_same, mstore_mupd. auto.
    + eapply DConsequence; [| | apply DRand]; [post |].
      intros σ' [σ [HP Hk]]. inversion Hk; subst. simpl in *.
      match goal with H : exists v, _ |- _ => destruct H as [v ->] end.
      exists (mstore m σ x). rewrite mupd_mupd, mupd_same. exact HP.
    + eapply DConsequence; [| | apply DRead]; [post |].
      intros σ' [σ [HP Hk]]. inversion Hk; subst. simpl in *.
      match goal with H : exists v l, _ |- _ =>
        destruct H as [v [l [Hc ->]]] end.
      exists v, (mstore m σ x), l.
      rewrite mupd_mchupd, mupd_mupd, mupd_same, mchupd_mchupd, <- Hc,
        mchupd_same, mchan_mchupd, mstore_mchupd, mstore_mupd.
      auto.
    + eapply DConsequence; [| | apply DWrite]; [post |].
      intros σ' [σ [HP Hk]]. inversion Hk; subst. simpl in *. subst.
      exists (mchan m σ ch).
      rewrite mchupd_mchupd, mchupd_same, mchan_mchupd, mstore_mchupd.
      auto.
    + destruct m.
      * eapply DConsequence; [| | apply DEmpty]; [post |].
        intros σ' [σ [HP Hk]]. inversion Hk; subst. simpl in *.
        match goal with H : Victim = Adversary /\ _ |- _ =>
          destruct H as [E _]; discriminate E end.
      * eapply DConsequence;
          [| | apply (DDisj Adversary P _ P _ _
                        (DAdvAssertSuccess P B) (DAdvAssertFailure P B))];
          [intros ? [? | ?]; assumption |].
        intros σ' [σ [HP Hk]]. inversion Hk; subst. simpl in *.
        match goal with H : Adversary = Adversary /\ _ |- _ =>
          destruct H as [_ ->] end.
        destruct (classic (B (avs σ))); [left | right]; auto.
  - eapply DConsequence; [| | apply DAssume]; [post |].
    intros σ' [σ [HP Hk]]. inversion Hk; subst. auto.
  - eapply DSeq; [apply IH1 |].
    eapply DConsequence; [| | apply IH2]; [post |].
    intros σ'' [σ [HP Hk]]. inversion Hk; subst.
    eexists. split; [eexists; split |]; eassumption.
  - eapply DConsequence;
      [| | apply (DDisj m P (asp m c1 P) P (asp m c2 P) (TChoice c1 c2));
           [apply DChoiceL, IH1 | apply DChoiceR, IH2]];
      [intros ? [? | ?]; assumption |].
    intros σ' [σ [HP Hk]]. inversion Hk; subst; [left | right];
      exists σ; split; assumption.
  - eapply DConsequence; [| | apply (DBackwardVariant m (aiter m c P))].
    + post.
    + intros σ' [σ [HP Hk]]. exact (star_aiter m c σ σ' Hk P 0 HP).
    + intros n. apply IH.
  - eapply DConsequence; [| | apply DLocal, IH]; [post |].
    intros σ' [σ [HP Hk]]. simpl in Hk.
    inversion Hk as [| | | ? ? ? σ1 ? Ha Hr | | | |]; subst.
    inversion Ha; subst.
    inversion Hr as [| | | ? ? ? σ2 ? Hc Hx | | | |]; subst.
    inversion Hx; subst. simpl in *.
    match goal with H : exists v, _ |- _ => destruct H as [v ->] end.
    exists σ2, v. split; [| reflexivity].
    exists σ1. split; [| exact Hc]. subst. exists σ. auto.
Qed.

Theorem van_complete : forall m P c Q, al_valid m P c Q -> van m P c Q.
Proof.
  intros m P c Q V. eapply DConsequence; [| | apply van_sp]; [post |].
  intros σ' HQ. exact (V σ' HQ).
Qed.

(** ** Against the generated logic *)

Theorem van_iff_generated : forall m P c Q,
    van m P c Q <-> prov (asem m) (ALv m) P (tenc m c) Q.
Proof.
  intros m P c Q. rewrite al_valid_iff.
  split; [apply van_sound | apply van_complete].
Qed.
