(** * Imp's bottom-face rules are instances of the bottom-face generator

    Each forward rule [brule] and backward rule [wrule] of Imp's bottom face
    ([ImpCube.BotRules], [ImpCube.BotWlpRules]) is a derived rule of the
    generated bottom-face system ([Core.GenerateBot]) on encoded programs
    ([brule_instance], [wrule_instance]).

    The loop rules need two observations:

    - The generated star rule follows every body step, while Imp's loop
      rule follows only steps from states satisfying the guard. For states
      where the guard fails, the body premise is derived from the
      generator's own exactness with an empty pre. So the star's per-state
      posts are [b s ∧ F s], and the two chain relations coincide
      ([reach_equiv], [inf_equiv]).
    - For the wlp rule, [¬(b → W)] and [b ∧ ¬W] agree because Imp's tests
      are decidable. *)

From LogicTransformers.Imp Require Import Syntax BigStep Diverge LangBot.
From LogicTransformers.Imp Require Import Hoare.
From LogicTransformers.ImpCube Require Import BotRules BotWlpRules.
From LogicTransformers.Framework Require Import Language ProgramLogic Cube.
From LogicTransformers.Core Require Import
  Kernel KernelBot ImpCore Generate GenerateBot.

Notation IB := (KLangB iact_sem).
Notation cbt := (@mkTriple IB).
Notation GFB := (@fwdB_base state iact iact_sem iact_sem).
Notation GBB := (@bwdB_base state iact iact_sem iact_sem).

Definition encTB (t : triple ImpBot) : triple IB :=
  @mkTriple IB (pre t) (enc (cmd t)) (post t).

Lemma iact_refl : forall a s s', iact_sem a s s' <-> iact_sem a s s'.
Proof. intros. split; auto. Qed.

Lemma gFB : forall g ps c,
    fwdB_rule iact_sem g ps c -> (forall t, ps t -> derivable GFB t) ->
    derivable GFB c.
Proof. intros g ps c HR H. eapply D_Rule; [exists g; exact HR | exact H]. Qed.

Lemma gBB : forall g ps c,
    bwdB_rule iact_sem g ps c -> (forall t, ps t -> derivable GBB t) ->
    derivable GBB c.
Proof. intros g ps c HR H. eapply D_Rule; [exists g; exact HR | exact H]. Qed.

Lemma bassn_dec : forall b s, bassn b s \/ ~ bassn b s.
Proof.
  intros b s. unfold bassn. destruct (beval s b); [left | right]; auto.
Qed.

Lemma eq_post : forall P c (Q Q' : assertion IB),
    aequiv Q Q' -> triple_equiv (cbt P c Q) (cbt P c Q').
Proof. intros. repeat split; auto; apply H. Qed.

Lemma eq_pre : forall (P P' : assertion IB) c Q,
    aequiv P P' -> triple_equiv (cbt P c Q) (cbt P' c Q).
Proof. intros. repeat split; auto; apply H. Qed.

Ltac no_prem := intros t [].

(** ** Chains: the generated relation and Imp's guarded one agree *)

Lemma reach_equiv : forall (G : state -> option state -> Prop) b F,
    (forall s s', G s (Some s') <-> stepF b F s s') ->
    forall s s', reachK G s s' <-> reachF b F s s'.
Proof.
  intros G b F H s s'. split; intros R; induction R.
  - apply rF_refl.
  - eapply rF_step; [apply H; eassumption | assumption].
  - apply rK_refl.
  - eapply rK_step; [apply H; eassumption | assumption].
Qed.

Lemma inf_equiv : forall (G : state -> option state -> Prop) b F,
    (forall s s', G s (Some s') <-> stepF b F s s') ->
    forall s, infK G s <-> infF b F s.
Proof.
  intros G b F H s. split.
  - revert s. cofix CH. intros s Hi. destruct Hi as [s s1 HG Hi].
    apply (infF_step b F s s1); [apply H, HG | apply CH, Hi].
  - revert s. cofix CH. intros s Hi. destruct Hi as [s s1 HG Hi].
    apply (infK_step G s s1); [apply H, HG | apply CH, Hi].
Qed.

(** ** Forward rules *)

Theorem brule_instance : forall r ps c,
    brule r ps c ->
    (forall t, ps t -> derivable GFB (encTB t)) -> derivable GFB (encTB c).
Proof.
  intros r ps c HR H. destruct HR; simpl.
  - apply (gFB _ _ _ (FB_Skip _ _ P)). no_prem.
  - apply (gFB _ _ _ (FB_Act _ _ P (IAsgn x a))). no_prem.
  - apply (gFB _ _ _ (FB_Seq _ _ P Q R (enc c1) (enc c2))).
    intros t [-> | ->]; [apply (H _ (or_introl eq_refl))
                        | apply (H _ (or_intror eq_refl))].
  - apply (gFB _ _ _ (FB_Choice _ _ P Q1 Q2 _ _)).
    intros t [-> | ->].
    + apply (gFB _ _ _ (FB_Seq _ _ P (bwith P b) Q1 _ _)).
      intros t [-> | ->];
        [apply (gFB _ _ _ (FB_Assume _ _ P (bassn b))); no_prem
        | apply (H _ (or_introl eq_refl))].
    + apply (gFB _ _ _ (FB_Seq _ _ P (bwithout P b) Q2 _ _)).
      intros t [-> | ->];
        [apply (gFB _ _ _ (FB_Assume _ _ P (fun s => ~ bassn b s))); no_prem
        | apply (H _ (or_intror eq_refl))].
  - apply (gFB _ _ _ (FB_Choice _ _ P Q1 Q2 _ _)).
    intros t [-> | ->]; [apply (H _ (or_introl eq_refl))
                        | apply (H _ (or_intror eq_refl))].
  - eapply D_Equiv; [apply (gFB _ _ _ (FB_Act _ _ P (IHavoc x))); no_prem |].
    apply eq_post. intros [s'|]; simpl; [| tauto]. split.
    + intros [s [HP [n ->]]]. exists s, n. auto.
    + intros [s [n [HP ->]]]. exists s. split; [exact HP | exists n; auto].
  - (* While *)
    set (body := KSeq (KAssume (bassn b)) (enc c)).
    set (F' := fun s o => bassn b s /\ F s o).
    assert (HG : forall s s', F' s (Some s') <-> stepF b F s s')
      by (intros; unfold F', stepF; tauto).
    eapply D_Equiv;
      [apply (gFB _ _ _ (FB_Seq _ _ P (starB_post iact_sem F' P)
                          (assumeB_post iact_sem (fun s => ~ bassn b s)
                             (starB_post iact_sem F' P))
                          (KStar body) (KAssume (fun s => ~ bassn b s)))) |].
    + intros t [-> | ->].
      * apply (gFB _ _ _ (FB_Star _ _ P body F')). intros t [s ->].
        set (X := assumeB_post iact_sem (bassn b) (single iact_sem s)).
        destruct (bassn_dec b s) as [Hb | Hb].
        -- eapply D_Equiv;
             [apply (gFB _ _ _ (FB_Seq _ _ (single iact_sem s) X (F s)
                                  (KAssume (bassn b)) (enc c))) |].
           ++ intros t [-> | ->];
                [apply (gFB _ _ _
                          (FB_Assume _ _ (single iact_sem s) (bassn b)));
                 no_prem |].
              eapply D_Equiv; [apply (H _ (ex_intro _ s eq_refl)) |].
              apply eq_pre. intros [s0|]; unfold X, single, single_b; simpl;
                split.
              ** intros [Heq Hb']. inversion Heq; subst. split; auto.
              ** intros [Heq Hb']. inversion Heq; subst. split; auto.
              ** intros [Heq _]. discriminate.
              ** intros Heq. discriminate.
           ++ apply eq_post. intros o. unfold F'. tauto.
        -- eapply D_Equiv;
             [apply (gFB _ _ _ (FB_Seq _ _ (single iact_sem s) X
                                  (@img IB (enc c) X)
                                  (KAssume (bassn b)) (enc c))) |].
           ++ intros t [-> | ->];
                [apply (gFB _ _ _
                          (FB_Assume _ _ (single iact_sem s) (bassn b)));
                 no_prem |].
              apply (fwdB_exact iact_sem iact_sem iact_refl).
           ++ apply eq_post. intros o. unfold F', img. split.
              ** intros [[s0|] [HX _]]; unfold X, single in HX; simpl in HX.
                 --- destruct HX as [Heq Hb0]. inversion Heq; subst.
                     contradiction.
                 --- discriminate.
              ** intros [Hb' _]. contradiction.
      * apply (gFB _ _ _ (FB_Assume _ _ _ (fun s => ~ bassn b s))). no_prem.
    + apply eq_post. intros [s'|]; simpl.
      * split.
        -- intros [[s [HP Hr]] Hnb]. exists s.
           repeat split; [exact HP | apply (reach_equiv F' b F HG), Hr
                         | exact Hnb].
        -- intros [s [HP [Hr Hnb]]]. split; [| exact Hnb].
           exists s. split; [exact HP | apply (reach_equiv F' b F HG), Hr].
      * split.
        -- intros [HP | [[s [s1 [HP [Hr [Hb HF]]]]] | [s [HP Hi]]]].
           ++ left. exact HP.
           ++ right. left. exists s, s1.
              repeat split; auto. apply (reach_equiv F' b F HG), Hr.
           ++ right. right. exists s.
              split; [exact HP | apply (inf_equiv F' b F HG), Hi].
        -- intros [HP | [[s [s1 [HP [Hr [Hb HF]]]]] | [s [HP Hi]]]].
           ++ left. exact HP.
           ++ right. left. exists s, s1.
              repeat split; auto. apply (reach_equiv F' b F HG), Hr.
           ++ right. right. exists s.
              split; [exact HP | apply (inf_equiv F' b F HG), Hi].
Qed.

(** ** Backward rules *)

Theorem wrule_instance : forall r ps c,
    wrule r ps c ->
    (forall t, ps t -> derivable GBB (encTB t)) -> derivable GBB (encTB c).
Proof.
  intros r ps c HR H. destruct HR; simpl.
  - apply (gBB _ _ _ (BB_Skip _ _ Q)). no_prem.
  - eapply D_Equiv; [apply (gBB _ _ _ (BB_Act _ _ Q (IAsgn x a))); no_prem |].
    apply eq_pre. intros [s|]; simpl; [| tauto]. split.
    + intros Hw. apply Hw. reflexivity.
    + intros HQ s' ->. exact HQ.
  - apply (gBB _ _ _ (BB_Seq _ _ P Q R (enc c1) (enc c2))).
    intros t [-> | ->]; [apply (H _ (or_introl eq_refl))
                        | apply (H _ (or_intror eq_refl))].
  - eapply D_Equiv;
      [apply (gBB _ _ _ (BB_Choice _ _ (assumeB_pre iact_sem (bassn b) P1)
                           (assumeB_pre iact_sem (fun s => ~ bassn b s) P2) Q
                           (KSeq (KAssume (bassn b)) (enc c1))
                           (KSeq (KAssume (fun s => ~ bassn b s))
                                 (enc c2)))) |].
    + intros t [-> | ->].
      * apply (gBB _ _ _ (BB_Seq _ _ _ P1 Q _ _)).
        intros t [-> | ->];
          [apply (gBB _ _ _ (BB_Assume _ _ P1 (bassn b))); no_prem
          | apply (H _ (or_introl eq_refl))].
      * apply (gBB _ _ _ (BB_Seq _ _ _ P2 Q _ _)).
        intros t [-> | ->];
          [apply (gBB _ _ _ (BB_Assume _ _ P2 (fun s => ~ bassn b s))); no_prem
          | apply (H _ (or_intror eq_refl))].
    + apply eq_pre. intros [s|]; simpl; tauto.
  - apply (gBB _ _ _ (BB_Choice _ _ P1 P2 Q _ _)).
    intros t [-> | ->]; [apply (H _ (or_introl eq_refl))
                        | apply (H _ (or_intror eq_refl))].
  - eapply D_Equiv; [apply (gBB _ _ _ (BB_Act _ _ Q (IHavoc x))); no_prem |].
    apply eq_pre. intros [s|]; simpl; [| tauto]. split.
    + intros Hw n. apply Hw. exists n. reflexivity.
    + intros HQ s' [n ->]. apply HQ.
  - (* While *)
    set (body := KSeq (KAssume (bassn b)) (enc c)).
    set (M := assumeB_pre iact_sem (fun s => ~ bassn b s) Q).
    set (W' := fun s' => assumeB_pre iact_sem (bassn b) (W s')).
    set (Wd' := assumeB_pre iact_sem (bassn b) Wd).
    assert (HG : forall s s', stepsW iact_sem W' Wd' s (Some s') <->
                              stepF b (BotWlpRules.stepsW W Wd) s s').
    { intros s s'. unfold stepsW, BotWlpRules.stepsW, stepF, W'.
      simpl. destruct (bassn_dec b s); tauto. }
    assert (HWd : forall s, ~ Wd' (Some s) <-> bassn b s /\ ~ Wd (Some s)).
    { intros s. unfold Wd'. simpl. destruct (bassn_dec b s); tauto. }
    eapply D_Equiv;
      [apply (gBB _ _ _ (BB_Seq _ _ (starB_pre iact_sem W' Wd' M) M Q
                          (KStar body) (KAssume (fun s => ~ bassn b s)))) |].
    + intros t [-> | ->].
      * apply (gBB _ _ _ (BB_Star _ _ M body W' Wd')).
        intros t [[s' ->] | ->].
        -- apply (gBB _ _ _ (BB_Seq _ _ (W' s') (W s') (neqS iact_sem s')
                               (KAssume (bassn b)) (enc c))).
           intros t [-> | ->];
             [apply (gBB _ _ _ (BB_Assume _ _ (W s') (bassn b))); no_prem
             | apply (H _ (or_introl (ex_intro _ s' eq_refl)))].
        -- apply (gBB _ _ _ (BB_Seq _ _ Wd' Wd (neqNone iact_sem)
                               (KAssume (bassn b)) (enc c))).
           intros t [-> | ->];
             [apply (gBB _ _ _ (BB_Assume _ _ Wd (bassn b))); no_prem
             | apply (H _ (or_intror eq_refl))].
      * apply (gBB _ _ _ (BB_Assume _ _ Q (fun s => ~ bassn b s))). no_prem.
    + apply eq_pre. intros [s|]; simpl; [| tauto].
      pose proof (reach_equiv _ b _ HG s) as RE.
      pose proof (inf_equiv _ b _ HG s) as IE.
      split.
      * intros [H1 H2]. split.
        -- intros s' Hr. apply H1, RE, Hr.
        -- intros [[s1 [Hr [Hb HnWd]]] | Hi]; apply H2.
           ++ left. exists s1. split; [apply RE, Hr | apply HWd; auto].
           ++ right. apply IE, Hi.
      * intros [H1 H2]. split.
        -- intros s' Hr. apply H1, RE, Hr.
        -- intros [[s1 [Hr HnWd]] | Hi]; apply H2.
           ++ left. exists s1. destruct (proj1 (HWd s1) HnWd) as [Hb Hn].
              repeat split; [apply RE, Hr | exact Hb | exact Hn].
           ++ right. apply IE, Hi.
Qed.
