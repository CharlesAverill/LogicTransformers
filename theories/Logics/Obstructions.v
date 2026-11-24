(** * Why the invariant rule cannot be flipped

    Cousot (POPL'24, Thm. II.3.1): Park's fixpoint induction, the
    principle behind the Hoare invariant rule, is an lfp
    over-approximation principle, and "by order-duality, this is sound
    and complete greatest fixpoint under approximation". This file makes
    that concrete for Imp:

    - [sp_while_lfp]: the strongest postcondition of a loop is the least
      fixpoint of [F X = P ∪ sp c (X ∧ b)], restricted to [¬b].
    - [naive_premises_gfp]: the premises of the order-flipped invariant
      rule only make [I] a coinvariant, so [I ⊆ gfp F] (via [park_gfp]).
    - [naive_flipped_invariant_unsound]: that rule is unsound for IL. The
      counterexample's coinvariant contains states that are not reachable
      from [P]; they lie in the gfp but not in the lfp.
    - [flipped_invariant_trivial]: the order flip of the bare [WhileInv]
      rule is IL-sound only because its conclusion is always valid
      (zero iterations), so it can never contribute to completeness.

    The counterexample needs [functional_extensionality] to show that a
    state equals the result of an assignment. Nothing else in this file
    uses it. *)

From Stdlib Require Import String Arith Lia FunctionalExtensionality.
From LogicTransformers.Imp Require Import Syntax BigStep Lang.
From LogicTransformers.Logics Require Import Hoare ImpRules HoareLogic IL.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Fixpoints.

Definition loop_F (P : assertion Imp) (b : bexp) (c : com)
  : @pset state -> @pset state :=
  fun X s => P s \/ sp c (with_b X b) s.

Lemma loop_F_monotone : forall P b c, monotone (loop_F P b c).
Proof.
  intros P b c X Y H s [HP | [s0 [[HX Hb] Hc]]].
  - left. exact HP.
  - right. exists s0. repeat split; auto.
Qed.

Theorem sp_while_lfp : forall P b c,
    aequiv (sp (CWhile b c) P) (with_nb (lfp (loop_F P b c)) b).
Proof.
  intros P b c s'. unfold img. cbn. split.
  - intros [s [HP Hc]].
    assert (Hin : lfp (loop_F P b c) s)
      by (apply lfp_prefix; [apply loop_F_monotone | left; exact HP]).
    clear HP. remember (CWhile b c) as w eqn:Ew.
    induction Hc; inversion Ew; subst.
    + split; [exact Hin | apply bassn_false'; assumption].
    + apply IHHc2; [reflexivity |].
      apply lfp_prefix; [apply loop_F_monotone |].
      right. exists st. repeat split; assumption.
  - intros [Hl Hnb].
    set (X := fun s' => exists s, P s /\
                (forall s'', ceval (CWhile b c) s' s'' ->
                             ceval (CWhile b c) s s'')).
    assert (HX : sub (loop_F P b c X) X).
    { intros s1 [HP | [s0 [[[s [H0 Hpre]] Hb] Hc]]].
      - exists s1. split; [exact HP | auto].
      - exists s. split; [exact H0 |].
        intros s'' Hw. apply Hpre. eapply E_WhileTrue; eassumption. }
    destruct (lfp_least _ X HX s' Hl) as [s [HP Hpre]].
    exists s. split; [exact HP |].
    apply Hpre, E_WhileFalse, bassn_false, Hnb.
Qed.

(** ** The naively flipped invariant rule

    Hoare's rule, with consequence folded in, is
    [P ⊆ I, {I ∧ b} c {I}, I ∧ ¬b ⊆ Q ⟹ {P} while b c {Q}]. Flipping the
    inclusions that consequence controls gives the following IL rule. *)

Definition naive_flipped_invariant_rule : Prop :=
  forall (P I Q : assertion Imp) b c,
    aimpl P I ->
    valid IL (ht (with_b I b) c I) ->
    aimpl Q (with_nb I b) ->
    valid IL (ht P (CWhile b c) Q).

(** Its premises make [I] a post-fixpoint of [F], i.e. a coinvariant, so
    they only bound the gfp, while the conclusion is about the lfp. *)
Lemma naive_premises_gfp : forall P I b c,
    valid IL (ht (with_b I b) c I) -> sub I (gfp (loop_F P b c)).
Proof.
  intros P I b c H. apply gfp_greatest. intros s Hs. right.
  destruct (proj1 (IL_valid_iff _ _ _) H s Hs) as [s0 [H0 Hc]].
  exists s0. split; assumption.
Qed.

Local Notation vx := "x"%string.
Local Notation vy := "y"%string.

Lemma countdown_preserves_y : forall s s',
    ceval (CWhile (BNot (BLe (AVar vx) (ANum 0)))
                  (CAsgn vx (AMinus (AVar vx) (ANum 1)))) s s' ->
    s' vy = s vy.
Proof.
  intros s s' Hc.
  remember (CWhile (BNot (BLe (AVar vx) (ANum 0)))
                   (CAsgn vx (AMinus (AVar vx) (ANum 1)))) as w eqn:Ew.
  induction Hc; inversion Ew; subst; auto.
  rewrite IHHc2 by reflexivity.
  match goal with
  | H : ceval (CAsgn _ _) _ _ |- _ => inversion H; subst
  end.
  apply update_neq. discriminate.
Qed.

Theorem naive_flipped_invariant_unsound : ~ naive_flipped_invariant_rule.
Proof.
  intros Hrule.
  set (b := BNot (BLe (AVar vx) (ANum 0))).
  set (c := CAsgn vx (AMinus (AVar vx) (ANum 1))).
  set (Inv := fun _ : state => True).
  set (P := fun s : state => s vx = 0 /\ s vy = 0).
  set (Q := fun s : state => s vx = 0 /\ s vy = 1).
  assert (Hprem : valid IL (ht (with_b Inv b) c Inv)).
  { apply IL_valid_iff. intros st' _.
    set (s0 := update st' vx (S (st' vx))).
    exists s0. split.
    - split; [exact I |]. unfold bassn, s0. simpl.
      try rewrite update_eq. reflexivity.
    - assert (E : update s0 vx (aeval s0 (AMinus (AVar vx) (ANum 1))) = st').
      { apply functional_extensionality. intros z. unfold s0.
        cbn [aeval]. rewrite update_eq. unfold update.
        destruct (String.eqb vx z) eqn:Ez; [| reflexivity].
        apply String.eqb_eq in Ez. subst z. lia. }
      rewrite <- E. apply E_Asgn. }
  assert (HQ : @aimpl Imp Q (with_nb Inv b)).
  { intros s [Hx _]. split; [exact I |].
    unfold bassn, b. simpl. rewrite Hx. discriminate. }
  pose proof (Hrule P Inv Q b c (fun _ _ => I) Hprem HQ) as Hc.
  apply IL_valid_iff in Hc.
  set (st' := update (update empty_state vx 0) vy 1).
  assert (Hst' : Q st').
  { unfold Q, st'. rewrite update_eq, update_neq by discriminate.
    rewrite update_eq. auto. }
  destruct (Hc st' Hst') as [s [[_ Hy] Hw]].
  apply countdown_preserves_y in Hw.
  unfold st' in Hw. rewrite update_eq in Hw. congruence.
Qed.

(** The flip of the bare invariant rule is sound only because its
    conclusion holds for every [I]. *)
Theorem flipped_invariant_trivial : forall (I : assertion Imp) b c,
    valid IL (ht I (CWhile b c) (with_nb I b)).
Proof.
  intros I b c. apply IL_valid_iff. intros s [HI Hnb].
  exists s. split; [exact HI | apply E_WhileFalse, bassn_false, Hnb].
Qed.
