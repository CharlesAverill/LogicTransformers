(** * A disjoint parallel rule for concurrent incorrectness

    Raad et al.'s concurrent incorrectness separation logic composes
    threads with the rule
    [[P1] C1 [Q1], [P2] C2 [Q2] ⊢ [P1 * P2] C1 ∥ C2 [Q1 * Q2]],
    where [*] separates the threads' resources. Separation is outside
    the relational cube, but the rule has a relational shadow: replace
    separation by threads confined to disjoint sets of variables.

    - [conf V c]: [c] reads and writes only the variables in [V]
      (stated semantically for expressions);
    - [conf_run]: a confined run leaves other variables alone, and is
      mirrored from any state that agrees on [V];
    - [il_disjoint_par]: if [c1] and [c2] are confined to disjoint sets
      and each precondition depends only on its thread's variables, then
      incorrectness triples for the threads combine into one for
      [c1 ∥ c2], with the conjunction of the postconditions (which need
      no condition). The witness run executes [c1] to the end, then
      [c2].
    - [il_disjoint_par_generated]: the same, in the generated logic.

    Building the witness state uses [functional_extensionality]. *)

From Stdlib Require Import String List Bool FunctionalExtensionality.
From LogicTransformers.Imp Require Import Syntax.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Relational Verified.
From LogicTransformers.Core Require Import Kernel SmallStepCore.
From LogicTransformers.ParImp Require Import ParImp ConcurrentIL.
Import ListNotations.

Section Confined.

Variable V : var -> bool.

Definition agreeOn (s t : state) : Prop := forall y, V y = true -> s y = t y.
Definition offV (s t : state) : Prop := forall y, V y = false -> s y = t y.

Definition adep (a : aexp) : Prop :=
  forall s t, agreeOn s t -> aeval s a = aeval t a.
Definition bdep (b : bexp) : Prop :=
  forall s t, agreeOn s t -> beval s b = beval t b.

Fixpoint mconf (l : list (var * aexp)) : Prop :=
  match l with
  | [] => True
  | (x, a) :: l => V x = true /\ adep a /\ mconf l
  end.

Fixpoint conf (c : pcom) : Prop :=
  match c with
  | PSkip => True
  | PAsgn x a => V x = true /\ adep a
  | PSeq c1 c2 | PPar c1 c2 => conf c1 /\ conf c2
  | PIf b c1 c2 => bdep b /\ conf c1 /\ conf c2
  | PWhile b c => bdep b /\ conf c
  | PMulti l => mconf l
  end.

Lemma upd_agree : forall s t x v, agreeOn s t ->
    agreeOn (update s x v) (update t x v).
Proof.
  intros s t x v H y Hy. unfold update.
  destruct (String.eqb x y); [reflexivity | apply H, Hy].
Qed.

Lemma upd_off : forall s x v, V x = true -> offV s (update s x v).
Proof.
  intros s x v Hx y Hy. unfold update.
  destruct (String.eqb_spec x y); [subst; congruence | reflexivity].
Qed.

Lemma off_trans : forall s t u, offV s t -> offV t u -> offV s u.
Proof. intros s t u H1 H2 y Hy. rewrite H1, H2; auto. Qed.

Lemma off_refl : forall s, offV s s.
Proof. intros s y _. reflexivity. Qed.

Lemma massign_conf : forall l s t, mconf l -> agreeOn s t ->
    agreeOn (massign l s) (massign l t) /\ offV s (massign l s) /\
    offV t (massign l t).
Proof.
  induction l as [| [x a] l IH]; intros s t Hc H; simpl.
  - split; [exact H | split; apply off_refl].
  - destruct Hc as [Hx [Ha Hl]]. rewrite (Ha s t H).
    destruct (IH (update s x (aeval t a)) (update t x (aeval t a)) Hl
                 (upd_agree _ _ _ _ H)) as [A [O1 O2]].
    split; [exact A |].
    split; eapply off_trans; [apply upd_off, Hx | exact O1
                             | apply upd_off, Hx | exact O2].
Qed.

Lemma conf_step : forall c s c' s', conf c -> pstep (c, s) (c', s') ->
    conf c' /\ offV s s' /\
    forall t, agreeOn s t ->
      exists t', pstep (c, t) (c', t') /\ agreeOn s' t' /\ offV t t'.
Proof.
  intros c s c' s' Hc H.
  remember (c, s) as k eqn:Ek. remember (c', s') as k' eqn:Ek'.
  revert c s c' s' Ek Ek' Hc.
  induction H; intros c0 s0 c0' s0' Ek Ek' Hc;
    injection Ek; injection Ek'; intros; subst; simpl in Hc.
  - destruct Hc as [Hx Ha]. split; [exact I |]. split; [apply upd_off, Hx |].
    intros t Ht. exists (update t x (aeval t a)).
    split; [apply PS_Asgn |]. rewrite (Ha s0 t Ht).
    split; [apply upd_agree, Ht | apply upd_off, Hx].
  - split; [apply Hc |]. split; [apply off_refl |].
    intros t Ht. exists t.
    split; [apply PS_SeqSkip | split; [exact Ht | apply off_refl]].
  - destruct Hc as [C1 C2].
    destruct (IHpstep p1 s0 p1' s0' eq_refl eq_refl C1) as [C1' [O F]].
    split; [split; assumption |]. split; [exact O |].
    intros t Ht. destruct (F t Ht) as [t' [S [A O']]].
    exists t'. split; [apply PS_Seq, S | auto].
  - destruct Hc as [Hb [C1 C2]]. split; [exact C1 |]. split; [apply off_refl |].
    intros t Ht. exists t. split; [| split; [exact Ht | apply off_refl]].
    apply PS_IfT. rewrite <- (Hb s0 t Ht). assumption.
  - destruct Hc as [Hb [C1 C2]]. split; [exact C2 |]. split; [apply off_refl |].
    intros t Ht. exists t. split; [| split; [exact Ht | apply off_refl]].
    apply PS_IfF. rewrite <- (Hb s0 t Ht). assumption.
  - destruct Hc as [Hb C]. split; [simpl; tauto |]. split; [apply off_refl |].
    intros t Ht. exists t.
    split; [apply PS_While | split; [exact Ht | apply off_refl]].
  - destruct Hc as [C1 C2].
    destruct (IHpstep p1 s0 p1' s0' eq_refl eq_refl C1) as [C1' [O F]].
    split; [split; assumption |]. split; [exact O |].
    intros t Ht. destruct (F t Ht) as [t' [S [A O']]].
    exists t'. split; [apply PS_ParL, S | auto].
  - destruct Hc as [C1 C2].
    destruct (IHpstep p2 s0 p2' s0' eq_refl eq_refl C2) as [C2' [O F]].
    split; [split; assumption |]. split; [exact O |].
    intros t Ht. destruct (F t Ht) as [t' [S [A O']]].
    exists t'. split; [apply PS_ParR, S | auto].
  - split; [exact I |]. split; [apply off_refl |].
    intros t Ht. exists t.
    split; [apply PS_ParDone | split; [exact Ht | apply off_refl]].
  - destruct (massign_conf l s0 s0 Hc (fun _ _ => eq_refl)) as [_ [O _]].
    split; [exact I |]. split; [exact O |].
    intros t Ht. destruct (massign_conf l s0 t Hc Ht) as [A [_ O']].
    exists (massign l t). split; [apply PS_Multi | split; assumption].
Qed.

Theorem conf_run : forall c s c' s', conf c -> run (c, s) (c', s') ->
    offV s s' /\
    forall t, agreeOn s t ->
      exists t', run (c, t) (c', t') /\ agreeOn s' t' /\ offV t t'.
Proof.
  intros c s c' s' Hc H.
  remember (c, s) as k eqn:Ek. remember (c', s') as k' eqn:Ek'.
  revert c s Ek Hc.
  induction H as [k | k [c1 s1] k2 Hs _ IH]; intros c s Ek Hc.
  - rewrite Ek in Ek'. injection Ek'. intros; subst.
    split; [apply off_refl |]. intros t Ht.
    exists t. split; [apply SM_Refl | split; [exact Ht | apply off_refl]].
  - subst k. destruct (conf_step c s c1 s1 Hc Hs) as [Hc1 [O1 F1]].
    destruct (IH Ek' c1 s1 eq_refl Hc1) as [O2 F2].
    split; [eapply off_trans; eassumption |].
    intros t Ht. destruct (F1 t Ht) as [t1 [S1 [A1 O1']]].
    destruct (F2 t1 A1) as [t' [R [A O]]].
    exists t'. split; [eapply SM_Step; eassumption |].
    split; [exact A | eapply off_trans; eassumption].
Qed.

End Confined.

Definition local (V : var -> bool) (P : state -> Prop) : Prop :=
  forall s t, agreeOn V s t -> P s -> P t.

Definition merge (V : var -> bool) (s t : state) : state :=
  fun y => if V y then s y else t y.

Theorem il_disjoint_par : forall V1 V2 (P1 P2 Q1 Q2 : state -> Prop) c1 c2,
    (forall y, V1 y = true -> V2 y = false) ->
    conf V1 c1 -> conf V2 c2 -> local V1 P1 -> local V2 P2 ->
    cil_valid P1 c1 Q1 -> cil_valid P2 c2 Q2 ->
    cil_valid (fun s => P1 s /\ P2 s) (PPar c1 c2)
              (fun s => Q1 s /\ Q2 s).
Proof.
  intros V1 V2 P1 P2 Q1 Q2 c1 c2 Hd C1 C2 L1 L2 H1 H2 s' [Hq1 Hq2].
  destruct (H1 s' Hq1) as [s1 [Hp1 R1]].
  destruct (H2 s' Hq2) as [s2 [Hp2 R2]].
  set (s := merge V1 s1 s2).
  assert (A1 : agreeOn V1 s1 s).
  { intros y Hy. unfold s, merge. rewrite Hy. reflexivity. }
  assert (A2 : agreeOn V2 s2 s).
  { intros y Hy. unfold s, merge.
    destruct (V1 y) eqn:E; [rewrite (Hd y E) in Hy; discriminate |].
    reflexivity. }
  exists s. split; [split; [exact (L1 _ _ A1 Hp1) | exact (L2 _ _ A2 Hp2)] |].
  destruct (conf_run V1 c1 s1 PSkip s' C1 R1) as [_ F1].
  destruct (F1 s A1) as [t1 [Q1r [B1 O1]]].
  destruct (conf_run V2 c2 s2 PSkip s' C2 R2) as [Off2 F2].
  assert (A2' : agreeOn V2 s2 t1).
  { intros y Hy. rewrite (A2 y Hy).
    destruct (V1 y) eqn:E; [rewrite (Hd y E) in Hy; discriminate |].
    apply O1, E. }
  destruct (F2 t1 A2') as [t2 [Q2r [B2 O2]]].
  assert (E : t2 = s').
  { apply functional_extensionality. intros y.
    destruct (V2 y) eqn:Ey2; [symmetry; apply B2, Ey2 |].
    rewrite <- (O2 y Ey2).
    destruct (V1 y) eqn:Ey1; [symmetry; apply B1, Ey1 |].
    rewrite <- (O1 y Ey1). unfold s, merge. rewrite Ey1.
    apply Off2, Ey2. }
  subst t2.
  eapply run_trans; [apply run_parL, Q1r |].
  eapply run_trans; [apply run_parR, Q2r |].
  apply run_step, PS_ParDone.
Qed.

(** In the generated incorrectness logic. *)
Corollary il_disjoint_par_generated :
  forall V1 V2 (P1 P2 Q1 Q2 : state -> Prop) c1 c2,
    (forall y, V1 y = true -> V2 y = false) ->
    conf V1 c1 -> conf V2 c2 -> local V1 P1 -> local V2 P2 ->
    cil P1 c1 Q1 -> cil P2 c2 Q2 ->
    cil (fun s => P1 s /\ P2 s) (PPar c1 c2) (fun s => Q1 s /\ Q2 s).
Proof.
  intros. apply cil_complete.
  eapply il_disjoint_par; try eassumption; apply cil_sound; assumption.
Qed.
