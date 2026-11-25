(** * Big-step divergence is infinite small-step reduction

    [Imp.Diverge] defines divergence coinductively, in big-step style
    ([diverges]). This file cross-checks it against the small-step
    semantics: [sdiverges c s] says some reduction sequence from [(c, s)]
    never ends. [diverges_iff_sdiverges] proves they agree, so the
    bottom-face semantics of Imp ([ImpBot]) rests on two independent
    definitions that coincide, as the top face already did
    ([big_small_equiv]).

    - Big-step to small-step is constructive: every diverging program
      takes a step to a diverging program ([diverges_step]).
    - Small-step to big-step uses [classic]: for an infinite reduction of
      [c1; c2], either [c1] eventually finishes or it never does
      ([sdiv_seq_split]). *)

From Stdlib Require Import Classical.
From LogicTransformers.Imp Require Import
  Syntax BigStep SmallStep Equiv Diverge LangBot.

CoInductive sdiverges : com -> state -> Prop :=
  | SDv : forall c s c' s',
      cstep c s c' s' -> sdiverges c' s' -> sdiverges c s.

(** ** Big-step to small-step *)

(** A terminating program other than [skip] takes a first step that
    keeps the same final state. *)
Lemma ceval_first_step : forall c s s1, ceval c s s1 -> c <> CSkip ->
    exists c' s', cstep c s c' s' /\ ceval c' s' s1.
Proof.
  intros c s s1 H Hne. apply big_to_small in H. inversion H; subst.
  - contradiction.
  - eexists _, _. split; [eassumption | apply small_to_big; assumption].
Qed.

Lemma diverges_step : forall c s, diverges c s ->
    exists c' s', cstep c s c' s' /\ diverges c' s'.
Proof.
  induction c; intros s H; inversion H; subst.
  - destruct (IHc1 s ltac:(assumption)) as [c1' [s' [Hs Hd]]].
    exists (CSeq c1' c2), s'. split; [apply S_SeqStep, Hs | apply Dv_SeqL, Hd].
  - match goal with Hc : ceval c1 _ _ |- _ => rename Hc into Hc1 end.
    assert (Hk : c1 = CSkip \/ c1 <> CSkip)
      by (destruct c1; (left; reflexivity) || (right; discriminate)).
    destruct Hk as [-> | Hne].
    + inversion Hc1; subst. exists c2. eexists.
      split; [apply S_SeqSkip | eassumption].
    + destruct (ceval_first_step _ _ _ Hc1 Hne) as [c1' [s' [Hs Hc']]].
      exists (CSeq c1' c2), s'.
      split; [apply S_SeqStep, Hs | eapply Dv_SeqR; eassumption].
  - exists c1. eexists. split; [apply S_IfTrue; eassumption | eassumption].
  - exists c2. eexists. split; [apply S_IfFalse; eassumption | eassumption].
  - eexists _, _. split; [apply S_While |].
    apply Dv_IfTrue; [eassumption | apply Dv_SeqL; eassumption].
  - eexists _, _. split; [apply S_While |].
    apply Dv_IfTrue; [eassumption | eapply Dv_SeqR; eassumption].
  - exists c1. eexists. split; [apply S_ChoiceL | eassumption].
  - exists c2. eexists. split; [apply S_ChoiceR | eassumption].
Qed.

Theorem diverges_sdiverges : forall c s, diverges c s -> sdiverges c s.
Proof.
  cofix CH. intros c s H.
  destruct (diverges_step c s H) as [c' [s' [Hs Hd]]].
  exact (SDv c s c' s' Hs (CH c' s' Hd)).
Qed.

(** ** Small-step to big-step *)

Lemma sdiv_inv : forall c s, sdiverges c s ->
    exists c' s', cstep c s c' s' /\ sdiverges c' s'.
Proof. intros c s H. inversion H; subst. eauto. Qed.

Lemma sdiv_skip : forall s, ~ sdiverges CSkip s.
Proof.
  intros s H. destruct (sdiv_inv _ _ H) as [c' [s' [Hs _]]]. inversion Hs.
Qed.

(** Inversion lemmas, one per construct. Proved outside any [cofix], so
    the coinductive proofs below only take apart disjunctions. *)
Lemma sdiv_seq_step : forall c1 c2 s, sdiverges (CSeq c1 c2) s ->
    (c1 = CSkip /\ sdiverges c2 s) \/
    (exists c1' s', cstep c1 s c1' s' /\ sdiverges (CSeq c1' c2) s').
Proof.
  intros c1 c2 s H. destruct (sdiv_inv _ _ H) as [c' [s' [Hs Hd]]].
  inversion Hs; subst; [left; auto | right; eauto].
Qed.

Lemma sdiv_asgn : forall x a s, ~ sdiverges (CAsgn x a) s.
Proof.
  intros x a s H. destruct (sdiv_inv _ _ H) as [c' [s' [Hs Hd]]].
  inversion Hs; subst. exact (sdiv_skip _ Hd).
Qed.

Lemma sdiv_havoc : forall x s, ~ sdiverges (CHavoc x) s.
Proof.
  intros x s H. destruct (sdiv_inv _ _ H) as [c' [s' [Hs Hd]]].
  inversion Hs; subst. exact (sdiv_skip _ Hd).
Qed.

Lemma sdiv_if : forall b c1 c2 s, sdiverges (CIf b c1 c2) s ->
    (beval s b = true /\ sdiverges c1 s) \/
    (beval s b = false /\ sdiverges c2 s).
Proof.
  intros b c1 c2 s H. destruct (sdiv_inv _ _ H) as [c' [s' [Hs Hd]]].
  inversion Hs; subst; auto.
Qed.

Lemma sdiv_while : forall b c s, sdiverges (CWhile b c) s ->
    beval s b = true /\ sdiverges (CSeq c (CWhile b c)) s.
Proof.
  intros b c s H. destruct (sdiv_inv _ _ H) as [c' [s' [Hs Hd]]].
  inversion Hs; subst. destruct (sdiv_if _ _ _ _ Hd) as [[Hb H1] | [_ H2]].
  - auto.
  - exfalso. exact (sdiv_skip _ H2).
Qed.

Lemma sdiv_choice : forall c1 c2 s, sdiverges (CChoice c1 c2) s ->
    sdiverges c1 s \/ sdiverges c2 s.
Proof.
  intros c1 c2 s H. destruct (sdiv_inv _ _ H) as [c' [s' [Hs Hd]]].
  inversion Hs; subst; auto.
Qed.

Lemma sdiv_seq_left : forall c2 c1 s,
    sdiverges (CSeq c1 c2) s ->
    ~ (exists s1, cmulti c1 s CSkip s1 /\ sdiverges c2 s1) ->
    sdiverges c1 s.
Proof.
  intros c2. cofix CH. intros c1 s H Hn.
  destruct (sdiv_seq_step _ _ _ H) as [[E Hd] | [c1' [s' [Hs Hd]]]].
  - exfalso. apply Hn. exists s. split; [rewrite E; apply MS_Refl | exact Hd].
  - apply (SDv c1 s c1' s' Hs). apply CH; [exact Hd |].
    intros [s1 [Hm Hd1]]. apply Hn. exists s1.
    split; [eapply MS_Step; eassumption | exact Hd1].
Qed.

Lemma sdiv_seq_split : forall c1 c2 s,
    sdiverges (CSeq c1 c2) s ->
    sdiverges c1 s \/ exists s1, cmulti c1 s CSkip s1 /\ sdiverges c2 s1.
Proof.
  intros c1 c2 s H.
  destruct (classic (exists s1, cmulti c1 s CSkip s1 /\ sdiverges c2 s1))
    as [Hy | Hn]; [right; exact Hy | left].
  exact (sdiv_seq_left c2 c1 s H Hn).
Qed.

Theorem sdiverges_diverges : forall c s, sdiverges c s -> diverges c s.
Proof.
  cofix CH. intros c s H. destruct c.
  - exfalso. exact (sdiv_skip s H).
  - exfalso. exact (sdiv_asgn _ _ s H).
  - destruct (sdiv_seq_split c1 c2 s H) as [H1 | [s1 [Hm H2]]].
    + apply Dv_SeqL, CH, H1.
    + eapply Dv_SeqR; [apply small_to_big, Hm | apply CH, H2].
  - destruct (sdiv_if _ _ _ _ H) as [[Hb Hd] | [Hb Hd]].
    + apply Dv_IfTrue; [exact Hb | apply CH, Hd].
    + apply Dv_IfFalse; [exact Hb | apply CH, Hd].
  - destruct (sdiv_while _ _ _ H) as [Hb Hd].
    destruct (sdiv_seq_split _ _ _ Hd) as [H1 | [s1 [Hm H2]]].
    + apply Dv_WhileBody; [exact Hb | apply CH, H1].
    + eapply Dv_WhileIter; [exact Hb | apply small_to_big, Hm | apply CH, H2].
  - destruct (sdiv_choice _ _ _ H) as [Hd | Hd].
    + apply Dv_ChoiceL, CH, Hd.
    + apply Dv_ChoiceR, CH, Hd.
  - exfalso. exact (sdiv_havoc _ s H).
Qed.

Theorem diverges_iff_sdiverges : forall c s, diverges c s <-> sdiverges c s.
Proof. split; [apply diverges_sdiverges | apply sdiverges_diverges]. Qed.

(** Imp's bottom-face semantics, stated with the small-step semantics
    alone. *)
Theorem semB_small : forall c o o',
    semB c o o' <->
    match o, o' with
    | None, None => True
    | None, Some _ => False
    | Some s, Some s' => cmulti c s CSkip s'
    | Some s, None => sdiverges c s
    end.
Proof.
  intros c [s|] [s'|]; simpl;
    [apply big_small_equiv | apply diverges_iff_sdiverges | tauto | tauto].
Qed.
