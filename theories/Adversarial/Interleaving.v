(** * Adversarial logic: victim and adversary, interleaved

    The victim and the adversary run together. A configuration is the
    pair of residual programs and the state. A step is a small step of
    the victim ([tstep Victim]), a small step of the adversary
    ([tstep Adversary]), or a channel transfer ([com]): a value moves
    from the head of one side's channel to the tail of the other's.
    Transfers can happen at any time, including after both programs have
    finished.

    Only the language is defined here; the logic is generated. The
    interleaved run, as a segment, is a core program ([Core.StepCore]),
    and [Examples.Common] turns any core language into all sixteen
    corners by transformers. Interleaved adversarial logic is the
    generated IL record [AILv], obtained from the generated HL record by
    [vto]:

    - [ail P (c1, c2) (d1, d2) Q] is derivability in [AILv]: every state
      in [Q] is reached, from some state in [P], by an interleaved run
      from residuals [(c1, c2)] to [(d1, d2)]. A triple about the victim
      against the adversary is the case [d1 = d2 = skip];
    - [ail_iff]: soundness and completeness, read off the record;
    - its rules are the segment rules of [Core.StepCore], which hold
      for every step relation ([sprov_trans], [sprov_step],
      [sprov_embed], ...); ILAL's interleaving rules ([iderivable]:
      reflexivity, transitivity, consequence, infinitary disjunction, a
      step of either side, a transfer) hold as well;
    - the language supplies only facts about its steps: a thread's run
      is a run of the interleaving ([thread_l], [prefix_l], ...), and
      what a transfer does ([com_va], [com_av]).

    The generated records use [classic] (through [Examples.Common]); the
    language and the segment encoding are axiom-free. *)

From Stdlib Require Import String List.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Relational Verified.
From LogicTransformers.Core Require Import Kernel StepCore Rules.
From LogicTransformers.Examples Require Import Common.
From LogicTransformers.Adversarial Require Import AL.
Import ListNotations.

(** ** Small steps of one thread *)

Inductive tstep (m : mode) : tcom * estate -> tcom * estate -> Prop :=
  | TS_Atom : forall a σ σ', asem m a σ σ' -> tstep m (TAtom a, σ) (TSkip, σ')
  | TS_Assume : forall B σ, massume m B σ -> tstep m (TAssume B, σ) (TSkip, σ)
  | TS_SeqSkip : forall c σ, tstep m (TSeq TSkip c, σ) (c, σ)
  | TS_Seq : forall c1 c1' c2 σ σ',
      tstep m (c1, σ) (c1', σ') -> tstep m (TSeq c1 c2, σ) (TSeq c1' c2, σ')
  | TS_ChoiceL : forall c1 c2 σ, tstep m (TChoice c1 c2, σ) (c1, σ)
  | TS_ChoiceR : forall c1 c2 σ, tstep m (TChoice c1 c2, σ) (c2, σ)
  | TS_Star0 : forall c σ, tstep m (TStar c, σ) (TSkip, σ)
  | TS_StarN : forall c σ, tstep m (TStar c, σ) (TSeq c (TStar c), σ)
  | TS_Local : forall x e c σ,
      tstep m (TLocal x e c, σ)
        (TSeq (TAtom (AAsgn x e)) (TSeq c (TAtom (ARand x))), σ).

(** ** Channel transfers *)

Inductive com : estate -> estate -> Prop :=
  | ComVA : forall c v l σ,
      vch σ c = v :: l ->
      com σ (mkE (vs σ) (cupd (vch σ) c l)
                 (avs σ) (cupd (ach σ) c (ach σ c ++ [v])))
  | ComAV : forall c v l σ,
      ach σ c = v :: l ->
      com σ (mkE (vs σ) (cupd (vch σ) c (vch σ c ++ [v]))
                 (avs σ) (cupd (ach σ) c l)).

(** ** Interleaved steps, and the segment language *)

Notation conf := ((tcom * tcom) * estate)%type.

Inductive istep : conf -> conf -> Prop :=
  | IS_L : forall c1 c1' c2 σ σ',
      tstep Victim (c1, σ) (c1', σ') -> istep ((c1, c2), σ) ((c1', c2), σ')
  | IS_R : forall c1 c2 c2' σ σ',
      tstep Adversary (c2, σ) (c2', σ') -> istep ((c1, c2), σ) ((c1, c2'), σ')
  | IS_Com : forall p σ σ', com σ σ' -> istep (p, σ) (p, σ').

Definition ALang : Language := Seg istep.

Definition aval (P : estate -> Prop) (p q : tcom * tcom) (Q : estate -> Prop)
  : Prop :=
  forall σ', Q σ' -> exists σ, P σ /\ steps istep (p, σ) (q, σ').

(** ** The generated logic *)

Notation asem2 := (tact_sem istep).

Definition AILv : VLogic (KLang asem2) Forward Plain Under := ILv asem2.

Definition ail : (estate -> Prop) -> tcom * tcom -> tcom * tcom ->
                (estate -> Prop) -> Prop := sprov istep AILv.

Theorem ail_iff : forall P p q Q, ail P p q Q <-> aval P p q Q.
Proof. intros. apply sprov_iff. Qed.

(** ** ILAL's interleaving rules, as lemmas *)

Lemma ail_refl : forall P p, ail P p p P.
Proof.
  intros P p. apply ail_iff. intros σ' HQ.
  exists σ'. split; [exact HQ | apply ST_Refl].
Qed.

Lemma ail_trans : forall P R Q p q r,
    ail P p q R -> ail R q r Q -> ail P p r Q.
Proof.
  intros P R Q p q r H1 H2. apply ail_iff in H1, H2. apply ail_iff.
  intros σ' HQ. destruct (H2 σ' HQ) as [σ1 [HR K2]].
  destruct (H1 σ1 HR) as [σ [HP K1]].
  exists σ. split; [exact HP | eapply steps_trans; eassumption].
Qed.

Lemma ail_cons : forall P P' Q Q' p q,
    (forall σ, P σ -> P' σ) -> (forall σ, Q' σ -> Q σ) ->
    ail P p q Q -> ail P' p q Q'.
Proof.
  intros P P' Q Q' p q HP HQ H. apply ail_iff in H. apply ail_iff.
  intros σ' Hq. destruct (H σ' (HQ σ' Hq)) as [σ [Hp Hs]]. eauto.
Qed.

Lemma ail_disj_all : forall (I : Type) P (Qi : I -> estate -> Prop) p q,
    (forall i, ail P p q (Qi i)) -> ail P p q (fun σ => exists i, Qi i σ).
Proof.
  intros I P Qi p q H. apply ail_iff. intros σ' [i HQ].
  exact (proj1 (ail_iff _ _ _ _) (H i) σ' HQ).
Qed.

Lemma ail_step_l : forall P c1 c1' c2,
    ail P (c1, c2) (c1', c2)
        (fun σ' => exists σ, P σ /\ tstep Victim (c1, σ) (c1', σ')).
Proof.
  intros. apply ail_iff. intros σ' [σ [HP Hs]]. exists σ.
  split; [exact HP | eapply ST_Step; [apply IS_L, Hs | apply ST_Refl]].
Qed.

Lemma ail_step_r : forall P c1 c2 c2',
    ail P (c1, c2) (c1, c2')
        (fun σ' => exists σ, P σ /\ tstep Adversary (c2, σ) (c2', σ')).
Proof.
  intros. apply ail_iff. intros σ' [σ [HP Hs]]. exists σ.
  split; [exact HP | eapply ST_Step; [apply IS_R, Hs | apply ST_Refl]].
Qed.

Lemma ail_com : forall P p,
    ail P p p (fun σ' => exists σ, P σ /\ com σ σ').
Proof.
  intros. apply ail_iff. intros σ' [σ [HP Hs]]. exists σ.
  split; [exact HP | eapply ST_Step; [apply IS_Com, Hs | apply ST_Refl]].
Qed.

(** ** From thread runs to interleaved runs

    A big-step run of a thread ([kev] of its encoding) is a small-step
    run of [tstep] ([kev_tsteps]), and a thread's run is a run of the
    interleaving with the other side frozen ([lift_l], [lift_r]). Worked
    attacks are built from these pieces. *)

Lemma tsteps_seq : forall m c1 c2 σ σ',
    steps (tstep m) (c1, σ) (TSkip, σ') ->
    steps (tstep m) (TSeq c1 c2, σ) (c2, σ').
Proof.
  intros m c1 c2 σ σ' H.
  remember (c1, σ) as k eqn:Ek. remember (TSkip, σ') as k' eqn:Ek'.
  revert c1 σ Ek. induction H as [k | k [c1' σ1] k2 Hs _ IH];
    intros c1 σ Ek; subst.
  - injection Ek; intros; subst.
    eapply ST_Step; [apply TS_SeqSkip | apply ST_Refl].
  - eapply ST_Step; [apply TS_Seq, Hs | eapply IH; reflexivity].
Qed.

Lemma kev_tsteps : forall m c σ σ', kev (asem m) (tenc m c) σ σ' ->
    steps (tstep m) (c, σ) (TSkip, σ').
Proof.
  intros m c. induction c as [| a | B | c1 IH1 c2 IH2 | c1 IH1 c2 IH2
                             | c IH | x e c IH]; simpl; intros σ σ' H.
  - inversion H; subst. apply ST_Refl.
  - inversion H; subst.
    eapply ST_Step; [apply TS_Atom; eassumption | apply ST_Refl].
  - inversion H; subst.
    eapply ST_Step; [apply TS_Assume; eassumption | apply ST_Refl].
  - inversion H; subst. eapply steps_trans;
      [apply tsteps_seq, IH1; eassumption | apply IH2; eassumption].
  - inversion H; subst.
    + eapply ST_Step; [apply TS_ChoiceL | apply IH1; assumption].
    + eapply ST_Step; [apply TS_ChoiceR | apply IH2; assumption].
  - remember (KStar (tenc m c)) as k eqn:Ek.
    induction H; inversion Ek; subst.
    + eapply ST_Step; [apply TS_Star0 | apply ST_Refl].
    + eapply ST_Step; [apply TS_StarN |]. eapply steps_trans;
        [apply tsteps_seq, IH; eassumption | apply IHkev2; reflexivity].
  - eapply ST_Step; [apply TS_Local |].
    inversion H as [| | | ? ? ? σ1 ? Ha Hr | | | |]; subst.
    inversion Ha; subst.
    inversion Hr as [| | | ? ? ? σ2 ? Hc Hx | | | |]; subst.
    inversion Hx; subst.
    eapply steps_trans; [apply tsteps_seq; eapply ST_Step;
      [apply TS_Atom; eassumption | apply ST_Refl] |].
    eapply steps_trans; [apply tsteps_seq, IH; eassumption |].
    eapply ST_Step; [apply TS_Atom; eassumption | apply ST_Refl].
Qed.

(** Running a prefix [c1] of [c1 ; c2] by big step. *)
Corollary kev_prefix : forall m c1 c2 σ σ',
    kev (asem m) (tenc m c1) σ σ' ->
    steps (tstep m) (TSeq c1 c2, σ) (c2, σ').
Proof. intros. apply tsteps_seq, kev_tsteps. assumption. Qed.

Lemma lift_l : forall c1 c1' c2 σ σ',
    steps (tstep Victim) (c1, σ) (c1', σ') ->
    steps istep ((c1, c2), σ) ((c1', c2), σ').
Proof.
  intros c1 c1' c2 σ σ' H.
  remember (c1, σ) as k eqn:Ek. remember (c1', σ') as k' eqn:Ek'.
  revert c1 σ Ek. induction H as [k | k [d σ1] k2 Hs _ IH];
    intros c1 σ Ek; subst.
  - injection Ek; intros; subst. apply ST_Refl.
  - eapply ST_Step; [apply IS_L, Hs | eapply IH; reflexivity].
Qed.

Lemma lift_r : forall c1 c2 c2' σ σ',
    steps (tstep Adversary) (c2, σ) (c2', σ') ->
    steps istep ((c1, c2), σ) ((c1, c2'), σ').
Proof.
  intros c1 c2 c2' σ σ' H.
  remember (c2, σ) as k eqn:Ek. remember (c2', σ') as k' eqn:Ek'.
  revert c2 σ Ek. induction H as [k | k [d σ1] k2 Hs _ IH];
    intros c2 σ Ek; subst.
  - injection Ek; intros; subst. apply ST_Refl.
  - eapply ST_Step; [apply IS_R, Hs | eapply IH; reflexivity].
Qed.

Lemma com_steps : forall p σ σ', com σ σ' -> steps istep (p, σ) (p, σ').
Proof. intros. eapply ST_Step; [apply IS_Com; eassumption | apply ST_Refl]. Qed.

(** ** Facts about the interleaving

    Facts about [istep], not rules. A thread's run is a run of the
    interleaving with the other side waiting, in full or as the first
    part of a sequence; and a transfer is a step. Proofs feed them to
    the generic segment rules ([sprov_embed], [sprov_step]). *)

Lemma thread_l : forall c d σ σ', kev (asem Victim) (tenc Victim c) σ σ' ->
    steps istep ((c, d), σ) ((TSkip, d), σ').
Proof. intros. apply lift_l, kev_tsteps. assumption. Qed.

Lemma prefix_l : forall c k d σ σ',
    kev (asem Victim) (tenc Victim c) σ σ' ->
    steps istep ((TSeq c k, d), σ) ((k, d), σ').
Proof. intros. apply lift_l, kev_prefix. assumption. Qed.

Lemma thread_r : forall c d σ σ',
    kev (asem Adversary) (tenc Adversary c) σ σ' ->
    steps istep ((d, c), σ) ((d, TSkip), σ').
Proof. intros. apply lift_r, kev_tsteps. assumption. Qed.

Lemma prefix_r : forall c k d σ σ',
    kev (asem Adversary) (tenc Adversary c) σ σ' ->
    steps istep ((d, TSeq c k), σ) ((d, k), σ').
Proof. intros. apply lift_r, kev_prefix. assumption. Qed.

(** Transfers, in value form. *)

Lemma com_va : forall p σ c v l l', vch σ c = v :: l -> ach σ c = l' ->
    istep (p, σ)
      (p, mchupd Adversary (mchupd Victim σ c l) c (l' ++ [v])).
Proof.
  intros p σ c v l l' H <-. apply IS_Com.
  destruct σ as [a b d e]. simpl in *. exact (ComVA c v l (mkE a b d e) H).
Qed.

Lemma com_av : forall p σ c v l l', ach σ c = v :: l -> vch σ c = l' ->
    istep (p, σ)
      (p, mchupd Adversary (mchupd Victim σ c (l' ++ [v])) c l).
Proof.
  intros p σ c v l l' H <-. apply IS_Com.
  destruct σ as [a b d e]. simpl in *. exact (ComAV c v l (mkE a b d e) H).
Qed.

(** ** Attacks

    [attack P (c1, c2) Q]: the adversary [c2] can drive the victim [c1]
    to an outcome in [Q]. It is an adversarial-logic triple with a
    nonempty postcondition inside [Q]: some final state [σf] in [Q] is
    reached, from [P], by a complete interleaved run. *)

Definition attack (P : estate -> Prop) (p : tcom * tcom)
    (Q : estate -> Prop) : Prop :=
  exists σf, Q σf /\ ail P p (TSkip, TSkip) (only σf).

Lemma attack_intro : forall (P Q : estate -> Prop) p σf,
    ail P p (TSkip, TSkip) (only σf) -> Q σf -> attack P p Q.
Proof. intros. exists σf. auto. Qed.

