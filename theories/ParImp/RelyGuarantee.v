(** * Rely/guarantee: thread-modular reasoning for concurrent Imp

    The small-step route into the cube ([Core.SmallStepCore]) turns a
    concurrent program into one loop over configurations, so its proofs
    use global invariants over every thread's position. This file adds
    thread-modular reasoning, in the style of Jones's rely/guarantee,
    and connects it to the cube.

    A judgment [rg R G P c Q] says: if [c] starts in [P], and every step
    of its environment (the other threads) satisfies the rely [R], then
    every step of [c] satisfies the guarantee [G], and if [c] finishes,
    it finishes in [Q]. Validity ([rg_valid]) is stated directly on
    concurrent Imp's interleaving semantics ([pstep]), with environment
    steps interleaved ([reach]).

    - [rg_sound]: every rule is sound. The parallel rule verifies each
      thread separately: each thread's guarantee must be allowed by the
      other's rely ([RG_Par]).
    - [rg_closed_hl]: a closed program (no environment, rely [False])
      proved with rely/guarantee has a valid Hoare triple in the cube's
      sense, for the concurrent language itself.
    - [rg_derive_HL]: so it has a derivation in any Hoare-logic record
      for the encoded program, and from there every other corner is
      computed by the transformers.

    Preconditions and postconditions of each rule are required to be
    stable under the rely where the environment can interfere, and the
    guarantee must be reflexive, since some program steps (unfolding a
    loop, leaving a [skip]) do not change the state. All of it is
    axiom-free. *)

From LogicTransformers.Imp Require Import Syntax.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Relational Verified.
From LogicTransformers.Core Require Import Kernel SmallStepCore.
From LogicTransformers.ParImp Require Import ParImp.

Definition srel := state -> state -> Prop.

Definition stable (R : srel) (P : state -> Prop) : Prop :=
  forall s s', P s -> R s s' -> P s'.

(** Configurations reached from [k0] by program steps and environment
    steps (which change only the state, by [R]). *)
Inductive reach (R : srel) (k0 : pcfg) : pcfg -> Prop :=
  | RRefl : reach R k0 k0
  | RProg : forall k k', reach R k0 k -> pstep k k' -> reach R k0 k'
  | REnv : forall c s s', reach R k0 (c, s) -> R s s' -> reach R k0 (c, s').

Definition rg_valid (R G : srel) (P : state -> Prop) (c : pcom)
    (Q : state -> Prop) : Prop :=
  forall s0 k, P s0 -> reach R (c, s0) k ->
    (forall k', pstep k k' -> G (snd k) (snd k')) /\
    (fst k = PSkip -> Q (snd k)).

Lemma reach_mono : forall (R R' : srel) k0 k,
    (forall s s', R s s' -> R' s s') -> reach R k0 k -> reach R' k0 k.
Proof.
  intros R R' k0 k HR H. induction H.
  - apply RRefl.
  - eapply RProg; eassumption.
  - eapply REnv; [eassumption | apply HR; assumption].
Qed.

Ltac pinv1 H := inversion H; subst; clear H.

(** ** The rules, each sound *)

Lemma rg_skip_sound : forall R G P,
    stable R P -> rg_valid R G P PSkip P.
Proof.
  intros R G P HP s0 k H0 Hr.
  assert (Hk : fst k = PSkip /\ P (snd k)).
  { induction Hr as [| k k' _ IH Hs | c s s' _ IH HR].
    - auto.
    - destruct IH as [E _]. destruct k as [c s]. simpl in E. subst c.
      inversion Hs.
    - destruct IH as [E Hp]. simpl in *. split; [exact E | eapply HP; eauto]. }
  destruct Hk as [E Hp]. split; [| intros _; exact Hp].
  intros k' Hs. destruct k as [c s]. simpl in E. subst c. inversion Hs.
Qed.

Lemma rg_asgn_sound : forall R G (P Q : state -> Prop) x a,
    stable R P -> stable R Q ->
    (forall s, P s ->
       Q (update s x (aeval s a)) /\ G s (update s x (aeval s a))) ->
    rg_valid R G P (PAsgn x a) Q.
Proof.
  intros R G P Q x a HP HQ Hs s0 k H0 Hr.
  assert (Hk : (fst k = PAsgn x a /\ P (snd k)) \/
               (fst k = PSkip /\ Q (snd k))).
  { induction Hr as [| k k' _ IH Hst | c s s' _ IH HR].
    - left. auto.
    - destruct k as [c s]. destruct IH as [[E Hp] | [E Hq]]; simpl in E;
        subst c; pinv1 Hst.
      right. split; [reflexivity | exact (proj1 (Hs s Hp))].
    - destruct IH as [[E Hp] | [E Hq]]; [left | right]; simpl in *;
        split; try exact E; eauto. }
  destruct k as [c s]. simpl in *.
  destruct Hk as [[E Hp] | [E Hq]]; subst c.
  - split; [| discriminate]. intros k' Hst. pinv1 Hst.
    exact (proj2 (Hs s Hp)).
  - split; [intros k' Hst; inversion Hst | intros _; exact Hq].
Qed.

Lemma rg_seq_sound : forall R G P M Q c1 c2,
    (forall s, G s s) ->
    rg_valid R G P c1 M -> rg_valid R G M c2 Q ->
    rg_valid R G P (PSeq c1 c2) Q.
Proof.
  intros R G P M Q c1 c2 HG H1 H2 s0 k H0 Hr.
  assert (Hk : (exists c1', fst k = PSeq c1' c2 /\
                            reach R (c1, s0) (c1', snd k)) \/
               (exists s1, reach R (c1, s0) (PSkip, s1) /\
                           reach R (c2, s1) k)).
  { induction Hr as [| k k' _ IH Hst | c s s' _ IH HR].
    - left. exists c1. split; [reflexivity | apply RRefl].
    - destruct k as [c s]. destruct IH as [[c1' [E Hr1]] | [s1 [Hr1 Hr2]]].
      + simpl in E, Hr1. subst c. pinv1 Hst.
        * right. exists s. split; [exact Hr1 | apply RRefl].
        * left. eexists. split; [reflexivity |]. simpl.
          eapply RProg; eassumption.
      + right. exists s1. split; [exact Hr1 | eapply RProg; eassumption].
    - destruct IH as [[c1' [E Hr1]] | [s1 [Hr1 Hr2]]].
      + left. exists c1'. split; [exact E |]. simpl in *. subst c.
        eapply REnv; eassumption.
      + right. exists s1. split; [exact Hr1 | eapply REnv; eassumption]. }
  destruct Hk as [[c1' [E Hr1]] | [s1 [Hr1 Hr2]]].
  - destruct k as [c s]. simpl in E, Hr1 |- *. subst c.
    split; [| discriminate]. intros k' Hst. pinv1 Hst.
    + apply HG.
    + exact (proj1 (H1 s0 _ H0 Hr1) _ ltac:(eassumption)).
  - apply (H2 s1 k); [| exact Hr2].
    exact (proj2 (H1 s0 _ H0 Hr1) eq_refl).
Qed.

Lemma rg_if_sound : forall R G P Q b c1 c2,
    (forall s, G s s) -> stable R P ->
    rg_valid R G (fun s => P s /\ beval s b = true) c1 Q ->
    rg_valid R G (fun s => P s /\ beval s b = false) c2 Q ->
    rg_valid R G P (PIf b c1 c2) Q.
Proof.
  intros R G P Q b c1 c2 HG HP H1 H2 s0 k H0 Hr.
  assert (Hk : (fst k = PIf b c1 c2 /\ P (snd k)) \/
               (exists s1, (P s1 /\ beval s1 b = true) /\
                           reach R (c1, s1) k) \/
               (exists s1, (P s1 /\ beval s1 b = false) /\
                           reach R (c2, s1) k)).
  { induction Hr as [| k k' _ IH Hst | c s s' _ IH HR].
    - left. auto.
    - destruct k as [c s].
      destruct IH as [[E Hp] | [[s1 [Hp1 Hr1]] | [s1 [Hp1 Hr1]]]].
      + simpl in E, Hp. subst c. pinv1 Hst.
        * right. left. exists s. split; [auto | apply RRefl].
        * right. right. exists s. split; [auto | apply RRefl].
      + right. left. exists s1. split; [exact Hp1 | eapply RProg; eassumption].
      + right. right. exists s1.
        split; [exact Hp1 | eapply RProg; eassumption].
    - destruct IH as [[E Hp] | [[s1 [Hp1 Hr1]] | [s1 [Hp1 Hr1]]]].
      + left. simpl in *. split; [exact E | eapply HP; eassumption].
      + right. left. exists s1. split; [exact Hp1 | eapply REnv; eassumption].
      + right. right. exists s1.
        split; [exact Hp1 | eapply REnv; eassumption]. }
  destruct Hk as [[E Hp] | [[s1 [Hp1 Hr1]] | [s1 [Hp1 Hr1]]]].
  - destruct k as [c s]. simpl in E |- *. subst c.
    split; [| discriminate]. intros k' Hst. pinv1 Hst; apply HG.
  - exact (H1 s1 k Hp1 Hr1).
  - exact (H2 s1 k Hp1 Hr1).
Qed.

Lemma rg_while_sound : forall R G (I : state -> Prop) b c,
    (forall s, G s s) -> stable R I ->
    stable R (fun s => I s /\ beval s b = false) ->
    rg_valid R G (fun s => I s /\ beval s b = true) c I ->
    rg_valid R G I (PWhile b c) (fun s => I s /\ beval s b = false).
Proof.
  intros R G I b c HG HI HE Hb s0 k H0 Hr.
  set (W := PWhile b c).
  set (U := PIf b (PSeq c W) PSkip).
  assert (Hk : (fst k = W /\ I (snd k)) \/ (fst k = U /\ I (snd k)) \/
               (exists c' s1, fst k = PSeq c' W /\
                  (I s1 /\ beval s1 b = true) /\ reach R (c, s1) (c', snd k)) \/
               (fst k = PSkip /\ I (snd k) /\ beval (snd k) b = false)).
  { induction Hr as [| k k' _ IH Hst | cc s s' _ IH HR].
    - left. auto.
    - destruct k as [cc s].
      destruct IH as [[E Hi] | [[E Hi] | [[c' [s1 [E [Hp1 Hr1]]]] |
                                         [E [Hi Hf]]]]];
        cbn [fst snd] in *; subst cc.
      + pinv1 Hst. right. left. auto.
      + pinv1 Hst.
        * right. right. left. exists c, s.
          split; [reflexivity |]. split; [auto | apply RRefl].
        * right. right. right. auto.
      + simpl in Hr1. pinv1 Hst.
        * left. split; [reflexivity |].
          exact (proj2 (Hb s1 _ Hp1 Hr1) eq_refl).
        * right. right. left. eexists _, s1. split; [reflexivity |].
          split; [exact Hp1 | simpl; eapply RProg; eassumption].
      + inversion Hst.
    - destruct IH as [[E Hi] | [[E Hi] | [[c' [s1 [E [Hp1 Hr1]]]] |
                                         [E [Hi Hf]]]]]; simpl in *.
      + left. split; [exact E | eapply HI; eassumption].
      + right. left. split; [exact E | eapply HI; eassumption].
      + right. right. left. exists c', s1. split; [exact E |].
        split; [exact Hp1 | eapply REnv; eassumption].
      + right. right. right. split; [exact E |].
        exact (HE s s' (conj Hi Hf) HR). }
  destruct k as [cc s].
  destruct Hk as [[E Hi] | [[E Hi] | [[c' [s1 [E [Hp1 Hr1]]]] |
                                     [E [Hi Hf]]]]];
    cbn [fst snd] in *; subst cc.
  - split; [| discriminate]. intros k' Hst. pinv1 Hst. apply HG.
  - split; [| discriminate]. intros k' Hst. pinv1 Hst; apply HG.
  - split; [| discriminate]. intros k' Hst. pinv1 Hst.
    + apply HG.
    + exact (proj1 (Hb s1 _ Hp1 Hr1) _ ltac:(eassumption)).
  - split; [intros k' Hst; inversion Hst | intros _; auto].
Qed.

Lemma rg_par_sound : forall R G R1 G1 R2 G2 P1 P2 Q1 Q2 c1 c2,
    (forall s, G s s) ->
    (forall s s', R s s' \/ G2 s s' -> R1 s s') ->
    (forall s s', R s s' \/ G1 s s' -> R2 s s') ->
    (forall s s', G1 s s' \/ G2 s s' -> G s s') ->
    rg_valid R1 G1 P1 c1 Q1 -> rg_valid R2 G2 P2 c2 Q2 ->
    rg_valid R G (fun s => P1 s /\ P2 s) (PPar c1 c2)
      (fun s => Q1 s /\ Q2 s).
Proof.
  intros R G R1 G1 R2 G2 P1 P2 Q1 Q2 c1 c2 HG HR1 HR2 HGG H1 H2
    s0 k [H01 H02] Hr.
  assert (Hk : (exists c1' c2', fst k = PPar c1' c2' /\
                  reach R1 (c1, s0) (c1', snd k) /\
                  reach R2 (c2, s0) (c2', snd k)) \/
               (fst k = PSkip /\ reach R1 (c1, s0) (PSkip, snd k) /\
                reach R2 (c2, s0) (PSkip, snd k))).
  { induction Hr as [| k k' _ IH Hst | c s s' _ IH HR].
    - left. exists c1, c2. split; [reflexivity |]. split; apply RRefl.
    - destruct k as [c s].
      destruct IH as [[c1' [c2' [E [Hr1 Hr2]]]] | [E [Hr1 Hr2]]];
        simpl in E, Hr1, Hr2; subst c; [| inversion Hst].
      pinv1 Hst.
      + left. eexists _, c2'. split; [reflexivity |]. simpl. split.
        * eapply RProg; eassumption.
        * eapply REnv; [exact Hr2 |]. apply HR2. right.
          exact (proj1 (H1 s0 _ H01 Hr1) _ ltac:(eassumption)).
      + left. exists c1'. eexists. split; [reflexivity |]. simpl. split.
        * eapply REnv; [exact Hr1 |]. apply HR1. right.
          exact (proj1 (H2 s0 _ H02 Hr2) _ ltac:(eassumption)).
        * eapply RProg; eassumption.
      + right. auto.
    - destruct IH as [[c1' [c2' [E [Hr1 Hr2]]]] | [E [Hr1 Hr2]]];
        simpl in *.
      + left. exists c1', c2'. split; [exact E |]. split.
        * eapply REnv; [exact Hr1 | apply HR1; left; exact HR].
        * eapply REnv; [exact Hr2 | apply HR2; left; exact HR].
      + right. split; [exact E |]. split.
        * eapply REnv; [exact Hr1 | apply HR1; left; exact HR].
        * eapply REnv; [exact Hr2 | apply HR2; left; exact HR]. }
  destruct k as [c s].
  destruct Hk as [[c1' [c2' [E [Hr1 Hr2]]]] | [E [Hr1 Hr2]]];
    simpl in E, Hr1, Hr2 |- *; subst c.
  - split; [| discriminate]. intros k' Hst. pinv1 Hst.
    + apply HGG. left. exact (proj1 (H1 s0 _ H01 Hr1) _ ltac:(eassumption)).
    + apply HGG. right. exact (proj1 (H2 s0 _ H02 Hr2) _ ltac:(eassumption)).
    + apply HG.
  - split; [intros k' Hst; inversion Hst |]. intros _.
    split; [exact (proj2 (H1 s0 _ H01 Hr1) eq_refl)
           | exact (proj2 (H2 s0 _ H02 Hr2) eq_refl)].
Qed.

Lemma rg_cons_sound : forall R R' G G' P P' Q Q' c,
    (forall s, P s -> P' s) -> (forall s s', R s s' -> R' s s') ->
    (forall s s', G' s s' -> G s s') -> (forall s, Q' s -> Q s) ->
    rg_valid R' G' P' c Q' -> rg_valid R G P c Q.
Proof.
  intros R R' G G' P P' Q Q' c HP HR HG HQ H s0 k H0 Hr.
  destruct (H s0 k (HP s0 H0) (reach_mono R R' _ _ HR Hr)) as [Hg Hq].
  split; [intros k' Hst; apply HG, Hg, Hst | intros E; apply HQ, Hq, E].
Qed.

(** ** The proof system *)

Inductive rg : srel -> srel -> (state -> Prop) -> pcom ->
               (state -> Prop) -> Prop :=
  | RG_Skip : forall R G P, stable R P -> rg R G P PSkip P
  | RG_Asgn : forall R G (P Q : state -> Prop) x a,
      stable R P -> stable R Q ->
      (forall s, P s ->
         Q (update s x (aeval s a)) /\ G s (update s x (aeval s a))) ->
      rg R G P (PAsgn x a) Q
  | RG_Seq : forall R G P M Q c1 c2,
      (forall s, G s s) -> rg R G P c1 M -> rg R G M c2 Q ->
      rg R G P (PSeq c1 c2) Q
  | RG_If : forall R G P Q b c1 c2,
      (forall s, G s s) -> stable R P ->
      rg R G (fun s => P s /\ beval s b = true) c1 Q ->
      rg R G (fun s => P s /\ beval s b = false) c2 Q ->
      rg R G P (PIf b c1 c2) Q
  | RG_While : forall R G (I : state -> Prop) b c,
      (forall s, G s s) -> stable R I ->
      stable R (fun s => I s /\ beval s b = false) ->
      rg R G (fun s => I s /\ beval s b = true) c I ->
      rg R G I (PWhile b c) (fun s => I s /\ beval s b = false)
  | RG_Par : forall R G R1 G1 R2 G2 P1 P2 Q1 Q2 c1 c2,
      (forall s, G s s) ->
      (forall s s', R s s' \/ G2 s s' -> R1 s s') ->
      (forall s s', R s s' \/ G1 s s' -> R2 s s') ->
      (forall s s', G1 s s' \/ G2 s s' -> G s s') ->
      rg R1 G1 P1 c1 Q1 -> rg R2 G2 P2 c2 Q2 ->
      rg R G (fun s => P1 s /\ P2 s) (PPar c1 c2) (fun s => Q1 s /\ Q2 s)
  | RG_Cons : forall R R' G G' P P' Q Q' c,
      (forall s, P s -> P' s) -> (forall s s', R s s' -> R' s s') ->
      (forall s s', G' s s' -> G s s') -> (forall s, Q' s -> Q s) ->
      rg R' G' P' c Q' -> rg R G P c Q.

Theorem rg_sound : forall R G P c Q, rg R G P c Q -> rg_valid R G P c Q.
Proof.
  intros R G P c Q H. induction H.
  - apply rg_skip_sound; assumption.
  - apply rg_asgn_sound; assumption.
  - eapply rg_seq_sound; eassumption.
  - apply rg_if_sound; assumption.
  - apply rg_while_sound; assumption.
  - exact (rg_par_sound R G R1 G1 R2 G2 P1 P2 Q1 Q2 c1 c2
               H H0 H1 H2 IHrg1 IHrg2).
  - eapply rg_cons_sound; eassumption.
Qed.

(** ** Into the cube *)

Lemma smulti_reach : forall (R : srel) k0 k1 k2,
    reach R k0 k1 -> smulti pstep k1 k2 -> reach R k0 k2.
Proof.
  intros R k0 k1 k2 H1 H2. revert H1. induction H2; intros H1;
    [exact H1 | apply IHsmulti; eapply RProg; eassumption].
Qed.

(** A closed program (no environment) verified thread-modularly has a
    valid Hoare triple, for concurrent Imp itself. *)
Theorem rg_closed_hl : forall G P c Q,
    rg_valid (fun _ _ => False) G P c Q ->
    cvalid Forward Plain Over (@mkTriple ParImp P c Q).
Proof.
  intros G P c Q H. apply cvalid_cvr. simpl. intros s s' HP Hm.
  apply (proj2 (H s (PSkip, s') HP (smulti_reach _ _ _ _ (RRefl _ _) Hm))).
  reflexivity.
Qed.

(** So it has a derivation in any Hoare-logic record for the encoded
    program; every other corner is then computed by the transformers. *)
Corollary rg_derive_HL :
    forall (V : VLogic (KLang pact_sem) Forward Plain Over) G P c Q,
    rg (fun _ _ => False) G P c Q ->
    derivable (rules (vl_logic V))
      (@mkTriple (KLang pact_sem) (fun k => P (snd k)) (penc c)
         (liftG snd pfin Forward Plain Over Q)).
Proof.
  intros V G P c Q H. apply vl_derive.
  apply (penc_cvalid Forward Plain Over).
  exact (rg_closed_hl G P c Q (rg_sound _ _ _ _ _ H)).
Qed.
