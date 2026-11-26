(** * A complete rely/guarantee logic, generated

    Rely/guarantee validity ([RelyGuarantee.rg_valid]) is not about a
    program's start and end states alone: the guarantee constrains every
    step. It becomes a cube validity with an error outcome. For a rely
    [R] and guarantee [G], [rgstep R G] steps a configuration of a
    residual program and an optional state:
    - a program step that satisfies [G] is taken as is;
    - a program step that violates [G] jumps to [(skip, None)];
    - an environment step allowed by [R] changes the state only.

    [rg_valid_iff]: [R, G ⊢ {P} c {Q}] is valid exactly when the Hoare
    triple [{P} (c, skip) {Q, and not None}] holds for the segment
    language of [rgstep R G] ([Core.StepCore]). That language is a core
    instance, so the transformers generate all sixteen logics for it.
    The Hoare-logic one, [RGv R G], is a rely/guarantee logic:

    - [rgprov_iff]: it is sound and complete for rely/guarantee
      validity;
    - [rgprov_skip], ..., [rgprov_par], [rgprov_cons]: Jones's rules,
      parallel composition included, hold in it, so [rg_embed] turns
      every rely/guarantee derivation into one in [RGv];
    - [inc2_rgprov]: it proves [{x = 0} x := x+1 ∥ x := x+1 {x = 2}],
      which no rely/guarantee derivation proves without auxiliary
      variables ([RGIncomplete.inc2_not_rg]); so [RGv] is strictly
      stronger than Jones's rules alone ([rg_generated_stronger]).

    Its completeness comes from the generated rules about the whole
    configuration's steps, not from the parallel rule: a proof in [RGv]
    may use thread-modular steps where they suffice and global ones
    where they do not. The other corners come with it: for example
    [RGILv R G] is incorrectness logic under interference.

    [classic] decides whether a step meets the guarantee; the generated
    records use it too. *)

From Stdlib Require Import String Arith Lia Classical.
From LogicTransformers.Imp Require Import Syntax.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Relational Verified.
From LogicTransformers.Core Require Import
  Kernel Rules SmallStepCore StepCore.
From LogicTransformers.Examples Require Import Common.
From LogicTransformers.ParImp Require Import
  ParImp RelyGuarantee RGIncomplete.

(** ** Steps under a rely, checking a guarantee *)

Notation rcfg := (pcom * option state)%type.

Inductive rgstep (R G : srel) : rcfg -> rcfg -> Prop :=
  | RGS_Prog : forall c c' s s',
      pstep (c, s) (c', s') -> G s s' ->
      rgstep R G (c, Some s) (c', Some s')
  | RGS_Bad : forall c c' s s',
      pstep (c, s) (c', s') -> ~ G s s' ->
      rgstep R G (c, Some s) (PSkip, None)
  | RGS_Env : forall c s s', R s s' ->
      rgstep R G (c, Some s) (c, Some s').

Definition RGLang (R G : srel) : Language := Seg (rgstep R G).

(** Pre on proper states; post on proper states, excluding a broken
    guarantee. *)
Definition lift (P : state -> Prop) (o : option state) : Prop :=
  exists s, o = Some s /\ P s.
Definition okQ (Q : state -> Prop) (o : option state) : Prop :=
  match o with Some s => Q s | None => False end.

Lemma steps_snoc : forall {X Y : Type} (st : X * Y -> X * Y -> Prop) k k1 k2,
    steps st k k1 -> st k1 k2 -> steps st k k2.
Proof.
  intros X Y st k k1 k2 H1 H2. eapply steps_trans; [exact H1 |].
  eapply ST_Step; [exact H2 | apply ST_Refl].
Qed.

Definition rg_hl (R G : srel) (P : state -> Prop) (c : pcom)
    (Q : state -> Prop) : Prop :=
  forall o o', lift P o -> steps (rgstep R G) (c, o) (PSkip, o') -> okQ Q o'.

(** From a valid judgment: runs of [rgstep] stay reachable, and never
    break the guarantee. *)
Lemma rg_runs : forall R G P c Q s0, rg_valid R G P c Q -> P s0 ->
    forall k k', steps (rgstep R G) k k' ->
    forall d s, k = (d, Some s) -> reach R (c, s0) (d, s) ->
    exists d' s', k' = (d', Some s') /\ reach R (c, s0) (d', s').
Proof.
  intros R G P c Q s0 V H0 k k' H. induction H as [k | k k1 k2 Hs _ IH];
    intros d s E Hr; subst.
  - eauto.
  - inversion Hs; subst.
    + eapply IH; [reflexivity | eapply RProg; [exact Hr | eassumption]].
    + exfalso. match goal with Hn : ~ G _ _ |- _ => apply Hn end.
      exact (proj1 (V s0 _ H0 Hr) _ ltac:(eassumption)).
    + eapply IH; [reflexivity | eapply REnv; eassumption].
Qed.

(** To a valid judgment: every reachable configuration is reached by
    [rgstep] without breaking the guarantee. *)
Lemma reach_runs : forall R G P c Q s0, rg_hl R G P c Q -> P s0 ->
    forall k, reach R (c, s0) k ->
    steps (rgstep R G) (c, Some s0) (fst k, Some (snd k)).
Proof.
  intros R G P c Q s0 V H0 k H. induction H as [| [d s] [d' s'] _ IH Hs
                                               | d s s' _ IH HR].
  - apply ST_Refl.
  - simpl in *. eapply steps_snoc; [exact IH |]. apply RGS_Prog; [exact Hs |].
    apply NNPP. intros Hn.
    exact (V (Some s0) None (ex_intro _ s0 (conj eq_refl H0))
             (steps_snoc _ _ _ _ IH (RGS_Bad R G d d' s s' Hs Hn))).
  - simpl in *. eapply steps_snoc; [exact IH | apply RGS_Env, HR].
Qed.

Theorem rg_hl_iff : forall R G P c Q, rg_valid R G P c Q <-> rg_hl R G P c Q.
Proof.
  intros R G P c Q. split.
  - intros V o o' [s0 [-> H0]] Hs.
    destruct (rg_runs R G P c Q s0 V H0 _ _ Hs c s0 eq_refl (RRefl _ _))
      as [d' [s' [E Hr]]].
    injection E; intros; subst. simpl.
    exact (proj2 (V s0 _ H0 Hr) eq_refl).
  - intros V s0 [d s] H0 Hr.
    pose proof (reach_runs R G P c Q s0 V H0 _ Hr) as K.
    simpl in K. split.
    + intros [d' s'] Hs. simpl. apply NNPP. intros Hn.
      exact (V (Some s0) None (ex_intro _ s0 (conj eq_refl H0))
               (steps_snoc _ _ _ _ K (RGS_Bad R G d d' s s' Hs Hn))).
    + simpl. intros ->.
      exact (V (Some s0) (Some s) (ex_intro _ s0 (conj eq_refl H0)) K).
Qed.

Theorem rg_valid_iff : forall R G P c Q,
    rg_valid R G P c Q <->
    cvalid Forward Plain Over
      (@mkTriple (RGLang R G) (lift P) (c, PSkip) (okQ Q)).
Proof.
  intros R G P c Q. rewrite rg_hl_iff, cvalid_cvr. simpl. reflexivity.
Qed.

(** ** The generated logics *)

Notation rsem R G := (tact_sem (rgstep R G)).

Definition RGv (R G : srel) : VLogic (KLang (rsem R G)) Forward Plain Over :=
  HLv (rsem R G).
Definition RGILv (R G : srel)
  : VLogic (KLang (rsem R G)) Forward Plain Under := ILv (rsem R G).

Definition rgprov (R G : srel) (P : state -> Prop) (c : pcom)
    (Q : state -> Prop) : Prop :=
  prov (rsem R G) (RGv R G) (fun k => lift P (snd k)) (segenc (c, PSkip))
    (liftG snd (fun k => fst k = PSkip) Forward Plain Over (okQ Q)).

Theorem rgprov_iff : forall R G P c Q, rgprov R G P c Q <-> rg_valid R G P c Q.
Proof.
  intros R G P c Q. unfold rgprov, prov. rewrite vl_theory.
  rewrite <- (segenc_cvalid (rgstep R G) Forward Plain Over
                (lift P) (okQ Q) (c, PSkip)).
  symmetry. apply rg_valid_iff.
Qed.

(** ** Jones's rules, in the generated logic *)

Section JonesRules.

Ltac via := repeat rewrite rgprov_iff in *.

Lemma rgprov_skip : forall R G P, stable R P -> rgprov R G P PSkip P.
Proof. intros. via. apply rg_skip_sound; assumption. Qed.

Lemma rgprov_asgn : forall R G (P Q : state -> Prop) x a,
    stable R P -> stable R Q ->
    (forall s, P s ->
       Q (update s x (aeval s a)) /\ G s (update s x (aeval s a))) ->
    rgprov R G P (PAsgn x a) Q.
Proof. intros. via. apply rg_asgn_sound; assumption. Qed.

Lemma rgprov_seq : forall R G P M Q c1 c2,
    (forall s, G s s) -> rgprov R G P c1 M -> rgprov R G M c2 Q ->
    rgprov R G P (PSeq c1 c2) Q.
Proof. intros. via. eapply rg_seq_sound; eassumption. Qed.

Lemma rgprov_if : forall R G P Q b c1 c2,
    (forall s, G s s) -> stable R P ->
    rgprov R G (fun s => P s /\ beval s b = true) c1 Q ->
    rgprov R G (fun s => P s /\ beval s b = false) c2 Q ->
    rgprov R G P (PIf b c1 c2) Q.
Proof. intros. via. apply rg_if_sound; assumption. Qed.

Lemma rgprov_while : forall R G (I : state -> Prop) b c,
    (forall s, G s s) -> stable R I ->
    stable R (fun s => I s /\ beval s b = false) ->
    rgprov R G (fun s => I s /\ beval s b = true) c I ->
    rgprov R G I (PWhile b c) (fun s => I s /\ beval s b = false).
Proof. intros. via. apply rg_while_sound; assumption. Qed.

Lemma rgprov_par : forall R G R1 G1 R2 G2 P1 P2 Q1 Q2 c1 c2,
    (forall s, G s s) ->
    (forall s s', R s s' \/ G2 s s' -> R1 s s') ->
    (forall s s', R s s' \/ G1 s s' -> R2 s s') ->
    (forall s s', G1 s s' \/ G2 s s' -> G s s') ->
    rgprov R1 G1 P1 c1 Q1 -> rgprov R2 G2 P2 c2 Q2 ->
    rgprov R G (fun s => P1 s /\ P2 s) (PPar c1 c2) (fun s => Q1 s /\ Q2 s).
Proof.
  intros R G R1 G1 R2 G2 P1 P2 Q1 Q2 c1 c2 HG H1 H2 H3 K1 K2.
  apply rgprov_iff in K1, K2. apply rgprov_iff.
  exact (rg_par_sound R G R1 G1 R2 G2 P1 P2 Q1 Q2 c1 c2 HG H1 H2 H3 K1 K2).
Qed.

Lemma rgprov_cons : forall R R' G G' P P' Q Q' c,
    (forall s, P s -> P' s) -> (forall s s', R s s' -> R' s s') ->
    (forall s s', G' s s' -> G s s') -> (forall s, Q' s -> Q s) ->
    rgprov R' G' P' c Q' -> rgprov R G P c Q.
Proof. intros. via. eapply rg_cons_sound; eassumption. Qed.

End JonesRules.

Theorem rg_embed : forall R G P c Q, rg R G P c Q -> rgprov R G P c Q.
Proof. intros. apply rgprov_iff, rg_sound. assumption. Qed.

(** ** The counterexample, proved *)

Local Open Scope string_scope.
Local Notation X := "x".

Lemma smulti_snoc : forall k k1 k2,
    smulti pstep k k1 -> pstep k1 k2 -> smulti pstep k k2.
Proof.
  intros k k1 k2 H. induction H; intros Hs.
  - eapply SM_Step; [exact Hs | apply SM_Refl].
  - eapply SM_Step; [eassumption | apply IHsmulti, Hs].
Qed.

Lemma reach_closed : forall k0 k, reach (fun _ _ => False) k0 k ->
    smulti pstep k0 k.
Proof.
  intros k0 k H. induction H.
  - apply SM_Refl.
  - eapply smulti_snoc; eassumption.
  - contradiction.
Qed.

Theorem inc2_rgprov :
  rgprov (fun _ _ => False) (fun _ _ => True)
    (fun s => s X = 0) inc2 (fun s => s X = 2).
Proof.
  apply rgprov_iff. intros s0 [d s] H0 Hr. split; [auto |].
  simpl. intros ->. apply reach_closed in Hr.
  pose proof inc2_correct as V. rewrite cvalid_cvr in V. simpl in V.
  exact (V s0 s H0 Hr).
Qed.

(** The same triple, by a rule of the generated logic: the configuration
    invariant [hsprov_inv] of [Core.StepCore]. The invariant counts the
    increments still to come, which is exactly what a thread-local
    assertion cannot see. *)

Definition incr (c : pcom) : Prop := c = incx \/ c = PSkip.

Definition inc_inv (k : rcfg) : Prop :=
  match k with
  | (d, Some s) =>
      (exists a b, d = PPar a b /\ incr a /\ incr b /\
                   s X + cnt a + cnt b = 2) \/
      (d = PSkip /\ s X = 2)
  | (_, None) => False
  end.

Lemma incx_step : forall a s a' s', incr a -> pstep (a, s) (a', s') ->
    a = incx /\ a' = PSkip /\ s' = update s X (s X + 1).
Proof.
  intros a s a' s' [-> | ->] H; inversion H; subst; auto.
Qed.

Theorem inc2_by_invariant :
  rgprov (fun _ _ => False) (fun _ _ => True)
    (fun s => s X = 0) inc2 (fun s => s X = 2).
Proof.
  apply (hsprov_inv _ _ inc_inv).
  - intros [s|] [s0 [E Hs]]; [| discriminate]. injection E; intros; subst.
    left. exists incx, incx. repeat split; try (left; reflexivity).
    simpl. rewrite Hs. reflexivity.
  - intros [d [s|]] k' Hi Hst; [| contradiction]. inversion Hst; subst;
      [| match goal with H : ~ True |- _ => contradiction (H I) end
       | contradiction].
    match goal with H : pstep _ _ |- _ => rename H into Hp end.
    destruct Hi as [[a [b [-> [Ha [Hb E]]]]] | [-> _]];
      [| inversion Hp].
    inversion Hp; subst.
    + match goal with H : pstep (a, _) _ |- _ =>
        destruct (incx_step _ _ _ _ Ha H) as [-> [-> ->]] end.
      left. exists PSkip, b. repeat split; [right; reflexivity | exact Hb |].
      rewrite update_eq. simpl in *. lia.
    + match goal with H : pstep (b, _) _ |- _ =>
        destruct (incx_step _ _ _ _ Hb H) as [-> [-> ->]] end.
      left. exists a, PSkip. repeat split; [exact Ha | right; reflexivity |].
      rewrite update_eq. simpl in *. lia.
    + right. split; [reflexivity |]. simpl in E. lia.
  - intros [s|] Hi; [| contradiction]. simpl.
    destruct Hi as [[a [b [E _]]] | [_ H]]; [discriminate | exact H].
Qed.

Theorem rg_generated_stronger :
  exists P c Q,
    rgprov (fun _ _ => False) (fun _ _ => True) P c Q /\
    forall G, ~ rg (fun _ _ => False) G P c Q.
Proof.
  exists (fun s => s X = 0), inc2, (fun s => s X = 2).
  split; [exact inc2_rgprov | intros G; apply inc2_not_rg].
Qed.
