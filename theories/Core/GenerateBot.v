(** * Generating bottom-face rules for the core language

    The generator of [Core.Generate], for the language with nontermination
    [KLangB] (assertions over [option Σ], [None = ⊥]). For every operator:

    - [fwdB_rule]: exact strongest postconditions with ⊥, sound at both
      forward nodes (HL⊥, IL⊥);
    - [bwdB_rule]: exact weakest liberal preconditions with ⊥, sound for
      HL⊥ and the wlp-dual.

    The star rules are pointwise (one premise per state), for the reason in
    README finding 9. Under unbounded nondeterminism the set-level iterates
    do not decide whether an infinite chain exists, so chains are followed
    state by state: [reachK] (inductive) for finite iteration, [infK]
    (coinductive) for infinite iteration. HL⊥ soundness of the forward star
    rule and wlp-dual soundness of the backward one are classical. *)

From Stdlib Require Import Classical.
From LogicTransformers.Framework Require Import Language ProgramLogic Cube.
From LogicTransformers.Core Require Import Kernel KernelBot Generate.

(** ** Chains of star iterations, from per-state body posts [F] *)

Section Chains.

Context {Σ : Type} (F : Σ -> option Σ -> Prop).

Inductive reachK : Σ -> Σ -> Prop :=
  | rK_refl : forall s, reachK s s
  | rK_step : forall s s1 s', F s (Some s1) -> reachK s1 s' -> reachK s s'.

CoInductive infK : Σ -> Prop :=
  | infK_step : forall s s', F s (Some s') -> infK s' -> infK s.

End Chains.

Section GenerateBot.

Context {Σ Act : Type} (act_sem : Act -> Σ -> Σ -> Prop).

Notation LB := (KLangB act_sem).
Notation kbt := (@mkTriple LB).
Notation kev := (kev act_sem).
Notation kdiv := (kdiv act_sem).
Notation semKB := (semKB act_sem).
Notation spLB := (@img LB).
Notation wlpLB := (@wlp LB).

(** ** Star lemmas *)

Lemma star_over_term : forall c (F : Σ -> option Σ -> Prop),
    (forall s s', kev c s s' -> F s (Some s')) ->
    forall s s', kev (KStar c) s s' -> reachK F s s'.
Proof.
  intros c F Hst s s' H. remember (KStar c) as k eqn:Ek.
  induction H; inversion Ek; subst; [constructor |].
  eapply rK_step; [apply Hst; eassumption | apply IHkev2; reflexivity].
Qed.

Lemma star_over_div : forall c (F : Σ -> option Σ -> Prop),
    (forall s s', kev c s s' -> F s (Some s')) ->
    forall s, kdiv (KStar c) s ->
    (exists s1, reachK F s s1 /\ kdiv c s1) \/ infK F s.
Proof.
  intros c F Hst s Hd.
  destruct (classic (exists s1, reachK F s s1 /\ kdiv c s1)) as [Hex | Hn];
    [left; exact Hex | right].
  revert s Hd Hn. cofix CH. intros s Hd Hn.
  inversion Hd; subst.
  - exfalso. apply Hn. exists s. split; [constructor | assumption].
  - apply (infK_step F s s1); [apply Hst; assumption |].
    apply CH; [assumption |].
    intros [s2 [Hr Hd2]]. apply Hn. exists s2. split; [| assumption].
    apply rK_step with s1; [apply Hst; assumption | exact Hr].
Qed.

Lemma star_under_reach : forall c (F : Σ -> option Σ -> Prop),
    (forall s s', F s (Some s') -> kev c s s') ->
    forall s s', reachK F s s' ->
    kev (KStar c) s s' /\ (kdiv (KStar c) s' -> kdiv (KStar c) s).
Proof.
  intros c F Hreal s s' Hr.
  induction Hr as [s | s s1 s' HF Hr [IH1 IH2]].
  - split; [apply KE_StarRefl | auto].
  - pose proof (Hreal _ _ HF) as Hc. split.
    + eapply KE_StarStep; eassumption.
    + intros H. eapply KD_StarIter; [exact Hc | apply IH2, H].
Qed.

Lemma star_under_inf : forall c (F : Σ -> option Σ -> Prop),
    (forall s s', F s (Some s') -> kev c s s') ->
    forall s, infK F s -> kdiv (KStar c) s.
Proof.
  intros c F Hreal. cofix CH. intros s Hi.
  destruct Hi as [s s' HF Hi].
  eapply KD_StarIter; [apply Hreal, HF | apply CH; exact Hi].
Qed.

(** ** The rules *)

Variable rel : Act -> Σ -> Σ -> Prop.

Definition spB_rel (a : Act) (P : assertion LB) : assertion LB :=
  fun o => match o with
           | Some s' => exists s, P (Some s) /\ rel a s s'
           | None => P None
           end.

Definition wlpB_rel (a : Act) (Q : assertion LB) : assertion LB :=
  fun o => match o with
           | Some s => forall s', rel a s s' -> Q (Some s')
           | None => Q None
           end.

Definition assumeB_post (B : Σ -> Prop) (P : assertion LB) : assertion LB :=
  fun o => match o with Some s => P (Some s) /\ B s | None => P None end.

Definition assumeB_pre (B : Σ -> Prop) (Q : assertion LB) : assertion LB :=
  fun o => match o with Some s => B s -> Q (Some s) | None => Q None end.

Definition single (s : Σ) : assertion LB := fun o => o = Some s.
Definition neqS (s' : Σ) : assertion LB := fun o => o <> Some s'.
Definition neqNone : assertion LB := fun o => o <> None.

Definition starB_post (F : Σ -> assertion LB) (P : assertion LB)
  : assertion LB :=
  fun o => match o with
           | Some s' => exists s, P (Some s) /\ reachK F s s'
           | None =>
               P None \/
               (exists s s1, P (Some s) /\ reachK F s s1 /\ F s1 None) \/
               (exists s, P (Some s) /\ infK F s)
           end.

Definition stepsW (W : Σ -> assertion LB) (Wd : assertion LB)
  : Σ -> assertion LB :=
  fun s o => match o with
             | Some s' => ~ W s' (Some s)
             | None => ~ Wd (Some s)
             end.

Definition starB_pre (W : Σ -> assertion LB) (Wd : assertion LB)
    (Q : assertion LB) : assertion LB :=
  fun o => match o with
           | None => Q None
           | Some s =>
               (forall s', reachK (stepsW W Wd) s s' -> Q (Some s')) /\
               ((exists s1, reachK (stepsW W Wd) s s1 /\ ~ Wd (Some s1)) \/
                infK (stepsW W Wd) s -> Q None)
           end.

Definition bpr0 : triple LB -> Prop := fun _ => False.
Definition bpr2 (x y : triple LB) : triple LB -> Prop :=
  fun t => t = x \/ t = y.

Inductive fwdB_rule : gname -> ruleset LB :=
  | FB_Skip : forall P, fwdB_rule GSkip bpr0 (kbt P KSkip P)
  | FB_Act : forall P a,
      fwdB_rule GAct bpr0 (kbt P (KAct a) (spB_rel a P))
  | FB_Assume : forall P B,
      fwdB_rule GAssume bpr0 (kbt P (KAssume B) (assumeB_post B P))
  | FB_Seq : forall P Q R c1 c2,
      fwdB_rule GSeq (bpr2 (kbt P c1 Q) (kbt Q c2 R)) (kbt P (KSeq c1 c2) R)
  | FB_Choice : forall P Q1 Q2 c1 c2,
      fwdB_rule GChoice (bpr2 (kbt P c1 Q1) (kbt P c2 Q2))
        (kbt P (KChoice c1 c2) (fun o => Q1 o \/ Q2 o))
  | FB_Star : forall P c (F : Σ -> assertion LB),
      fwdB_rule GStar (fun t => exists s, t = kbt (single s) c (F s))
        (kbt P (KStar c) (starB_post F P)).

Inductive bwdB_rule : gname -> ruleset LB :=
  | BB_Skip : forall Q, bwdB_rule GSkip bpr0 (kbt Q KSkip Q)
  | BB_Act : forall Q a,
      bwdB_rule GAct bpr0 (kbt (wlpB_rel a Q) (KAct a) Q)
  | BB_Assume : forall Q B,
      bwdB_rule GAssume bpr0 (kbt (assumeB_pre B Q) (KAssume B) Q)
  | BB_Seq : forall P Q R c1 c2,
      bwdB_rule GSeq (bpr2 (kbt P c1 Q) (kbt Q c2 R)) (kbt P (KSeq c1 c2) R)
  | BB_Choice : forall P1 P2 Q c1 c2,
      bwdB_rule GChoice (bpr2 (kbt P1 c1 Q) (kbt P2 c2 Q))
        (kbt (fun o => P1 o /\ P2 o) (KChoice c1 c2) Q)
  | BB_Star : forall Q c (W : Σ -> assertion LB) Wd,
      bwdB_rule GStar
        (fun t => (exists s', t = kbt (W s') c (neqS s')) \/
                  t = kbt Wd c neqNone)
        (kbt (starB_pre W Wd Q) (KStar c) Q).

Hypothesis Hrel : forall a s s', rel a s s' <-> act_sem a s s'.

(** ** Forward rules: sound over and under *)

Theorem fwdB_over_sound : forall r ps c,
    fwdB_rule r ps c ->
    (forall t, ps t -> cube_valid Forward Over t) ->
    cube_valid Forward Over c.
Proof.
  intros r ps c HR H.
  assert (H' : forall t, ps t ->
            forall o o', pre t o -> semKB (cmd t) o o' -> post t o')
    by (intros t Ht; apply (hl_valid_iff t), H, Ht).
  clear H. apply hl_valid_iff.
  destruct HR; cbn; intros o o' HP Hc.
  - apply semKB_skip in Hc. subst. exact HP.
  - apply semKB_act in Hc.
    destruct o as [s|], o' as [s'|]; try contradiction; [| exact HP].
    exists s. split; [exact HP | apply Hrel, Hc].
  - apply semKB_assume in Hc.
    destruct o as [s|], o' as [s'|]; try contradiction; [| exact HP].
    destruct Hc as [-> HB]. split; assumption.
  - apply semKB_seq in Hc as [o1 [H1 H2]].
    apply (H' _ (or_intror eq_refl) o1); [| exact H2].
    apply (H' _ (or_introl eq_refl) o); assumption.
  - apply semKB_choice in Hc as [Hc | Hc].
    + left. apply (H' _ (or_introl eq_refl) o); assumption.
    + right. apply (H' _ (or_intror eq_refl) o); assumption.
  - assert (Hst : forall s s', kev c s s' -> F s (Some s'))
      by (intros s s' Hc1;
          exact (H' _ (ex_intro _ s eq_refl) (Some s) (Some s') eq_refl Hc1)).
    assert (Hdv : forall s, kdiv c s -> F s None)
      by (intros s Hd;
          exact (H' _ (ex_intro _ s eq_refl) (Some s) None eq_refl Hd)).
    destruct o as [s|]; [destruct o' as [s'|] |].
    + exists s. split; [exact HP | exact (star_over_term c F Hst s s' Hc)].
    + destruct (star_over_div c F Hst s Hc) as [[s1 [Hr Hd]] | Hinf].
      * right. left. exists s, s1. repeat split; auto.
      * right. right. exists s. auto.
    + apply semKB_none in Hc. subst. left. exact HP.
Qed.

Theorem fwdB_under_sound : forall r ps c,
    fwdB_rule r ps c ->
    (forall t, ps t -> cube_valid Forward Under t) ->
    cube_valid Forward Under c.
Proof.
  intros r ps c HR H.
  assert (H' : forall t, ps t ->
            forall o', post t o' -> exists o, pre t o /\ semKB (cmd t) o o')
    by (intros t Ht; apply (il_valid_iff t), H, Ht).
  clear H. apply il_valid_iff.
  destruct HR; cbn; intros o' Ho'.
  - exists o'. split; [exact Ho' | apply semKB_skip; reflexivity].
  - destruct o' as [s'|].
    + destruct Ho' as [s [HP Hr]]. exists (Some s).
      split; [exact HP | apply semKB_act, Hrel, Hr].
    + exists None. split; [exact Ho' | exact I].
  - destruct o' as [s'|].
    + destruct Ho' as [HP HB]. exists (Some s').
      split; [exact HP | apply semKB_assume; auto].
    + exists None. split; [exact Ho' | exact I].
  - destruct (H' _ (or_intror eq_refl) o' Ho') as [o1 [HQ H2]].
    destruct (H' _ (or_introl eq_refl) o1 HQ) as [o [HP H1]].
    exists o. split; [exact HP | apply semKB_seq; exists o1; auto].
  - destruct Ho' as [Hq | Hq].
    + destruct (H' _ (or_introl eq_refl) o' Hq) as [o [HP Hc]].
      exists o. split; [exact HP | apply semKB_choice; auto].
    + destruct (H' _ (or_intror eq_refl) o' Hq) as [o [HP Hc]].
      exists o. split; [exact HP | apply semKB_choice; auto].
  - assert (Hreal : forall s s', F s (Some s') -> kev c s s').
    { intros s s' HF.
      destruct (H' _ (ex_intro _ s eq_refl) (Some s') HF) as [o [-> Hc]].
      exact Hc. }
    assert (Hreal_div : forall s, F s None -> kdiv c s).
    { intros s HF.
      destruct (H' _ (ex_intro _ s eq_refl) None HF) as [o [-> Hc]].
      exact Hc. }
    destruct o' as [s'|].
    + destruct Ho' as [s [HP Hr]]. exists (Some s). split; [exact HP |].
      exact (proj1 (star_under_reach c F Hreal s s' Hr)).
    + destruct Ho' as [HP | [[s [s1 [HP [Hr HF]]]] | [s [HP Hinf]]]].
      * exists None. split; [exact HP | exact I].
      * exists (Some s). split; [exact HP |]. simpl.
        apply (proj2 (star_under_reach c F Hreal s s1 Hr)).
        apply KD_StarBody, Hreal_div, HF.
      * exists (Some s). split; [exact HP |].
        exact (star_under_inf c F Hreal s Hinf).
Qed.

(** ** Backward rules: sound for HL⊥ and the wlp-dual *)

Theorem bwdB_over_sound : forall r ps c,
    bwdB_rule r ps c ->
    (forall t, ps t -> cube_valid Forward Over t) ->
    cube_valid Forward Over c.
Proof.
  intros r ps c HR H.
  assert (H' : forall t, ps t ->
            forall o o', pre t o -> semKB (cmd t) o o' -> post t o')
    by (intros t Ht; apply (hl_valid_iff t), H, Ht).
  clear H. apply hl_valid_iff.
  destruct HR; cbn; intros o o' HP Hc.
  - apply semKB_skip in Hc. subst. exact HP.
  - apply semKB_act in Hc.
    destruct o as [s|], o' as [s'|]; try contradiction; [| exact HP].
    apply HP, Hrel, Hc.
  - apply semKB_assume in Hc.
    destruct o as [s|], o' as [s'|]; try contradiction; [| exact HP].
    destruct Hc as [-> HB]. apply HP, HB.
  - apply semKB_seq in Hc as [o1 [H1 H2]].
    apply (H' _ (or_intror eq_refl) o1); [| exact H2].
    apply (H' _ (or_introl eq_refl) o); assumption.
  - apply semKB_choice in Hc as [Hc | Hc].
    + apply (H' _ (or_introl eq_refl) o); [apply HP | exact Hc].
    + apply (H' _ (or_intror eq_refl) o); [apply HP | exact Hc].
  - assert (Hst : forall s s', kev c s s' -> stepsW W Wd s (Some s')).
    { intros s s' Hc1 HW.
      exact (H' _ (or_introl (ex_intro _ s' eq_refl)) (Some s) (Some s')
                HW Hc1 eq_refl). }
    assert (Hdv : forall s, kdiv c s -> ~ Wd (Some s)).
    { intros s Hd HW.
      exact (H' _ (or_intror eq_refl) (Some s) None HW Hd eq_refl). }
    destruct o as [s|]; [destruct o' as [s'|] |].
    + apply (proj1 HP). exact (star_over_term c _ Hst s s' Hc).
    + apply (proj2 HP).
      destruct (star_over_div c _ Hst s Hc) as [[s1 [Hr Hd]] | Hinf].
      * left. exists s1. split; [exact Hr | apply Hdv, Hd].
      * right. exact Hinf.
    + apply semKB_none in Hc. subst. exact HP.
Qed.

Theorem bwdB_dual_sound : forall r ps c,
    bwdB_rule r ps c ->
    (forall t, ps t -> dual_valid t) ->
    dual_valid c.
Proof.
  intros r ps c HR H.
  assert (H' : forall t, ps t ->
            forall o, (forall o', semKB (cmd t) o o' -> post t o') -> pre t o)
    by (intros t Ht; apply H, Ht).
  clear H. destruct HR; unfold dual_valid, aimpl, wlp; cbn; intros o Hw.
  - apply Hw, semKB_skip. reflexivity.
  - destruct o as [s|].
    + intros s' Hr. apply Hw, semKB_act, Hrel, Hr.
    + apply Hw. exact I.
  - destruct o as [s|].
    + intros HB. apply Hw, semKB_assume. auto.
    + apply Hw. exact I.
  - apply (H' _ (or_introl eq_refl) o). intros o1 H1.
    apply (H' _ (or_intror eq_refl) o1). intros o2 H2.
    apply Hw, semKB_seq. exists o1. auto.
  - split; [apply (H' _ (or_introl eq_refl) o)
           | apply (H' _ (or_intror eq_refl) o)];
      intros o' Hc; apply Hw, semKB_choice; auto.
  - assert (Hreal : forall s s', stepsW W Wd s (Some s') -> kev c s s').
    { intros s s' HnW. apply NNPP. intros Hnc. apply HnW.
      apply (H' _ (or_introl (ex_intro _ s' eq_refl)) (Some s)).
      intros [s''|] Hc Heq; [| discriminate].
      inversion Heq; subst. contradiction. }
    assert (Hreal_div : forall s, ~ Wd (Some s) -> kdiv c s).
    { intros s HnWd. apply NNPP. intros Hnd. apply HnWd.
      apply (H' _ (or_intror eq_refl) (Some s)).
      intros [s''|] Hc Heq; [discriminate | contradiction]. }
    destruct o as [s|]; [split | apply Hw; exact I].
    + intros s' Hr. apply Hw. simpl.
      exact (proj1 (star_under_reach c _ Hreal s s' Hr)).
    + intros [[s1 [Hr HnWd]] | Hinf]; apply Hw; simpl.
      * apply (proj2 (star_under_reach c _ Hreal s s1 Hr)).
        apply KD_StarBody, Hreal_div, HnWd.
      * exact (star_under_inf c _ Hreal s Hinf).
Qed.

(** ** Exactness *)

Definition fwdB_base : ruleset LB := fun ps c => exists r, fwdB_rule r ps c.
Definition bwdB_base : ruleset LB := fun ps c => exists r, bwdB_rule r ps c.

Lemma fwdB_step : forall r ps c,
    fwdB_rule r ps c -> (forall t, ps t -> fexact t) -> fexact c.
Proof.
  intros r ps c HR H. apply fexact_iff. split.
  - apply (fwdB_over_sound r ps c HR). intros t Ht. apply fexact_iff, H, Ht.
  - apply (fwdB_under_sound r ps c HR). intros t Ht. apply fexact_iff, H, Ht.
Qed.

Lemma bwdB_step : forall r ps c,
    bwdB_rule r ps c -> (forall t, ps t -> pexact t) -> pexact c.
Proof.
  intros r ps c HR H. apply pexact_iff. split.
  - apply (bwdB_over_sound r ps c HR). intros t Ht. apply pexact_iff, H, Ht.
  - apply (bwdB_dual_sound r ps c HR). intros t Ht. apply pexact_iff, H, Ht.
Qed.

Ltac gbcase step HR pd pe :=
  eapply D_Equiv;
  [ eapply D_Rule; [eexists; exact HR | pd]
  | first [apply fexact_equiv | apply pexact_equiv];
    eapply (step _ _ _ HR); pe ].

Theorem fwdB_exact : forall c P, derivable fwdB_base (kbt P c (spLB c P)).
Proof.
  induction c; intros P.
  - gbcase fwdB_step (FB_Skip P) ltac:(intros t []) ltac:(intros t []).
  - gbcase fwdB_step (FB_Act P a) ltac:(intros t []) ltac:(intros t []).
  - gbcase fwdB_step (FB_Assume P B) ltac:(intros t []) ltac:(intros t []).
  - gbcase fwdB_step (FB_Seq P (spLB c1 P) (spLB c2 (spLB c1 P)) c1 c2)
      ltac:(intros t [-> | ->]; auto)
      ltac:(intros t [-> | ->]; apply fexact_img).
  - gbcase fwdB_step (FB_Choice P (spLB c1 P) (spLB c2 P) c1 c2)
      ltac:(intros t [-> | ->]; auto)
      ltac:(intros t [-> | ->]; apply fexact_img).
  - gbcase fwdB_step (FB_Star P c (fun s => spLB c (single s)))
      ltac:(intros t [s ->]; apply IHc)
      ltac:(intros t [s ->]; apply fexact_img).
Qed.

Theorem bwdB_exact : forall c Q, derivable bwdB_base (kbt (wlpLB c Q) c Q).
Proof.
  induction c; intros Q.
  - gbcase bwdB_step (BB_Skip Q) ltac:(intros t []) ltac:(intros t []).
  - gbcase bwdB_step (BB_Act Q a) ltac:(intros t []) ltac:(intros t []).
  - gbcase bwdB_step (BB_Assume Q B) ltac:(intros t []) ltac:(intros t []).
  - gbcase bwdB_step (BB_Seq (wlpLB c1 (wlpLB c2 Q)) (wlpLB c2 Q) Q c1 c2)
      ltac:(intros t [-> | ->]; auto)
      ltac:(intros t [-> | ->]; apply pexact_wlp).
  - gbcase bwdB_step (BB_Choice (wlpLB c1 Q) (wlpLB c2 Q) Q c1 c2)
      ltac:(intros t [-> | ->]; auto)
      ltac:(intros t [-> | ->]; apply pexact_wlp).
  - gbcase bwdB_step
      (BB_Star Q c (fun s' => wlpLB c (neqS s')) (wlpLB c neqNone))
      ltac:(intros t [[s' ->] | ->]; apply IHc)
      ltac:(intros t [[s' ->] | ->]; apply pexact_wlp).
Qed.

End GenerateBot.

Arguments fwdB_rule {Σ Act act_sem} rel.
Arguments bwdB_rule {Σ Act act_sem} rel.
Arguments fwdB_base {Σ Act act_sem} rel.
Arguments bwdB_base {Σ Act act_sem} rel.
