(** * Forward rules for the bottom face

    Rules over [ImpBot] (assertions over [option state], with [None] for
    nontermination ⊥), with no consequence rule. Every rule is sound for
    both HL⊥ ([cube_valid Forward Over]) and IL⊥
    ([cube_valid Forward Under]), and together they derive exact strongest
    postconditions ([bexact]). By [fexact_iff], exactness of each rule
    follows from its two-sided soundness.

    The loop rule [BR_While] is pointwise: one premise per start state
    [s], [{s ∧ b} c {F s}]. A loop diverges when some reachable iteration
    diverges in its body, or along an infinite chain of iterations. With
    unbounded nondeterminism ([havoc]), the set-level iterates of the body
    do not determine whether an infinite chain exists (every depth can be
    reachable while every run terminates). So the rule follows chains
    state by state: [reachF] (inductive) for termination and [infF]
    (coinductive) for infinite iteration. This mirrors Cousot's remark that
    termination methods based on bounded iterates are "incomplete for
    unbounded nondeterminism".

    HL⊥ soundness of the loop rule needs classical logic: a divergence is
    either a reachable body divergence or an infinite chain. *)

From Stdlib Require Import Classical.
From LogicTransformers.Imp Require Import Syntax BigStep Diverge LangBot.
From LogicTransformers.Logics Require Import Hoare.
From LogicTransformers.Framework Require Import Language ProgramLogic Cube.

Notation hb := (@mkTriple ImpBot).
Notation spB := (@img ImpBot).

Definition bwith (P : assertion ImpBot) (b : bexp) : assertion ImpBot :=
  fun o => match o with
           | Some s => P (Some s) /\ bassn b s
           | None => P None
           end.

Definition bwithout (P : assertion ImpBot) (b : bexp) : assertion ImpBot :=
  fun o => match o with
           | Some s => P (Some s) /\ ~ bassn b s
           | None => P None
           end.

Definition asgnB_post (x : var) (a : aexp) (P : assertion ImpBot)
  : assertion ImpBot :=
  fun o => match o with
           | Some s' => exists s, P (Some s) /\ s' = update s x (aeval s a)
           | None => P None
           end.

Definition havocB_post (x : var) (P : assertion ImpBot) : assertion ImpBot :=
  fun o => match o with
           | Some s' => exists s n, P (Some s) /\ s' = update s x n
           | None => P None
           end.

Definition single_b (s : state) (b : bexp) : assertion ImpBot :=
  fun o => o = Some s /\ bassn b s.

Definition pr0 : triple ImpBot -> Prop := fun _ => False.
Definition pr2 (a c : triple ImpBot) : triple ImpBot -> Prop :=
  fun t => t = a \/ t = c.

(** ** Chains of loop iterations, as described by the body posts [F] *)

Section Chains.

Variables (b : bexp) (F : state -> assertion ImpBot).

Definition stepF (s s' : state) : Prop := bassn b s /\ F s (Some s').

Inductive reachF : state -> state -> Prop :=
  | rF_refl : forall s, reachF s s
  | rF_step : forall s s1 s', stepF s s1 -> reachF s1 s' -> reachF s s'.

CoInductive infF : state -> Prop :=
  | infF_step : forall s s', stepF s s' -> infF s' -> infF s.

Definition loopB_post (P : assertion ImpBot) : assertion ImpBot :=
  fun o => match o with
           | Some s' => exists s, P (Some s) /\ reachF s s' /\ ~ bassn b s'
           | None =>
               P None \/
               (exists s s1, P (Some s) /\ reachF s s1 /\ bassn b s1 /\
                             F s1 None) \/
               (exists s, P (Some s) /\ infF s)
           end.

End Chains.

(** ** The rules *)

Inductive brule_name := BSkip | BAsgn | BSeq | BIf | BChoice | BHavoc | BWhile.

Inductive brule : brule_name -> ruleset ImpBot :=
  | BR_Skip : forall P,
      brule BSkip pr0 (hb P CSkip P)
  | BR_Asgn : forall P x a,
      brule BAsgn pr0 (hb P (CAsgn x a) (asgnB_post x a P))
  | BR_Seq : forall P Q R c1 c2,
      brule BSeq (pr2 (hb P c1 Q) (hb Q c2 R)) (hb P (CSeq c1 c2) R)
  | BR_If : forall P Q1 Q2 b c1 c2,
      brule BIf (pr2 (hb (bwith P b) c1 Q1) (hb (bwithout P b) c2 Q2))
        (hb P (CIf b c1 c2) (fun o => Q1 o \/ Q2 o))
  | BR_Choice : forall P Q1 Q2 c1 c2,
      brule BChoice (pr2 (hb P c1 Q1) (hb P c2 Q2))
        (hb P (CChoice c1 c2) (fun o => Q1 o \/ Q2 o))
  | BR_Havoc : forall P x,
      brule BHavoc pr0 (hb P (CHavoc x) (havocB_post x P))
  | BR_While : forall P b c (F : state -> assertion ImpBot),
      brule BWhile (fun t => exists s, t = hb (single_b s b) c (F s))
        (hb P (CWhile b c) (loopB_post b F P)).

(** ** Loop lemmas *)

Lemma loop_over_term : forall b c F,
    (forall s s', bassn b s -> ceval c s s' -> F s (Some s')) ->
    forall s s', ceval (CWhile b c) s s' ->
    reachF b F s s' /\ ~ bassn b s'.
Proof.
  intros b c F Hst s s' Hc. remember (CWhile b c) as w eqn:Ew.
  induction Hc; inversion Ew; subst.
  - split; [constructor | apply bassn_false'; assumption].
  - destruct (IHHc2 eq_refl) as [Hr Hnb]. split; [| exact Hnb].
    eapply rF_step; [split; [eassumption | apply Hst; eassumption] | exact Hr].
Qed.

Lemma loop_over_div : forall b c F,
    (forall s s', bassn b s -> ceval c s s' -> F s (Some s')) ->
    forall s, diverges (CWhile b c) s ->
    (exists s1, reachF b F s s1 /\ bassn b s1 /\ diverges c s1) \/
    infF b F s.
Proof.
  intros b c F Hst s Hd.
  destruct (classic (exists s1, reachF b F s s1 /\ bassn b s1 /\
                                diverges c s1)) as [Hex | Hn];
    [left; exact Hex | right].
  revert s Hd Hn. cofix CH. intros s Hd Hn.
  inversion Hd; subst.
  - exfalso. apply Hn. exists s. split; [constructor | auto].
  - apply (infF_step b F s st').
    + split; [assumption | apply Hst; assumption].
    + apply CH; [assumption |].
      intros [s1 [Hr [Hb Hd1]]]. apply Hn. exists s1. split; [| auto].
      apply rF_step with st';
        [split; [assumption | apply Hst; assumption] | exact Hr].
Qed.

Lemma loop_under_reach : forall b c F,
    (forall s s', bassn b s -> F s (Some s') -> ceval c s s') ->
    forall s s', reachF b F s s' ->
    (forall s'', ceval (CWhile b c) s' s'' -> ceval (CWhile b c) s s'') /\
    (diverges (CWhile b c) s' -> diverges (CWhile b c) s).
Proof.
  intros b c F Hreal s s' Hr.
  induction Hr as [s | s s1 s' [Hb HF] Hr [IH1 IH2]].
  - split; auto.
  - pose proof (Hreal _ _ Hb HF) as Hc. split; [intros s'' H | intros H].
    + eapply E_WhileTrue; [exact Hb | exact Hc | apply IH1, H].
    + eapply Dv_WhileIter; [exact Hb | exact Hc | apply IH2, H].
Qed.

Lemma loop_under_inf : forall b c F,
    (forall s s', bassn b s -> F s (Some s') -> ceval c s s') ->
    forall s, infF b F s -> diverges (CWhile b c) s.
Proof.
  intros b c F Hreal. cofix CH. intros s Hi.
  destruct Hi as [s s' [Hb HF] Hi].
  pose proof (Hreal _ _ Hb HF) as Hc.
  eapply Dv_WhileIter; [exact Hb | exact Hc | apply CH; exact Hi].
Qed.

(** ** Soundness at the over-approximate node (HL⊥) *)

Lemma over_premB : forall (ps : triple ImpBot -> Prop),
    (forall t, ps t -> cube_valid Forward Over t) ->
    forall t, ps t ->
    forall o o', pre t o -> semB (cmd t) o o' -> post t o'.
Proof. intros ps H t Ht. apply (hl_valid_iff t), H, Ht. Qed.

Theorem brule_over_sound : forall r ps c,
    brule r ps c ->
    (forall t, ps t -> cube_valid Forward Over t) ->
    cube_valid Forward Over c.
Proof.
  intros r ps c HR H. pose proof (over_premB _ H) as H'. clear H.
  apply hl_valid_iff.
  destruct HR; cbn; intros o o' HP Hc.
  - (* Skip *) apply semB_skip in Hc. subst. exact HP.
  - (* Asgn *)
    apply semB_asgn in Hc. destruct o as [s|]; subst; [| exact HP].
    exists s. auto.
  - (* Seq *)
    apply semB_seq in Hc as [o1 [H1 H2]].
    apply (H' _ (or_intror eq_refl) o1); [| exact H2].
    apply (H' _ (or_introl eq_refl) o); assumption.
  - (* If *)
    destruct o as [s|].
    + apply semB_if in Hc as [[Hb Hc] | [Hb Hc]].
      * left. apply (H' _ (or_introl eq_refl) (Some s)); [| exact Hc].
        split; assumption.
      * right. apply (H' _ (or_intror eq_refl) (Some s)); [| exact Hc].
        split; [assumption | apply bassn_false'; assumption].
    + apply semB_none in Hc. subst. left.
      apply (H' _ (or_introl eq_refl) None); [exact HP | exact I].
  - (* Choice *)
    apply semB_choice in Hc as [Hc | Hc].
    + left. apply (H' _ (or_introl eq_refl) o); assumption.
    + right. apply (H' _ (or_intror eq_refl) o); assumption.
  - (* Havoc *)
    apply semB_havoc in Hc. destruct o as [s|].
    + destruct Hc as [n ->]. exists s, n. auto.
    + subst. exact HP.
  - (* While *)
    assert (Hst : forall s s', bassn b s -> ceval c s s' -> F s (Some s'))
      by (intros s s' Hb Hc1;
          exact (H' _ (ex_intro _ s eq_refl) (Some s) (Some s')
                    (conj eq_refl Hb) Hc1)).
    assert (Hdv : forall s, bassn b s -> diverges c s -> F s None)
      by (intros s Hb Hd;
          exact (H' _ (ex_intro _ s eq_refl) (Some s) None
                    (conj eq_refl Hb) Hd)).
    destruct o as [s|]; [destruct o' as [s'|] |].
    + destruct (loop_over_term b c F Hst s s' Hc) as [Hr Hnb].
      exists s. auto.
    + destruct (loop_over_div b c F Hst s Hc)
        as [[s1 [Hr [Hb Hd]]] | Hinf].
      * right. left. exists s, s1. repeat split; auto.
      * right. right. exists s. auto.
    + apply semB_none in Hc. subst. left. exact HP.
Qed.

(** ** Soundness at the under-approximate node (IL⊥) *)

Lemma under_premB : forall (ps : triple ImpBot -> Prop),
    (forall t, ps t -> cube_valid Forward Under t) ->
    forall t, ps t ->
    forall o', post t o' -> exists o, pre t o /\ semB (cmd t) o o'.
Proof. intros ps H t Ht. apply (il_valid_iff t), H, Ht. Qed.

Theorem brule_under_sound : forall r ps c,
    brule r ps c ->
    (forall t, ps t -> cube_valid Forward Under t) ->
    cube_valid Forward Under c.
Proof.
  intros r ps c HR H. pose proof (under_premB _ H) as H'. clear H.
  apply il_valid_iff.
  destruct HR; cbn; intros o' Ho'.
  - (* Skip *) exists o'. split; [exact Ho' | apply semB_skip; reflexivity].
  - (* Asgn *)
    destruct o' as [s'|].
    + destruct Ho' as [s [HP ->]]. exists (Some s).
      split; [exact HP | apply semB_asgn; reflexivity].
    + exists None. split; [exact Ho' | exact I].
  - (* Seq *)
    destruct (H' _ (or_intror eq_refl) o' Ho') as [o1 [HQ H2]].
    destruct (H' _ (or_introl eq_refl) o1 HQ) as [o [HP H1]].
    exists o. split; [exact HP | apply semB_seq; exists o1; auto].
  - (* If *)
    destruct Ho' as [Hq | Hq].
    + destruct (H' _ (or_introl eq_refl) o' Hq) as [[s|] [Hpre Hc]].
      * exists (Some s). split; [apply Hpre |].
        apply semB_if. left. split; [apply Hpre | exact Hc].
      * apply semB_none in Hc. subst. exists None.
        split; [exact Hpre | exact I].
    + destruct (H' _ (or_intror eq_refl) o' Hq) as [[s|] [Hpre Hc]].
      * exists (Some s). split; [apply Hpre |].
        apply semB_if. right. split; [apply bassn_false, Hpre | exact Hc].
      * apply semB_none in Hc. subst. exists None.
        split; [exact Hpre | exact I].
  - (* Choice *)
    destruct Ho' as [Hq | Hq].
    + destruct (H' _ (or_introl eq_refl) o' Hq) as [o [HP Hc]].
      exists o. split; [exact HP | apply semB_choice; auto].
    + destruct (H' _ (or_intror eq_refl) o' Hq) as [o [HP Hc]].
      exists o. split; [exact HP | apply semB_choice; auto].
  - (* Havoc *)
    destruct o' as [s'|].
    + destruct Ho' as [s [n [HP ->]]]. exists (Some s).
      split; [exact HP | apply semB_havoc; exists n; reflexivity].
    + exists None. split; [exact Ho' | exact I].
  - (* While *)
    assert (Hreal : forall s s', F s (Some s') -> bassn b s /\ ceval c s s').
    { intros s s' HF.
      destruct (H' _ (ex_intro _ s eq_refl) (Some s') HF)
        as [o [[-> Hb] Hc]].
      auto. }
    assert (Hreal_div : forall s, F s None -> bassn b s /\ diverges c s).
    { intros s HF.
      destruct (H' _ (ex_intro _ s eq_refl) None HF) as [o [[-> Hb] Hc]].
      auto. }
    assert (Hreal' : forall s s', bassn b s -> F s (Some s') -> ceval c s s')
      by (intros s s' _ HF; exact (proj2 (Hreal s s' HF))).
    destruct o' as [s'|].
    + destruct Ho' as [s [HP [Hr Hnb]]]. exists (Some s).
      split; [exact HP |]. simpl.
      apply (proj1 (loop_under_reach b c F Hreal' s s' Hr)).
      apply E_WhileFalse, bassn_false, Hnb.
    + destruct Ho' as [HP | [[s [s1 [HP [Hr [Hb HF]]]]] | [s [HP Hinf]]]].
      * exists None. split; [exact HP | exact I].
      * exists (Some s). split; [exact HP |]. simpl.
        apply (proj2 (loop_under_reach b c F Hreal' s s1 Hr)).
        destruct (Hreal_div s1 HF) as [_ Hd].
        apply Dv_WhileBody; assumption.
      * exists (Some s). split; [exact HP |]. simpl.
        exact (loop_under_inf b c F Hreal' s Hinf).
Qed.

(** ** Exactness *)

Definition bbase : ruleset ImpBot := fun ps c => exists r, brule r ps c.

Lemma brule_der : forall r ps c,
    brule r ps c ->
    (forall t, ps t -> derivable bbase t) -> derivable bbase c.
Proof. intros r ps c HR H. eapply D_Rule; [exists r; exact HR | exact H]. Qed.

Lemma brule_exact_step : forall r ps c,
    brule r ps c -> (forall t, ps t -> fexact t) -> fexact c.
Proof.
  intros r ps c HR H. apply fexact_iff. split.
  - apply (brule_over_sound r ps c HR).
    intros t Ht. apply fexact_iff, H, Ht.
  - apply (brule_under_sound r ps c HR).
    intros t Ht. apply fexact_iff, H, Ht.
Qed.

Ltac bcase HR prems_der prems_ex :=
  eapply D_Equiv;
  [ eapply (brule_der _ _ _ HR); prems_der
  | apply fexact_equiv; eapply (brule_exact_step _ _ _ HR); prems_ex ].

Theorem bexact : forall c P, derivable bbase (hb P c (spB c P)).
Proof.
  induction c; intros P.
  - bcase (BR_Skip P) ltac:(intros t []) ltac:(intros t []).
  - bcase (BR_Asgn P x a) ltac:(intros t []) ltac:(intros t []).
  - bcase (BR_Seq P (spB c1 P) (spB c2 (spB c1 P)) c1 c2)
      ltac:(intros t [-> | ->]; auto)
      ltac:(intros t [-> | ->]; apply fexact_img).
  - bcase (BR_If P (spB c1 (bwith P b)) (spB c2 (bwithout P b)) b c1 c2)
      ltac:(intros t [-> | ->]; auto)
      ltac:(intros t [-> | ->]; apply fexact_img).
  - bcase (BR_While P b c (fun s => spB c (single_b s b)))
      ltac:(intros t [s ->]; apply IHc)
      ltac:(intros t [s ->]; apply fexact_img).
  - bcase (BR_Choice P (spB c1 P) (spB c2 P) c1 c2)
      ltac:(intros t [-> | ->]; auto)
      ltac:(intros t [-> | ->]; apply fexact_img).
  - bcase (BR_Havoc P x) ltac:(intros t []) ltac:(intros t []).
Qed.
