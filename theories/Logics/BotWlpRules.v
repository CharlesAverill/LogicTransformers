(** * Backward (wlp⊥) rules for the bottom face

    Rules over [ImpBot] that are sound for HL⊥ and for the wlp-dual
    ([dual_valid]: [wlp c Q ⊆ P]), and so derive exact weakest liberal
    preconditions with ⊥ ([wexactB]). Under complement they become the
    SIL⊥ rules, as on the top face.

    The loop rule [WR_While] needs the step relation of the body, which
    backward triples give only through complements. Its premises are

    - [(W s', c, ≠ s')]: [W s'] is (at least) the states that cannot reach
      [s'], so outside [W s'] lies a step to [s'];
    - [(Wd, c, ≠ ⊥)]: outside [Wd] lies a body divergence.

    These yield a step relation [stepsW W Wd], and the chain machinery of
    the forward rules ([reachF], [infF]) is reused. Reading steps off
    complements makes the wlp-dual soundness of this rule classical. *)

From Stdlib Require Import Classical.
From LogicTransformers.Imp Require Import Syntax BigStep Diverge LangBot.
From LogicTransformers.Logics Require Import Hoare BotRules.
From LogicTransformers.Framework Require Import Language ProgramLogic Cube.

Notation wlpB := (@wlp ImpBot).

Definition neqS (s' : state) : assertion ImpBot := fun o => o <> Some s'.
Definition neqNone : assertion ImpBot := fun o => o <> None.

Definition asgnB_pre (x : var) (a : aexp) (Q : assertion ImpBot)
  : assertion ImpBot :=
  fun o => match o with
           | Some s => Q (Some (update s x (aeval s a)))
           | None => Q None
           end.

Definition havocB_pre (x : var) (Q : assertion ImpBot) : assertion ImpBot :=
  fun o => match o with
           | Some s => forall n, Q (Some (update s x n))
           | None => Q None
           end.

Definition ifB_pre (b : bexp) (P1 P2 : assertion ImpBot) : assertion ImpBot :=
  fun o => match o with
           | Some s =>
               (bassn b s -> P1 (Some s)) /\ (~ bassn b s -> P2 (Some s))
           | None => P1 None /\ P2 None
           end.

(** The body's step relation, read off the premises' pres. *)
Definition stepsW (W : state -> assertion ImpBot) (Wd : assertion ImpBot)
  : state -> assertion ImpBot :=
  fun s o => match o with
             | Some s' => ~ W s' (Some s)
             | None => ~ Wd (Some s)
             end.

Definition wloop_pre (b : bexp) (W : state -> assertion ImpBot)
    (Wd : assertion ImpBot) (Q : assertion ImpBot) : assertion ImpBot :=
  fun o => match o with
           | None => Q None
           | Some s =>
               (forall s', reachF b (stepsW W Wd) s s' -> ~ bassn b s' ->
                           Q (Some s')) /\
               ((exists s1, reachF b (stepsW W Wd) s s1 /\ bassn b s1 /\
                            ~ Wd (Some s1)) \/
                infF b (stepsW W Wd) s -> Q None)
           end.

Inductive wrule_name := WSkip | WAsgn | WSeq | WIf | WChoice | WHavoc | WWhile.

Inductive wrule : wrule_name -> ruleset ImpBot :=
  | WR_Skip : forall Q,
      wrule WSkip pr0 (hb Q CSkip Q)
  | WR_Asgn : forall Q x a,
      wrule WAsgn pr0 (hb (asgnB_pre x a Q) (CAsgn x a) Q)
  | WR_Seq : forall P Q R c1 c2,
      wrule WSeq (pr2 (hb P c1 Q) (hb Q c2 R)) (hb P (CSeq c1 c2) R)
  | WR_If : forall P1 P2 Q b c1 c2,
      wrule WIf (pr2 (hb P1 c1 Q) (hb P2 c2 Q))
        (hb (ifB_pre b P1 P2) (CIf b c1 c2) Q)
  | WR_Choice : forall P1 P2 Q c1 c2,
      wrule WChoice (pr2 (hb P1 c1 Q) (hb P2 c2 Q))
        (hb (fun o => P1 o /\ P2 o) (CChoice c1 c2) Q)
  | WR_Havoc : forall Q x,
      wrule WHavoc pr0 (hb (havocB_pre x Q) (CHavoc x) Q)
  | WR_While : forall Q b c (W : state -> assertion ImpBot) Wd,
      wrule WWhile
        (fun t => (exists s', t = hb (W s') c (neqS s')) \/
                  t = hb Wd c neqNone)
        (hb (wloop_pre b W Wd Q) (CWhile b c) Q).

(** ** HL⊥ soundness *)

Theorem wrule_over_sound : forall r ps c,
    wrule r ps c ->
    (forall t, ps t -> cube_valid Forward Over t) ->
    cube_valid Forward Over c.
Proof.
  intros r ps c HR H. pose proof (over_premB _ H) as H'. clear H.
  apply hl_valid_iff.
  destruct HR; cbn; intros o o' HP Hc.
  - apply semB_skip in Hc. subst. exact HP.
  - apply semB_asgn in Hc. destruct o as [s|]; subst; exact HP.
  - apply semB_seq in Hc as [o1 [H1 H2]].
    apply (H' _ (or_intror eq_refl) o1); [| exact H2].
    apply (H' _ (or_introl eq_refl) o); assumption.
  - destruct o as [s|].
    + apply semB_if in Hc as [[Hb Hc] | [Hb Hc]].
      * apply (H' _ (or_introl eq_refl) (Some s)); [apply (proj1 HP) |];
          assumption.
      * apply (H' _ (or_intror eq_refl) (Some s));
          [apply (proj2 HP), bassn_false' |]; assumption.
    + apply semB_none in Hc. subst.
      apply (H' _ (or_introl eq_refl) None); [apply (proj1 HP) | exact I].
  - apply semB_choice in Hc as [Hc | Hc].
    + apply (H' _ (or_introl eq_refl) o); [apply (proj1 HP) | exact Hc].
    + apply (H' _ (or_intror eq_refl) o); [apply (proj2 HP) | exact Hc].
  - apply semB_havoc in Hc. destruct o as [s|].
    + destruct Hc as [n ->]. apply HP.
    + subst. exact HP.
  - assert (Hst : forall s s', bassn b s -> ceval c s s' ->
                               stepsW W Wd s (Some s')).
    { intros s s' Hb Hc1 HW.
      exact (H' _ (or_introl (ex_intro _ s' eq_refl)) (Some s) (Some s')
                HW Hc1 eq_refl). }
    assert (Hdv : forall s, bassn b s -> diverges c s -> ~ Wd (Some s)).
    { intros s Hb Hd HW.
      exact (H' _ (or_intror eq_refl) (Some s) None HW Hd eq_refl). }
    destruct o as [s|]; [destruct o' as [s'|] |].
    + destruct (loop_over_term b c _ Hst s s' Hc) as [Hr Hnb].
      apply (proj1 HP); assumption.
    + apply (proj2 HP).
      destruct (loop_over_div b c _ Hst s Hc) as [[s1 [Hr [Hb Hd]]] | Hinf].
      * left. exists s1. repeat split; auto.
      * right. exact Hinf.
    + apply semB_none in Hc. subst. exact HP.
Qed.

(** ** Soundness for the wlp-dual *)

Lemma dual_premB : forall (ps : triple ImpBot -> Prop),
    (forall t, ps t -> dual_valid t) ->
    forall t, ps t ->
    forall o, (forall o', semB (cmd t) o o' -> post t o') -> pre t o.
Proof. intros ps H t Ht. apply H, Ht. Qed.

Theorem wrule_dual_sound : forall r ps c,
    wrule r ps c ->
    (forall t, ps t -> dual_valid t) ->
    dual_valid c.
Proof.
  intros r ps c HR H. pose proof (dual_premB _ H) as H'. clear H.
  destruct HR; unfold dual_valid, aimpl, wlp; cbn; intros o Hw.
  - apply Hw, semB_skip. reflexivity.
  - destruct o as [s|]; apply Hw; [apply semB_asgn; reflexivity | exact I].
  - apply (H' _ (or_introl eq_refl) o). intros o1 H1.
    apply (H' _ (or_intror eq_refl) o1). intros o2 H2.
    apply Hw, semB_seq. exists o1. auto.
  - destruct o as [s|].
    + split; intros Hb.
      * apply (H' _ (or_introl eq_refl) (Some s)). intros o' Hc.
        apply Hw, semB_if. left. split; assumption.
      * apply (H' _ (or_intror eq_refl) (Some s)). intros o' Hc.
        apply Hw, semB_if. right.
        split; [apply bassn_false; assumption | assumption].
    + split; [apply (H' _ (or_introl eq_refl) None)
             | apply (H' _ (or_intror eq_refl) None)];
        intros o' Hc; apply semB_none in Hc; subst; apply Hw; exact I.
  - split; [apply (H' _ (or_introl eq_refl) o)
           | apply (H' _ (or_intror eq_refl) o)];
      intros o' Hc; apply Hw, semB_choice; auto.
  - destruct o as [s|].
    + intros n. apply Hw, semB_havoc. exists n. reflexivity.
    + apply Hw. exact I.
  - assert (Hreal : forall s s', bassn b s -> stepsW W Wd s (Some s') ->
                                 ceval c s s').
    { intros s s' _ HnW. apply NNPP. intros Hnc. apply HnW.
      apply (H' _ (or_introl (ex_intro _ s' eq_refl)) (Some s)).
      intros [s''|] Hc Heq; [| discriminate].
      inversion Heq; subst. contradiction. }
    assert (Hreal_div : forall s, ~ Wd (Some s) -> diverges c s).
    { intros s HnWd. apply NNPP. intros Hnd. apply HnWd.
      apply (H' _ (or_intror eq_refl) (Some s)).
      intros [s''|] Hc Heq; [discriminate | contradiction]. }
    destruct o as [s|]; [split | apply Hw; exact I].
    + intros s' Hr Hnb. apply Hw. simpl.
      apply (proj1 (loop_under_reach b c _ Hreal s s' Hr)).
      apply E_WhileFalse, bassn_false, Hnb.
    + intros [[s1 [Hr [Hb HnWd]]] | Hinf]; apply Hw; simpl.
      * apply (proj2 (loop_under_reach b c _ Hreal s s1 Hr)).
        apply Dv_WhileBody; [exact Hb | apply Hreal_div, HnWd].
      * exact (loop_under_inf b c _ Hreal s Hinf).
Qed.

(** ** Exactness *)

Definition wbase : ruleset ImpBot := fun ps c => exists r, wrule r ps c.

Lemma wrule_der : forall r ps c,
    wrule r ps c ->
    (forall t, ps t -> derivable wbase t) -> derivable wbase c.
Proof. intros r ps c HR H. eapply D_Rule; [exists r; exact HR | exact H]. Qed.

Lemma wrule_exact_step : forall r ps c,
    wrule r ps c -> (forall t, ps t -> pexact t) -> pexact c.
Proof.
  intros r ps c HR H. apply pexact_iff. split.
  - apply (wrule_over_sound r ps c HR).
    intros t Ht. apply pexact_iff, H, Ht.
  - apply (wrule_dual_sound r ps c HR).
    intros t Ht. apply pexact_iff, H, Ht.
Qed.

Ltac wcase HR prems_der prems_ex :=
  eapply D_Equiv;
  [ eapply (wrule_der _ _ _ HR); prems_der
  | apply pexact_equiv; eapply (wrule_exact_step _ _ _ HR); prems_ex ].

Theorem wexactB : forall c Q, derivable wbase (hb (wlpB c Q) c Q).
Proof.
  induction c; intros Q.
  - wcase (WR_Skip Q) ltac:(intros t []) ltac:(intros t []).
  - wcase (WR_Asgn Q x a) ltac:(intros t []) ltac:(intros t []).
  - wcase (WR_Seq (wlpB c1 (wlpB c2 Q)) (wlpB c2 Q) Q c1 c2)
      ltac:(intros t [-> | ->]; auto)
      ltac:(intros t [-> | ->]; apply pexact_wlp).
  - wcase (WR_If (wlpB c1 Q) (wlpB c2 Q) Q b c1 c2)
      ltac:(intros t [-> | ->]; auto)
      ltac:(intros t [-> | ->]; apply pexact_wlp).
  - wcase (WR_While Q b c (fun s' => wlpB c (neqS s')) (wlpB c neqNone))
      ltac:(intros t [[s' ->] | ->]; apply IHc)
      ltac:(intros t [[s' ->] | ->]; apply pexact_wlp).
  - wcase (WR_Choice (wlpB c1 Q) (wlpB c2 Q) Q c1 c2)
      ltac:(intros t [-> | ->]; auto)
      ltac:(intros t [-> | ->]; apply pexact_wlp).
  - wcase (WR_Havoc Q x) ltac:(intros t []) ltac:(intros t []).
Qed.
