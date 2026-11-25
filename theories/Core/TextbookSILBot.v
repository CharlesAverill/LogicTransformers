(** * Textbook sufficient incorrectness with nontermination, complete

    SIL⊥ for the core language: from every state of the precondition,
    some run reaches the postcondition, where ⊥ (divergence) counts as an
    outcome. Textbook rules as primitives: backward rules per construct,
    sequencing, left and right choice, disjunction on the precondition,
    consequence, a descending variant for loops ([SB_Star]), and a
    divergence rule ([SB_Diverge]): if every state of [J] has a body
    step back into [J], the loop can diverge from every state of [J].

    [silb_text_complete]: complete. The proof derives the triple whose
    precondition is the bottom-face preimage of the post. A state can
    reach the post through a loop in three ways, each covered:
    - by finitely many iterations, or by the body diverging after
      finitely many: the descending variant;
    - by iterating forever: the divergence rule.

    Soundness is constructive. Completeness uses [classic]. *)

From Stdlib Require Import Classical.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Verified.
From LogicTransformers.Core Require Import Kernel KernelBot.

Section TextbookSILBot.

Context {Σ Act : Type} (act_sem : Act -> Σ -> Σ -> Prop).

Notation B := (KLangB act_sem).
Notation kev := (kev act_sem).
Notation kdiv := (kdiv act_sem).
Notation semKB := (semKB act_sem).
Notation com := (kcom Σ Act).
Notation kt P c Q := (@mkTriple B P c Q).

Definition nop : @triple B -> Prop := fun _ => False.
Definition one (t1 : @triple B) : @triple B -> Prop := fun t => t = t1.
Definition two (t1 t2 : @triple B) : @triple B -> Prop :=
  fun t => t = t1 \/ t = t2.

Definition som (X : Σ -> Prop) : option Σ -> Prop :=
  fun o => match o with Some s => X s | None => False end.

Lemma silbv : forall P c Q, cvalid Backward Plain Under (kt P c Q) <->
    (forall o, P o -> exists o', semKB c o o' /\ Q o').
Proof. intros. simpl. unfold aimpl, preimg. firstorder. Qed.

(** ** The rules *)

Inductive silb_text : @ruleset B :=
  | SB_Skip : forall Q, silb_text nop (kt Q KSkip Q)
  | SB_Act : forall Q a,
      silb_text nop
        (kt (fun o => match o with
                      | Some s => exists s', act_sem a s s' /\ Q (Some s')
                      | None => Q None end) (KAct a) Q)
  | SB_Assume : forall Q Bt,
      silb_text nop
        (kt (fun o => match o with
                      | Some s => Bt s /\ Q (Some s)
                      | None => Q None end) (KAssume Bt) Q)
  | SB_Seq : forall P R Q c1 c2,
      silb_text (two (kt P c1 R) (kt R c2 Q)) (kt P (KSeq c1 c2) Q)
  | SB_ChoiceL : forall P Q c1 c2,
      silb_text (one (kt P c1 Q)) (kt P (KChoice c1 c2) Q)
  | SB_ChoiceR : forall P Q c1 c2,
      silb_text (one (kt P c2 Q)) (kt P (KChoice c1 c2) Q)
  | SB_Disj : forall P1 P2 Q c,
      silb_text (two (kt P1 c Q) (kt P2 c Q)) (kt (fun o => P1 o \/ P2 o) c Q)
  | SB_Star : forall (X : nat -> option Σ -> Prop) c,
      silb_text (fun t => exists n, t = kt (X (S n)) c (X n))
                (kt (fun o => exists n, X n o) (KStar c) (X 0))
  | SB_Diverge : forall (Rj : Σ -> Σ -> Prop) (J : Σ -> Prop) c,
      (forall s, J s -> exists s', Rj s s') ->
      (forall s s', Rj s s' -> J s') ->
      silb_text (fun t => exists s s', Rj s s' /\
                   t = kt (fun o => o = Some s) c (fun o => o = Some s'))
                (kt (som J) (KStar c) (fun o => o = None))
  | SB_Cons : forall P P' Q Q' c,
      (forall o, P o -> P' o) -> (forall o, Q' o -> Q o) ->
      silb_text (one (kt P' c Q')) (kt P c Q).

Definition SILB_text : @ProgramLogic B :=
  mkLogic (cvalid Backward Plain Under) (cvalid_proper _ _ _) silb_text.

(** ** Soundness *)

Lemma semKB_star_cons : forall c o o1 o',
    semKB c o o1 -> semKB (KStar c) o1 o' -> semKB (KStar c) o o'.
Proof.
  intros c [s|] [s1|] [s'|] H1 H2; simpl in *; try contradiction; auto.
  - eapply KE_StarStep; eassumption.
  - eapply KD_StarIter; eassumption.
  - apply KD_StarBody. exact H1.
Qed.

Lemma sdiverge_sound : forall c (Rj : Σ -> Σ -> Prop) (J : Σ -> Prop),
    (forall s, J s -> exists s', Rj s s') ->
    (forall s s', Rj s s' -> J s') ->
    (forall s s', Rj s s' -> kev c s s') ->
    forall s, J s -> kdiv (KStar c) s.
Proof.
  intros c Rj J Htot Hin Hrun. cofix CH. intros s Hs.
  destruct (Htot s Hs) as [s' Hr].
  exact (KD_StarIter act_sem c s s' (Hrun s s' Hr) (CH s' (Hin s s' Hr))).
Qed.

Theorem silb_text_lsound : locally_sound SILB_text.
Proof.
  intros ps t HR Hps. simpl in *. destruct HR; apply silbv.
  - intros o HQ. exists o. split; [apply semKB_skip; reflexivity | exact HQ].
  - intros [s|] H.
    + destruct H as [s' [Ha HQ]]. exists (Some s').
      split; [apply semKB_act; exact Ha | exact HQ].
    + exists None. split; [apply semKB_none; reflexivity | exact H].
  - intros [s|] H.
    + destruct H as [HB HQ]. exists (Some s).
      split; [apply semKB_assume; auto | exact HQ].
    + exists None. split; [apply semKB_none; reflexivity | exact H].
  - pose proof (proj1 (silbv _ _ _) (Hps _ (or_introl eq_refl))) as H1.
    pose proof (proj1 (silbv _ _ _) (Hps _ (or_intror eq_refl))) as H2.
    intros o HP. destruct (H1 o HP) as [o1 [Ha HR]].
    destruct (H2 o1 HR) as [o2 [Hb HQ]].
    exists o2. split; [apply semKB_seq; eauto | exact HQ].
  - pose proof (proj1 (silbv _ _ _) (Hps _ eq_refl)) as H1.
    intros o HP. destruct (H1 o HP) as [o' [Hk HQ]].
    exists o'. split; [apply semKB_choice; auto | exact HQ].
  - pose proof (proj1 (silbv _ _ _) (Hps _ eq_refl)) as H1.
    intros o HP. destruct (H1 o HP) as [o' [Hk HQ]].
    exists o'. split; [apply semKB_choice; auto | exact HQ].
  - pose proof (proj1 (silbv _ _ _) (Hps _ (or_introl eq_refl))) as H1.
    pose proof (proj1 (silbv _ _ _) (Hps _ (or_intror eq_refl))) as H2.
    intros o [HP | HP]; [apply H1 | apply H2]; exact HP.
  - assert (Hn : forall n o, X n o ->
                 exists o', semKB (KStar c) o o' /\ X 0 o').
    { induction n as [|n IH]; intros o Hx.
      - exists o. split; [| exact Hx].
        destruct o as [s|]; simpl; [apply KE_StarRefl | exact I].
      - pose proof (proj1 (silbv _ _ _) (Hps _ (ex_intro _ n eq_refl))) as H1.
        destruct (H1 o Hx) as [o1 [Hk Hx1]].
        destruct (IH o1 Hx1) as [o' [Hs Hx0]].
        exists o'. split; [eapply semKB_star_cons; eassumption | exact Hx0]. }
    intros o [n Hx]. exact (Hn n o Hx).
  - intros [s|] HJ; simpl in HJ; [| contradiction].
    exists None. split; [| reflexivity]. simpl.
    apply (sdiverge_sound c Rj J); [assumption | assumption | | assumption].
    intros x x' Hr.
    pose proof (proj1 (silbv _ _ _)
                  (Hps _ (ex_intro _ x (ex_intro _ x' (conj Hr eq_refl)))))
      as Hv.
    destruct (Hv (Some x) eq_refl) as [o' [Hk E]]. subst o'. exact Hk.
  - pose proof (proj1 (silbv _ _ _) (Hps _ eq_refl)) as H1.
    intros o HP. destruct (H1 o (H o HP)) as [o' [Hk HQ]].
    exists o'. split; [exact Hk | apply H0, HQ].
Qed.

(** ** Completeness *)

Definition preB (c : com) (Q : option Σ -> Prop) : option Σ -> Prop :=
  fun o => exists o', semKB c o o' /\ Q o'.

Fixpoint itP (c : com) (Q : option Σ -> Prop) (n : nat) : option Σ -> Prop :=
  match n with
  | 0 => Q
  | S m => preB c (itP c Q m)
  end.

Lemma silb_cons_d : forall P P' Q Q' c,
    derivable silb_text (kt P' c Q') ->
    (forall o, P o -> P' o) -> (forall o, Q' o -> Q o) ->
    derivable silb_text (kt P c Q).
Proof.
  intros P P' Q Q' c D HP HQ.
  apply (D_Rule _ (one (kt P' c Q'))); [apply SB_Cons; assumption |].
  intros t ->. exact D.
Qed.

(** A state from which the loop reaches [o'] in [Q] lies in some
    iterate, if the loop's run passes through a state of [itP]. *)
Lemma star_itP : forall c Q s s1, kev (KStar c) s s1 ->
    forall n, itP c Q n (Some s1) -> exists m, itP c Q m (Some s).
Proof.
  intros c Q s s1 H. remember (KStar c) as k eqn:Ek.
  induction H; inversion Ek; subst; intros n Hn; [eauto |].
  destruct (IHkev2 eq_refl n Hn) as [m Hm].
  exists (S m). exists (Some s1). split; assumption.
Qed.

Definition bodyReachS (c : com) (x : Σ) : Prop :=
  exists y, kev (KStar c) x y /\ kdiv c y.

Lemma silb_pre : forall c Q, derivable silb_text (kt (preB c Q) c Q).
Proof.
  induction c; intros Q.
  - apply (silb_cons_d _ Q _ Q); [| | auto].
    + apply (D_Rule _ nop); [apply SB_Skip | intros t []].
    + intros o [o' [Hk HQ]]. apply semKB_skip in Hk. subst. exact HQ.
  - apply (silb_cons_d _ (fun o => match o with
             | Some s => exists s', act_sem a s s' /\ Q (Some s')
             | None => Q None end) _ Q); [| | auto].
    + apply (D_Rule _ nop); [apply SB_Act | intros t []].
    + intros [s|] [[s'|] [Hk HQ]]; apply semKB_act in Hk; simpl in *;
        try contradiction; eauto.
  - apply (silb_cons_d _ (fun o => match o with
             | Some s => B s /\ Q (Some s)
             | None => Q None end) _ Q); [| | auto].
    + apply (D_Rule _ nop); [apply SB_Assume | intros t []].
    + intros [s|] [[s'|] [Hk HQ]]; apply semKB_assume in Hk; simpl in *;
        try contradiction.
      * destruct Hk as [E HB]. subst. auto.
      * exact HQ.
  - apply (silb_cons_d _ (preB c1 (preB c2 Q)) _ Q); [| | auto].
    + apply (D_Rule _ (two (kt (preB c1 (preB c2 Q)) c1 (preB c2 Q))
                           (kt (preB c2 Q) c2 Q)));
        [apply SB_Seq | intros t [-> | ->]; auto].
    + intros o [o'' [Hk HQ]]. apply semKB_seq in Hk as [o' [H1 H2]].
      exists o'. split; [exact H1 | exists o''; auto].
  - apply (silb_cons_d _ (fun o => preB c1 Q o \/ preB c2 Q o) _ Q);
      [| | auto].
    + apply (D_Rule _ (two (kt (preB c1 Q) (KChoice c1 c2) Q)
                           (kt (preB c2 Q) (KChoice c1 c2) Q)));
        [apply SB_Disj |].
      intros t [-> | ->].
      * apply (D_Rule _ (one (kt (preB c1 Q) c1 Q))); [apply SB_ChoiceL |].
        intros t ->. apply IHc1.
      * apply (D_Rule _ (one (kt (preB c2 Q) c2 Q))); [apply SB_ChoiceR |].
        intros t ->. apply IHc2.
    + intros o [o' [Hk HQ]]. apply semKB_choice in Hk as [Hk | Hk];
        [left | right]; exists o'; auto.
  - (* the descending variant *)
    assert (D1 : derivable silb_text
                   (kt (fun o => exists n, itP c Q n o) (KStar c) Q)).
    { apply (D_Rule _ (fun t => exists n,
                         t = kt (itP c Q (S n)) c (itP c Q n)));
        [apply (SB_Star (itP c Q)) |].
      intros t [n ->]. apply IHc. }
    (* the divergence rule *)
    set (Jd := fun x => kdiv (KStar c) x /\ ~ bodyReachS c x).
    assert (Hstep : forall x, Jd x -> exists x', kev c x x' /\ Jd x').
    { intros x [Hd Hn]. inversion Hd; subst.
      - exfalso. apply Hn. exists x. split; [apply KE_StarRefl | assumption].
      - match goal with Hk : kev c x ?x1, Hd1 : kdiv (KStar c) ?x1 |- _ =>
          exists x1; split; [exact Hk |]; split; [exact Hd1 |];
          intros [y [Hy Hdy]]; apply Hn; exists y;
          split; [eapply KE_StarStep; eassumption | exact Hdy] end. }
    assert (D2 : derivable silb_text
                   (kt (fun o => Q None /\ som Jd o) (KStar c) Q)).
    { destruct (classic (Q None)) as [HQn | HQn].
      - apply (silb_cons_d _ (som Jd) _ (fun o => o = None));
          [| intros o [_ H]; exact H | intros o ->; exact HQn].
        apply (D_Rule _ (fun t => exists s s',
                  (fun x x' => kev c x x' /\ Jd x') s s' /\
                  t = kt (fun o => o = Some s) c (fun o => o = Some s'))).
        + apply (SB_Diverge (fun x x' => kev c x x' /\ Jd x') Jd c).
          * intros x Hx. destruct (Hstep x Hx) as [x' Hx']. eauto.
          * intros x x' [_ H]. exact H.
        + intros t [x [x' [[Hk _] ->]]].
          apply (silb_cons_d _ (preB c (fun o => o = Some x')) _
                   (fun o => o = Some x'));
            [apply IHc | intros o -> ; exists (Some x'); auto | auto].
      - apply (silb_cons_d _ (fun o => exists n, itP c Q n o) _ Q);
          [exact D1 | intros o [H _]; contradiction | auto]. }
    apply (silb_cons_d _ (fun o => (exists n, itP c Q n o) \/
                                   (Q None /\ som Jd o)) _ Q); [| | auto].
    + apply (D_Rule _ (two (kt (fun o => exists n, itP c Q n o) (KStar c) Q)
                           (kt (fun o => Q None /\ som Jd o) (KStar c) Q)));
        [apply SB_Disj | intros t [-> | ->]; assumption].
    + intros [s|] [[s'|] [Hk HQ]]; simpl in Hk; try contradiction.
      * left. exact (star_itP c Q s s' Hk 0 HQ).
      * destruct (classic (bodyReachS c s)) as [[y [Hy Hdy]] | Hnb].
        -- left. destruct (star_itP c Q s y Hy 1) as [m Hm].
           ++ exists None. split; [exact Hdy | exact HQ].
           ++ exists m. exact Hm.
        -- right. split; [exact HQ |]. split; assumption.
      * left. exists 0. exact HQ.
Qed.

Theorem silb_text_complete : complete SILB_text.
Proof.
  intros [P c Q] V0.
  pose proof (proj1 (silbv P c Q) V0) as V. clear V0.
  apply (silb_cons_d _ (preB c Q) _ Q); [apply silb_pre | | auto].
  intros o HP. exact (V o HP).
Qed.

Definition vSILB_text : VLogic B Backward Plain Under :=
  @mkVLogic B Backward Plain Under SILB_text (fun t => iff_refl _)
    silb_text_lsound silb_text_complete.

End TextbookSILBot.
