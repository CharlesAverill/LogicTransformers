(** * Textbook incorrectness logic with nontermination, complete

    IL⊥ for the core language, with textbook rules as primitives: one
    rule per construct (on states that may be ⊥), sequencing, left and
    right choice, disjunction, consequence, the iteration-indexed loop
    rule, and a *divergence rule* ([IB_Diverge]): if a relation [Rj] on
    a set [J] is total on [J], stays in [J], and every [Rj] step is a
    run of the body, then the loop can run forever from any state of
    [J]. This is the recurrent-set principle for proving
    nontermination, as a proof rule.

    [ilb_text_complete]: the system is complete. The proof derives the
    triple whose post is the bottom-face strongest postcondition, by
    induction on the program. A loop can reach ⊥ in three ways, each
    covered:
    - ⊥ was already in the precondition, or the body diverges at a
      reachable iterate: the iteration rule, since each iterate's
      strongest post contains ⊥ in that case;
    - the loop iterates forever: the divergence rule, with [J] the
      states from which the loop diverges without the body ever
      diverging.

    Soundness is constructive. Completeness uses [classic], to split on
    how a loop diverges. *)

From Stdlib Require Import Classical.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Verified.
From LogicTransformers.Core Require Import Kernel KernelBot.

Section TextbookILBot.

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

Lemma ilbv : forall P c Q, cvalid Forward Plain Under (kt P c Q) <->
    (forall o', Q o' -> exists o, P o /\ semKB c o o').
Proof. intros. simpl. unfold aimpl, img. firstorder. Qed.

(** ** The rules *)

Inductive ilb_text : @ruleset B :=
  | IB_Skip : forall P, ilb_text nop (kt P KSkip P)
  | IB_Act : forall P a,
      ilb_text nop
        (kt P (KAct a)
            (fun o' => match o' with
                       | Some s' => exists s, P (Some s) /\ act_sem a s s'
                       | None => P None end))
  | IB_Assume : forall P Bt,
      ilb_text nop
        (kt P (KAssume Bt)
            (fun o => match o with
                      | Some s => P (Some s) /\ Bt s
                      | None => P None end))
  | IB_Seq : forall P R Q c1 c2,
      ilb_text (two (kt P c1 R) (kt R c2 Q)) (kt P (KSeq c1 c2) Q)
  | IB_ChoiceL : forall P Q c1 c2,
      ilb_text (one (kt P c1 Q)) (kt P (KChoice c1 c2) Q)
  | IB_ChoiceR : forall P Q c1 c2,
      ilb_text (one (kt P c2 Q)) (kt P (KChoice c1 c2) Q)
  | IB_Disj : forall P Q1 Q2 c,
      ilb_text (two (kt P c Q1) (kt P c Q2)) (kt P c (fun o => Q1 o \/ Q2 o))
  | IB_Star : forall (X : nat -> option Σ -> Prop) c,
      ilb_text (fun t => exists n, t = kt (X n) c (X (S n)))
               (kt (X 0) (KStar c) (fun o => exists n, X n o))
  | IB_Diverge : forall (Rj : Σ -> Σ -> Prop) (J : Σ -> Prop) c s0,
      J s0 -> (forall s, J s -> exists s', Rj s s') ->
      (forall s s', Rj s s' -> J s') ->
      ilb_text (fun t => exists s s', Rj s s' /\
                  t = kt (fun o => o = Some s) c (fun o => o = Some s'))
               (kt (fun o => o = Some s0) (KStar c) (fun o => o = None))
  | IB_Cons : forall P P' Q Q' c,
      (forall o, P' o -> P o) -> (forall o, Q o -> Q' o) ->
      ilb_text (one (kt P' c Q')) (kt P c Q).

Definition ILB_text : @ProgramLogic B :=
  mkLogic (cvalid Forward Plain Under) (cvalid_proper _ _ _) ilb_text.

(** ** Soundness *)

Lemma star_div_body : forall c s s1,
    kev (KStar c) s s1 -> kdiv c s1 -> kdiv (KStar c) s.
Proof.
  intros c s s1 H. remember (KStar c) as k eqn:Ek.
  induction H; inversion Ek; subst; intros Hd.
  - apply KD_StarBody, Hd.
  - eapply KD_StarIter; [eassumption | apply IHkev2; auto].
Qed.

Lemma semKB_star_snoc : forall c o o1 o',
    semKB (KStar c) o o1 -> semKB c o1 o' -> semKB (KStar c) o o'.
Proof.
  intros c [s|] [s1|] [s'|] H1 H2; simpl in *; try contradiction; auto.
  - eapply kev_star_snoc; eassumption.
  - eapply star_div_body; eassumption.
Qed.

Lemma diverge_sound : forall c (Rj : Σ -> Σ -> Prop) (J : Σ -> Prop),
    (forall s, J s -> exists s', Rj s s') ->
    (forall s s', Rj s s' -> J s') ->
    (forall s s', Rj s s' -> kev c s s') ->
    forall s, J s -> kdiv (KStar c) s.
Proof.
  intros c Rj J Htot Hin Hrun. cofix CH. intros s Hs.
  destruct (Htot s Hs) as [s' Hr].
  exact (KD_StarIter act_sem c s s' (Hrun s s' Hr) (CH s' (Hin s s' Hr))).
Qed.

Theorem ilb_text_lsound : locally_sound ILB_text.
Proof.
  intros ps t HR Hps. simpl in *. destruct HR; apply ilbv.
  - intros o' HP. exists o'. split; [exact HP | apply semKB_skip; reflexivity].
  - intros [s'|] H.
    + destruct H as [s [HP Ha]]. exists (Some s).
      split; [exact HP | apply semKB_act; exact Ha].
    + exists None. split; [exact H | apply semKB_none; reflexivity].
  - intros [s|] H.
    + destruct H as [HP HB]. exists (Some s).
      split; [exact HP | apply semKB_assume; auto].
    + exists None. split; [exact H | apply semKB_none; reflexivity].
  - pose proof (proj1 (ilbv _ _ _) (Hps _ (or_introl eq_refl))) as H1.
    pose proof (proj1 (ilbv _ _ _) (Hps _ (or_intror eq_refl))) as H2.
    intros o'' HQ. destruct (H2 o'' HQ) as [o' [HR Hb]].
    destruct (H1 o' HR) as [o [HP Ha]].
    exists o. split; [exact HP | apply semKB_seq; eauto].
  - pose proof (proj1 (ilbv _ _ _) (Hps _ eq_refl)) as H1.
    intros o' HQ. destruct (H1 o' HQ) as [o [HP Hk]].
    exists o. split; [exact HP | apply semKB_choice; auto].
  - pose proof (proj1 (ilbv _ _ _) (Hps _ eq_refl)) as H1.
    intros o' HQ. destruct (H1 o' HQ) as [o [HP Hk]].
    exists o. split; [exact HP | apply semKB_choice; auto].
  - pose proof (proj1 (ilbv _ _ _) (Hps _ (or_introl eq_refl))) as H1.
    pose proof (proj1 (ilbv _ _ _) (Hps _ (or_intror eq_refl))) as H2.
    intros o' [HQ | HQ]; [apply H1 | apply H2]; exact HQ.
  - assert (Hn : forall n o', X n o' ->
                 exists o, X 0 o /\ semKB (KStar c) o o').
    { induction n as [|n IH]; intros o' Hx.
      - exists o'. split; [exact Hx |].
        destruct o' as [s|]; simpl; [apply KE_StarRefl | exact I].
      - pose proof (proj1 (ilbv _ _ _) (Hps _ (ex_intro _ n eq_refl))) as H1.
        destruct (H1 o' Hx) as [o1 [Hx1 Hk]].
        destruct (IH o1 Hx1) as [o [Hx0 Hs]].
        exists o. split; [exact Hx0 | eapply semKB_star_snoc; eassumption]. }
    intros o' [n Hx]. exact (Hn n o' Hx).
  - intros o' ->. exists (Some s0). split; [reflexivity |]. simpl.
    apply (diverge_sound c Rj J); [assumption | assumption | | assumption].
    intros s s' Hr.
    pose proof (proj1 (ilbv _ _ _)
                  (Hps _ (ex_intro _ s (ex_intro _ s' (conj Hr eq_refl)))))
      as Hv.
    destruct (Hv (Some s') eq_refl) as [o [E Hk]]. subst o. exact Hk.
  - pose proof (proj1 (ilbv _ _ _) (Hps _ eq_refl)) as H1.
    intros o' HQ. destruct (H1 o' (H0 o' HQ)) as [o [HP Hk]].
    exists o. split; [apply H, HP | exact Hk].
Qed.

(** ** Completeness *)

Definition spB (c : com) (P : option Σ -> Prop) : option Σ -> Prop :=
  fun o' => exists o, P o /\ semKB c o o'.

Fixpoint itB (c : com) (P : option Σ -> Prop) (n : nat) : option Σ -> Prop :=
  match n with
  | 0 => P
  | S m => spB c (itB c P m)
  end.

Lemma ilb_cons_d : forall P P' Q Q' c,
    derivable ilb_text (kt P' c Q') ->
    (forall o, P' o -> P o) -> (forall o, Q o -> Q' o) ->
    derivable ilb_text (kt P c Q).
Proof.
  intros P P' Q Q' c D HP HQ.
  apply (D_Rule _ (one (kt P' c Q'))); [apply IB_Cons; assumption |].
  intros t ->. exact D.
Qed.

Lemma it_star : forall c P s s', kev (KStar c) s s' ->
    forall n, itB c P n (Some s) -> exists m, itB c P m (Some s').
Proof.
  intros c P s s' H. remember (KStar c) as k eqn:Ek.
  induction H; inversion Ek; subst; intros n Hn; [eauto |].
  apply (IHkev2 eq_refl (S n)). exists (Some s). split; assumption.
Qed.

Definition bodyReach (c : com) (x : Σ) : Prop :=
  exists y, kev (KStar c) x y /\ kdiv c y.

Lemma ilb_sp : forall c P, derivable ilb_text (kt P c (spB c P)).
Proof.
  induction c; intros P.
  - apply (ilb_cons_d _ P _ P); [| auto |].
    + apply (D_Rule _ nop); [apply IB_Skip | intros t []].
    + intros o' [o [HP Hk]]. apply semKB_skip in Hk. subst. exact HP.
  - apply (ilb_cons_d _ P _ (fun o' => match o' with
             | Some s' => exists s, P (Some s) /\ act_sem a s s'
             | None => P None end)); [| auto |].
    + apply (D_Rule _ nop); [apply IB_Act | intros t []].
    + intros [s'|] [[s|] [HP Hk]]; apply semKB_act in Hk; simpl in *;
        try contradiction; eauto.
  - apply (ilb_cons_d _ P _ (fun o => match o with
             | Some s => P (Some s) /\ B s
             | None => P None end)); [| auto |].
    + apply (D_Rule _ nop); [apply IB_Assume | intros t []].
    + intros [s'|] [[s|] [HP Hk]]; apply semKB_assume in Hk; simpl in *;
        try contradiction.
      * destruct Hk as [E HB]. subst. auto.
      * exact HP.
  - apply (ilb_cons_d _ P _ (spB c2 (spB c1 P))); [| auto |].
    + apply (D_Rule _ (two (kt P c1 (spB c1 P))
                           (kt (spB c1 P) c2 (spB c2 (spB c1 P)))));
        [apply IB_Seq | intros t [-> | ->]; auto].
    + intros o'' [o [HP Hk]]. apply semKB_seq in Hk as [o' [H1 H2]].
      exists o'. split; [exists o; auto | exact H2].
  - apply (ilb_cons_d _ P _ (fun o => spB c1 P o \/ spB c2 P o)); [| auto |].
    + apply (D_Rule _ (two (kt P (KChoice c1 c2) (spB c1 P))
                           (kt P (KChoice c1 c2) (spB c2 P))));
        [apply IB_Disj |].
      intros t [-> | ->].
      * apply (D_Rule _ (one (kt P c1 (spB c1 P)))); [apply IB_ChoiceL |].
        intros t ->. apply IHc1.
      * apply (D_Rule _ (one (kt P c2 (spB c2 P)))); [apply IB_ChoiceR |].
        intros t ->. apply IHc2.
    + intros o' [o [HP Hk]]. apply semKB_choice in Hk as [Hk | Hk];
        [left | right]; exists o; auto.
  - (* the iteration rule *)
    assert (D1 : derivable ilb_text
                   (kt P (KStar c) (fun o => exists n, itB c P n o))).
    { apply (D_Rule _ (fun t => exists n,
                         t = kt (itB c P n) c (itB c P (S n))));
        [apply (IB_Star (itB c P)) |].
      intros t [n ->]. apply IHc. }
    (* the divergence rule, for loops that iterate forever *)
    set (Jd := fun x => kdiv (KStar c) x /\ ~ bodyReach c x).
    assert (Hstep : forall x, Jd x -> exists x', kev c x x' /\ Jd x').
    { intros x [Hd Hn]. inversion Hd; subst.
      - exfalso. apply Hn. exists x. split; [apply KE_StarRefl | assumption].
      - match goal with Hk : kev c x ?x1, Hd1 : kdiv (KStar c) ?x1 |- _ =>
          exists x1; split; [exact Hk |]; split; [exact Hd1 |];
          intros [y [Hy Hdy]]; apply Hn; exists y;
          split; [eapply KE_StarStep; eassumption | exact Hdy] end. }
    destruct (classic (exists s, P (Some s) /\ Jd s)) as [[s0 [HP0 HJ0]] | Hno].
    + assert (D2 : derivable ilb_text (kt P (KStar c) (fun o => o = None))).
      { apply (ilb_cons_d _ (fun o => o = Some s0) _ (fun o => o = None));
          [| intros o ->; exact HP0 | auto].
        apply (D_Rule _ (fun t => exists s s',
                  (fun x x' => kev c x x' /\ Jd x') s s' /\
                  t = kt (fun o => o = Some s) c (fun o => o = Some s'))).
        - apply (IB_Diverge (fun x x' => kev c x x' /\ Jd x') Jd c s0 HJ0).
          + intros x Hx. destruct (Hstep x Hx) as [x' Hx']. eauto.
          + intros x x' [_ H]. exact H.
        - intros t [x [x' [[Hk _] ->]]].
          apply (ilb_cons_d _ (fun o => o = Some x) _
                   (spB c (fun o => o = Some x)));
            [apply IHc | auto | intros o -> ; exists (Some x); auto]. }
      apply (ilb_cons_d _ P _ (fun o => (exists n, itB c P n o) \/ o = None));
        [| auto |].
      * apply (D_Rule _ (two (kt P (KStar c) (fun o => exists n, itB c P n o))
                             (kt P (KStar c) (fun o => o = None))));
          [apply IB_Disj | intros t [-> | ->]; assumption].
      * intros [s'|] [[s|] [HP Hk]]; simpl in Hk; try contradiction.
        -- left. exact (it_star c P s s' Hk 0 HP).
        -- right. reflexivity.
        -- left. exists 0. exact HP.
    + apply (ilb_cons_d _ P _ (fun o => exists n, itB c P n o));
        [exact D1 | auto |].
      intros [s'|] [[s|] [HP Hk]]; simpl in Hk; try contradiction.
      * exact (it_star c P s s' Hk 0 HP).
      * destruct (classic (bodyReach c s)) as [[y [Hy Hdy]] | Hnb].
        -- destruct (it_star c P s y Hy 0 HP) as [m Hm].
           exists (S m). exists (Some y). split; [exact Hm | exact Hdy].
        -- exfalso. apply Hno. exists s. split; [exact HP |]. split; assumption.
      * exists 0. exact HP.
Qed.

Theorem ilb_text_complete : complete ILB_text.
Proof.
  intros [P c Q] V0.
  pose proof (proj1 (ilbv P c Q) V0) as V. clear V0.
  apply (ilb_cons_d _ P _ (spB c P)); [apply ilb_sp | auto |].
  intros o' HQ. exact (V o' HQ).
Qed.

Definition vILB_text : VLogic B Forward Plain Under :=
  @mkVLogic B Forward Plain Under ILB_text (fun t => iff_refl _)
    ilb_text_lsound ilb_text_complete.

End TextbookILBot.
