(** * Textbook Hoare logic with nontermination, primitive and complete

    The nontermination-aware Hoare logic (HL⊥) for the core language,
    with textbook rules as primitives:
    - one axiom per construct, sequencing, choice, consequence;
    - a *partial* loop rule: an invariant, with divergence allowed in the
      post ([HB_StarPartial]: [{I} c {I} ⟹ {I} c* {I ∨ ⊥}]);
    - a *total* loop rule with a variant into any well-founded order, only
      required to be well-founded on the invariant ([HB_StarTotal]).

    [hlb_text_complete]: the system is complete, under unbounded
    nondeterminism. Cousot warns that variants into the natural numbers
    are incomplete there; any well-founded order is enough. The proof
    derives the triple with the bottom-face wlp as precondition, by
    induction on the program. For a loop it splits on whether the post
    allows divergence:
    - if it does, the partial rule with the loop's wlp as invariant;
    - if not, the total rule with the variant "one more iteration of the
      body", which is well-founded on states from which the loop cannot
      diverge ([not_acc_div]).

    Completeness uses [classic], in that split and in building an
    infinite run from a state that is not well-founded. Soundness is
    constructive. *)

From Stdlib Require Import Classical.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Verified.
From LogicTransformers.Core Require Import Kernel KernelBot.

Section TextbookBot.

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

Lemma hlbv : forall P c Q, cvalid Forward Plain Over (kt P c Q) <->
    (forall o o', P o -> semKB c o o' -> Q o').
Proof. intros. simpl. unfold aimpl, img. firstorder. Qed.

(** ** The rules *)

Inductive hlb_text : @ruleset B :=
  | HB_Skip : forall P, hlb_text nop (kt P KSkip P)
  | HB_Act : forall Q a,
      hlb_text nop
        (kt (fun o => match o with
                      | Some s => forall s', act_sem a s s' -> Q (Some s')
                      | None => Q None end) (KAct a) Q)
  | HB_Assume : forall Q Bt,
      hlb_text nop
        (kt (fun o => match o with
                      | Some s => Bt s -> Q (Some s)
                      | None => Q None end) (KAssume Bt) Q)
  | HB_Seq : forall P R Q c1 c2,
      hlb_text (two (kt P c1 R) (kt R c2 Q)) (kt P (KSeq c1 c2) Q)
  | HB_Choice : forall P Q c1 c2,
      hlb_text (two (kt P c1 Q) (kt P c2 Q)) (kt P (KChoice c1 c2) Q)
  | HB_StarPartial : forall I c,
      hlb_text (one (kt I c I))
        (kt I (KStar c) (fun o => I o \/ o = None))
  | HB_StarTotal : forall (W : Type) (R : W -> W -> Prop) (mu : Σ -> W)
      (I : Σ -> Prop) c,
      (forall s, I s -> Acc R (mu s)) ->
      hlb_text (fun t => exists w,
                  t = kt (som (fun s => I s /\ mu s = w)) c
                         (som (fun s => I s /\ R (mu s) w)))
               (kt (som I) (KStar c) (som I))
  | HB_Cons : forall P P' Q Q' c,
      (forall o, P o -> P' o) -> (forall o, Q' o -> Q o) ->
      hlb_text (one (kt P' c Q')) (kt P c Q).

Definition HLB_text : @ProgramLogic B :=
  mkLogic (cvalid Forward Plain Over) (cvalid_proper _ _ _) hlb_text.

(** ** Soundness *)

Lemma star_inv : forall (I : Σ -> Prop) c,
    (forall s s', I s -> kev c s s' -> I s') ->
    forall s s', kev (KStar c) s s' -> I s -> I s'.
Proof.
  intros I c H s s' Hs. remember (KStar c) as k eqn:Ek.
  induction Hs; inversion Ek; subst; intros HI; [exact HI |].
  apply IHHs2; [reflexivity | eapply H; eassumption].
Qed.

Lemma star_total_no_div : forall (W : Type) (R : W -> W -> Prop) mu
    (I : Σ -> Prop) c,
    (forall w s o', I s -> mu s = w -> semKB c (Some s) o' ->
       som (fun s => I s /\ R (mu s) w) o') ->
    forall s, I s -> Acc R (mu s) -> ~ kdiv (KStar c) s.
Proof.
  intros W R mu I c H s HI Ha. remember (mu s) as w eqn:Ew.
  revert s HI Ew. induction Ha as [w _ IH]. intros s HI Ew Hd.
  inversion Hd; subst.
  - match goal with Hk : kdiv c ?x |- _ =>
      exact (H _ x None ltac:(assumption) eq_refl Hk) end.
  - match goal with Hk : kev c ?x ?s1, Hd1 : kdiv (KStar c) ?s1 |- _ =>
      destruct (H _ x (Some s1) ltac:(assumption) eq_refl Hk) as [HI1 HR];
      exact (IH (mu s1) HR s1 HI1 eq_refl Hd1) end.
Qed.

Theorem hlb_text_lsound : locally_sound HLB_text.
Proof.
  intros ps t HR Hps. simpl in *. destruct HR; apply hlbv.
  - intros o o' HP Hk. apply semKB_skip in Hk. subst. exact HP.
  - intros [s|] [s'|] HP Hk; apply semKB_act in Hk; simpl in *;
      try contradiction; auto.
  - intros [s|] [s'|] HP Hk; apply semKB_assume in Hk; simpl in *;
      try contradiction.
    + destruct Hk as [-> HB]. auto.
    + exact HP.
  - pose proof (proj1 (hlbv _ _ _) (Hps _ (or_introl eq_refl))) as H1.
    pose proof (proj1 (hlbv _ _ _) (Hps _ (or_intror eq_refl))) as H2.
    intros o o'' HP Hk. apply semKB_seq in Hk as [o' [Ha Hb]]. eauto.
  - pose proof (proj1 (hlbv _ _ _) (Hps _ (or_introl eq_refl))) as H1.
    pose proof (proj1 (hlbv _ _ _) (Hps _ (or_intror eq_refl))) as H2.
    intros o o' HP Hk. apply semKB_choice in Hk as [Hk | Hk]; eauto.
  - pose proof (proj1 (hlbv _ _ _) (Hps _ eq_refl)) as H1.
    intros [s|] [s'|] HI Hk; simpl in Hk; try contradiction; auto.
    left. refine (star_inv (fun x => I (Some x)) c _ s s' Hk HI).
    intros x x' Hx Hc. exact (H1 (Some x) (Some x') Hx Hc).
  - assert (Hprem : forall w s o', I s -> mu s = w -> semKB c (Some s) o' ->
                    som (fun s => I s /\ R (mu s) w) o').
    { intros w s o' HI Ew Hk.
      apply (proj1 (hlbv _ _ _) (Hps _ (ex_intro _ w eq_refl)) (Some s) o');
        [simpl; auto | exact Hk]. }
    intros [s|] [s'|] HI Hk; simpl in *; try contradiction.
    + refine (star_inv I c _ s s' Hk HI).
      intros x x' Hx Hc. exact (proj1 (Hprem _ x (Some x') Hx eq_refl Hc)).
    + exact (star_total_no_div W R mu I c Hprem s HI (H s HI) Hk).
  - pose proof (proj1 (hlbv _ _ _) (Hps _ eq_refl)) as H1. eauto.
Qed.

(** ** Completeness *)

Definition wlpB (c : com) (Q : option Σ -> Prop) : option Σ -> Prop :=
  fun o => forall o', semKB c o o' -> Q o'.

Lemma hlb_cons_d : forall P P' Q Q' c,
    derivable hlb_text (kt P' c Q') ->
    (forall o, P o -> P' o) -> (forall o, Q' o -> Q o) ->
    derivable hlb_text (kt P c Q).
Proof.
  intros P P' Q Q' c D HP HQ.
  apply (D_Rule _ (one (kt P' c Q'))); [apply HB_Cons; assumption |].
  intros t ->. exact D.
Qed.

Lemma semKB_refl_star : forall c o, semKB (KStar c) o o.
Proof. intros c [s|]; simpl; [apply KE_StarRefl | exact I]. Qed.

Lemma semKB_star_step : forall c o o1 o',
    semKB c o o1 -> semKB (KStar c) o1 o' -> semKB (KStar c) o o'.
Proof.
  intros c [s|] [s1|] [s'|] H1 H2; simpl in *; try contradiction; auto.
  - eapply KE_StarStep; eassumption.
  - eapply KD_StarIter; eassumption.
  - apply KD_StarBody. exact H1.
Qed.

(** From a state that is not well-founded for "one more iteration", the
    loop can run forever. *)
Lemma not_acc_div : forall c (I : Σ -> Prop) s,
    ~ Acc (fun s1 s0 => kev c s0 s1 /\ I s0) s -> I s ->
    kdiv (KStar c) s.
Proof.
  intros c I. cofix CH. intros s Hn HI.
  assert (Hx : exists s1, (kev c s s1 /\ I s) /\
                          ~ Acc (fun s1 s0 => kev c s0 s1 /\ I s0) s1).
  { apply NNPP. intros Hno. apply Hn. constructor. intros y Hy.
    apply NNPP. intros Hy'. apply Hno. exists y. auto. }
  destruct Hx as [s1 [[Hk _] Hn1]].
  assert (HI1 : I s1 \/ ~ I s1) by apply classic.
  destruct HI1 as [HI1 | HI1].
  - exact (KD_StarIter act_sem c s s1 Hk (CH s1 Hn1 HI1)).
  - exfalso. apply Hn1. constructor. intros y [_ Hy]. contradiction.
Qed.

Lemma hlb_wlp : forall c Q, derivable hlb_text (kt (wlpB c Q) c Q).
Proof.
  induction c; intros Q.
  - apply (hlb_cons_d _ Q _ Q); [| | auto].
    + apply (D_Rule _ nop); [apply HB_Skip | intros t []].
    + intros o H. apply H, semKB_skip. reflexivity.
  - apply (hlb_cons_d _ (fun o => match o with
             | Some s => forall s', act_sem a s s' -> Q (Some s')
             | None => Q None end) _ Q); [| | auto].
    + apply (D_Rule _ nop); [apply HB_Act | intros t []].
    + intros [s|] H; [intros s' Ha; apply H, semKB_act, Ha |].
      apply H, semKB_none. reflexivity.
  - apply (hlb_cons_d _ (fun o => match o with
             | Some s => B s -> Q (Some s)
             | None => Q None end) _ Q); [| | auto].
    + apply (D_Rule _ nop); [apply HB_Assume | intros t []].
    + intros [s|] H; [intros HB; apply H, semKB_assume; auto |].
      apply H, semKB_none. reflexivity.
  - apply (hlb_cons_d _ (wlpB c1 (wlpB c2 Q)) _ Q); [| | auto].
    + apply (D_Rule _ (two (kt (wlpB c1 (wlpB c2 Q)) c1 (wlpB c2 Q))
                           (kt (wlpB c2 Q) c2 Q)));
        [apply HB_Seq | intros t [-> | ->]; auto].
    + intros o H o1 H1 o2 H2. apply H, semKB_seq. eauto.
  - apply (D_Rule _ (two (kt (wlpB (KChoice c1 c2) Q) c1 Q)
                         (kt (wlpB (KChoice c1 c2) Q) c2 Q)));
      [apply HB_Choice |].
    intros t [-> | ->].
    + apply (hlb_cons_d _ (wlpB c1 Q) _ Q); [apply IHc1 | | auto].
      intros o H o' Hk. apply H, semKB_choice. auto.
    + apply (hlb_cons_d _ (wlpB c2 Q) _ Q); [apply IHc2 | | auto].
      intros o H o' Hk. apply H, semKB_choice. auto.
  - set (I := wlpB (KStar c) Q).
    assert (Hstep : forall o, I o -> wlpB c I o).
    { intros o HI o1 H1 o' H2. apply HI. eapply semKB_star_step; eassumption. }
    destruct (classic (Q None)) as [HQn | HQn].
    + (* the post allows divergence: the partial rule *)
      apply (hlb_cons_d _ I _ (fun o => I o \/ o = None)); [| auto |].
      * apply (D_Rule _ (one (kt I c I))); [apply HB_StarPartial |].
        intros t ->. apply (hlb_cons_d _ (wlpB c I) _ I); [apply IHc | | auto].
        exact Hstep.
      * intros o [HI | ->]; [apply HI, semKB_refl_star | exact HQn].
    + (* it doesn't: the total rule, variant "one more iteration" *)
      set (I' := fun s => I (Some s)).
      set (Rv := fun s1 s0 => kev c s0 s1 /\ I' s0).
      apply (hlb_cons_d _ (som I') _ (som I')).
      * apply (D_Rule _ (fun t => exists w,
                  t = kt (som (fun s => I' s /\ id s = w)) c
                         (som (fun s => I' s /\ Rv (id s) w))));
          [apply (HB_StarTotal Σ Rv id I' c) |].
        -- intros s HI. apply NNPP. intros Hn.
           apply HQn. apply HI. exact (not_acc_div c I' s Hn HI).
        -- intros t [w ->].
           apply (hlb_cons_d _ (wlpB c (som (fun s => I' s /\ Rv (id s) w)))
                    _ (som (fun s => I' s /\ Rv (id s) w)));
             [apply IHc | | auto].
           intros [s|] H; simpl in H; [| contradiction].
           destruct H as [HI Ew]. unfold id in Ew. subst w.
           intros [s1|] Hk; simpl.
           ++ split; [exact (Hstep (Some s) HI (Some s1) Hk) |].
              split; [exact Hk | exact HI].
           ++ apply HQn. apply HI. apply KD_StarBody. exact Hk.
      * intros [s|] HI; [exact HI |]. apply HQn, HI, semKB_none. reflexivity.
      * intros [s|] HI; simpl in HI;
          [apply HI, semKB_refl_star | contradiction].
Qed.

Theorem hlb_text_complete : complete HLB_text.
Proof.
  intros [P c Q] V0.
  pose proof (proj1 (hlbv P c Q) V0) as V. clear V0.
  apply (hlb_cons_d _ (wlpB c Q) _ Q); [apply hlb_wlp | | auto].
  intros o HP o' Hk. exact (V o o' HP Hk).
Qed.

Definition vHLB_text : VLogic B Forward Plain Over :=
  @mkVLogic B Forward Plain Over HLB_text (fun t => iff_refl _)
    hlb_text_lsound hlb_text_complete.

End TextbookBot.
