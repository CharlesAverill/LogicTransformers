(** * Rely/guarantee with auxiliary variables

    [RGIncomplete] shows Jones's rules cannot prove
    [{x = 0} x := x+1 ∥ x := x+1 {x = 2}]. The classical remedy is
    auxiliary (ghost) variables, updated atomically with real ones. This
    file adds them:

    - [rgx]: Jones's rules plus a rule for the atomic multiple
      assignment [PMulti] ([rgx_sound]);
    - [erase A c]: [c] with its assignments to the ghost variables [A]
      removed; a multiple assignment left with one real assignment
      becomes that assignment;
    - [aux_ok A c]: ghosts never flow into real variables or guards
      (stated semantically: those expressions agree on states that agree
      off [A]);
    - [aux_rule]: a closed rely/guarantee proof of [c] whose ghost-free
      start states cover [P], with a postcondition that does not read
      ghosts, gives a valid Hoare triple for [erase A c]. Every run of
      the erased program is matched by a run of [c] ([erase_runs]).
    - [inc2_by_ghosts]: the counterexample, proved compositionally: each
      thread sets its own ghost in the same atomic step as its
      increment, and the parallel rule's conjunction gives [x = 2].

    The classical completeness theorem (every valid triple has such a
    proof, with history ghosts) is not mechanized here. Axiom-free. *)

From Stdlib Require Import String Arith Lia List Bool.
From LogicTransformers.Imp Require Import Syntax.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Relational.
From LogicTransformers.Core Require Import Kernel SmallStepCore.
From LogicTransformers.ParImp Require Import
  ParImp RelyGuarantee RGIncomplete.
Import ListNotations.

(** ** Jones's rules with atomic multiple assignment *)

Lemma rg_multi_sound : forall R G (P Q : state -> Prop) l,
    stable R P -> stable R Q ->
    (forall s, P s -> Q (massign l s) /\ G s (massign l s)) ->
    rg_valid R G P (PMulti l) Q.
Proof.
  intros R G P Q l HP HQ Hs s0 k H0 Hr.
  assert (Hk : (fst k = PMulti l /\ P (snd k)) \/
               (fst k = PSkip /\ Q (snd k))).
  { induction Hr as [| k k' _ IH Hst | c s s' _ IH HR].
    - left. auto.
    - destruct k as [c s]. destruct IH as [[E Hp] | [E Hq]]; simpl in E;
        subst c; inversion Hst; subst.
      right. split; [reflexivity | exact (proj1 (Hs s Hp))].
    - destruct IH as [[E Hp] | [E Hq]]; [left | right]; simpl in *;
        split; try exact E; eauto. }
  destruct k as [c s]. simpl in *.
  destruct Hk as [[E Hp] | [E Hq]]; subst c.
  - split; [| discriminate]. intros k' Hst. inversion Hst; subst.
    exact (proj2 (Hs s Hp)).
  - split; [intros k' Hst; inversion Hst | intros _; exact Hq].
Qed.

Inductive rgx : srel -> srel -> (state -> Prop) -> pcom ->
                (state -> Prop) -> Prop :=
  | RGX_Skip : forall R G P, stable R P -> rgx R G P PSkip P
  | RGX_Asgn : forall R G (P Q : state -> Prop) x a,
      stable R P -> stable R Q ->
      (forall s, P s ->
         Q (update s x (aeval s a)) /\ G s (update s x (aeval s a))) ->
      rgx R G P (PAsgn x a) Q
  | RGX_Multi : forall R G (P Q : state -> Prop) l,
      stable R P -> stable R Q ->
      (forall s, P s -> Q (massign l s) /\ G s (massign l s)) ->
      rgx R G P (PMulti l) Q
  | RGX_Seq : forall R G P M Q c1 c2,
      (forall s, G s s) -> rgx R G P c1 M -> rgx R G M c2 Q ->
      rgx R G P (PSeq c1 c2) Q
  | RGX_If : forall R G P Q b c1 c2,
      (forall s, G s s) -> stable R P ->
      rgx R G (fun s => P s /\ beval s b = true) c1 Q ->
      rgx R G (fun s => P s /\ beval s b = false) c2 Q ->
      rgx R G P (PIf b c1 c2) Q
  | RGX_While : forall R G (I : state -> Prop) b c,
      (forall s, G s s) -> stable R I ->
      stable R (fun s => I s /\ beval s b = false) ->
      rgx R G (fun s => I s /\ beval s b = true) c I ->
      rgx R G I (PWhile b c) (fun s => I s /\ beval s b = false)
  | RGX_Par : forall R G R1 G1 R2 G2 P1 P2 Q1 Q2 c1 c2,
      (forall s, G s s) ->
      (forall s s', R s s' \/ G2 s s' -> R1 s s') ->
      (forall s s', R s s' \/ G1 s s' -> R2 s s') ->
      (forall s s', G1 s s' \/ G2 s s' -> G s s') ->
      rgx R1 G1 P1 c1 Q1 -> rgx R2 G2 P2 c2 Q2 ->
      rgx R G (fun s => P1 s /\ P2 s) (PPar c1 c2) (fun s => Q1 s /\ Q2 s)
  | RGX_Cons : forall R R' G G' P P' Q Q' c,
      (forall s, P s -> P' s) -> (forall s s', R s s' -> R' s s') ->
      (forall s s', G' s s' -> G s s') -> (forall s, Q' s -> Q s) ->
      rgx R' G' P' c Q' -> rgx R G P c Q.

Theorem rgx_sound : forall R G P c Q, rgx R G P c Q -> rg_valid R G P c Q.
Proof.
  intros R G P c Q H. induction H.
  - apply rg_skip_sound; assumption.
  - apply rg_asgn_sound; assumption.
  - apply rg_multi_sound; assumption.
  - eapply rg_seq_sound; eassumption.
  - apply rg_if_sound; assumption.
  - apply rg_while_sound; assumption.
  - apply (rg_par_sound R G R1 G1 R2 G2 P1 P2 Q1 Q2 c1 c2); assumption.
  - eapply rg_cons_sound; eassumption.
Qed.

(** ** Ghosts and erasure *)

Section Aux.

Variable A : var -> bool.

Definition agree (s t : state) : Prop := forall y, A y = false -> s y = t y.

Definition aindep (a : aexp) : Prop :=
  forall s t, agree s t -> aeval s a = aeval t a.
Definition bindep (b : bexp) : Prop :=
  forall s t, agree s t -> beval s b = beval t b.

Fixpoint multi_ok (l : list (var * aexp)) : Prop :=
  match l with
  | [] => True
  | (x, a) :: l => (A x = false -> aindep a) /\ multi_ok l
  end.

Fixpoint aux_ok (c : pcom) : Prop :=
  match c with
  | PSkip => True
  | PAsgn x a => A x = false /\ aindep a
  | PSeq c1 c2 | PPar c1 c2 => aux_ok c1 /\ aux_ok c2
  | PIf b c1 c2 => bindep b /\ aux_ok c1 /\ aux_ok c2
  | PWhile b c => bindep b /\ aux_ok c
  | PMulti l => multi_ok l
  end.

Definition real (l : list (var * aexp)) : list (var * aexp) :=
  filter (fun xa => negb (A (fst xa))) l.

Definition erase_multi (l : list (var * aexp)) : pcom :=
  match real l with
  | [(x, a)] => PAsgn x a
  | l' => PMulti l'
  end.

Fixpoint erase (c : pcom) : pcom :=
  match c with
  | PSkip => PSkip
  | PAsgn x a => PAsgn x a
  | PSeq c1 c2 => PSeq (erase c1) (erase c2)
  | PIf b c1 c2 => PIf b (erase c1) (erase c2)
  | PWhile b c => PWhile b (erase c)
  | PPar c1 c2 => PPar (erase c1) (erase c2)
  | PMulti l => erase_multi l
  end.

Lemma erase_skip : forall c, erase c = PSkip -> c = PSkip.
Proof.
  intros [] E; simpl in E; try discriminate; [reflexivity |].
  unfold erase_multi in E. destruct (real l) as [| [x a] [|]]; discriminate.
Qed.

Lemma agree_update : forall s t x v, agree s t ->
    agree (update s x v) (update t x v).
Proof.
  intros s t x v H y Hy. unfold update.
  destruct (String.eqb x y); [reflexivity | apply H, Hy].
Qed.

Lemma agree_ghost : forall s t x v, A x = true -> agree s t ->
    agree s (update t x v).
Proof.
  intros s t x v Hx H y Hy. unfold update.
  destruct (String.eqb_spec x y); [subst; congruence | apply H, Hy].
Qed.

Lemma massign_agree : forall l s t, multi_ok l -> agree s t ->
    agree (massign (real l) s) (massign l t).
Proof.
  induction l as [| [x a] l IH]; intros s t Hok H; [exact H |].
  destruct Hok as [Ha Hl]. unfold real. simpl. destruct (A x) eqn:Ex; simpl.
  - apply IH; [exact Hl | apply agree_ghost; assumption].
  - rewrite (Ha eq_refl s t H). apply IH; [exact Hl | apply agree_update, H].
Qed.

Lemma erase_multi_step : forall l s d s',
    pstep (erase_multi l, s) (d, s') ->
    d = PSkip /\ s' = massign (real l) s.
Proof.
  intros l s d s' H. unfold erase_multi in H.
  destruct (real l) as [| [x a] [| y l']] eqn:E; inversion H; subst;
    split; reflexivity.
Qed.

Lemma aux_ok_step : forall c t c' t', aux_ok c ->
    pstep (c, t) (c', t') -> aux_ok c'.
Proof.
  intros c t c' t' Hok H.
  remember (c, t) as k eqn:Ek. remember (c', t') as k' eqn:Ek'.
  revert c t c' t' Ek Ek' Hok.
  induction H; intros c0 t0 c0' t0' Ek Ek' Hok;
    injection Ek; injection Ek'; intros; subst; simpl in *;
    try exact I; try tauto.
  all: first [ split; [eapply IHpstep; eauto; tauto | tauto]
             | split; [tauto | eapply IHpstep; eauto; tauto]
             | repeat split; tauto ].
Qed.

(** One step of the erased program is matched by one step of [c]. *)
Lemma erase_step : forall c, aux_ok c ->
    forall d s s' t, pstep (erase c, s) (d, s') -> agree s t ->
    exists c' t', pstep (c, t) (c', t') /\ erase c' = d /\ agree s' t'.
Proof.
  induction c as [| x a | c1 IH1 c2 IH2 | b c1 IH1 c2 IH2 | b c IH
                  | c1 IH1 c2 IH2 | l]; intros Hok d s s' t H Hag;
    simpl in *.
  - inversion H.
  - inversion H; subst. destruct Hok as [Hx Ha].
    exists PSkip, (update t x (aeval t a)). split; [apply PS_Asgn |].
    split; [reflexivity |]. rewrite (Ha s t Hag). apply agree_update, Hag.
  - destruct Hok as [Ok1 Ok2]. inversion H; subst.
    + symmetry in H1. apply erase_skip in H1. subst c1.
      exists c2, t. split; [apply PS_SeqSkip | auto].
    + match goal with K : pstep (erase c1, _) _ |- _ =>
        destruct (IH1 Ok1 _ _ _ t K Hag) as [c1' [t' [Hs [E Ha]]]] end.
      exists (PSeq c1' c2), t'. split; [apply PS_Seq, Hs |].
      simpl. rewrite E. auto.
  - destruct Hok as [Hb [Ok1 Ok2]]. inversion H; subst.
    + exists c1, t. split; [apply PS_IfT; rewrite <- (Hb _ t Hag); auto
                           | auto].
    + exists c2, t. split; [apply PS_IfF; rewrite <- (Hb _ t Hag); auto
                           | auto].
  - inversion H; subst.
    exists (PIf b (PSeq c (PWhile b c)) PSkip), t.
    split; [apply PS_While | auto].
  - destruct Hok as [Ok1 Ok2]. inversion H; subst.
    + match goal with K : pstep (erase c1, _) _ |- _ =>
        destruct (IH1 Ok1 _ _ _ t K Hag) as [c1' [t' [Hs [E Ha]]]] end.
      exists (PPar c1' c2), t'. split; [apply PS_ParL, Hs |].
      simpl. rewrite E. auto.
    + match goal with K : pstep (erase c2, _) _ |- _ =>
        destruct (IH2 Ok2 _ _ _ t K Hag) as [c2' [t' [Hs [E Ha]]]] end.
      exists (PPar c1 c2'), t'. split; [apply PS_ParR, Hs |].
      simpl. rewrite E. auto.
    + symmetry in H1, H2. apply erase_skip in H1, H2. subst.
      exists PSkip, t. split; [apply PS_ParDone | auto].
  - apply erase_multi_step in H. destruct H as [-> ->].
    exists PSkip, (massign l t). split; [apply PS_Multi |].
    split; [reflexivity | apply massign_agree; assumption].
Qed.

Theorem erase_runs : forall c s s' t, aux_ok c -> agree s t ->
    smulti pstep (erase c, s) (PSkip, s') ->
    exists t', smulti pstep (c, t) (PSkip, t') /\ agree s' t'.
Proof.
  intros c s s' t Hok Hag H.
  remember (erase c, s) as k eqn:Ek. remember (PSkip, s') as k' eqn:Ek'.
  revert c s t Ek Hok Hag.
  induction H as [k | k [d s1] k2 Hs _ IH]; intros c s t Ek Hok Hag.
  - rewrite Ek in Ek'. injection Ek'. intros E1 E2. subst.
    apply erase_skip in E2. subst.
    exists t. split; [apply SM_Refl | exact Hag].
  - subst k. destruct (erase_step c Hok d s s1 t Hs Hag)
      as [c' [t1 [Hs' [E Ha]]]].
    subst d.
    destruct (IH Ek' c' s1 t1 eq_refl (aux_ok_step _ _ _ _ Hok Hs') Ha)
      as [t' [Hm Ha']].
    exists t'. split; [eapply SM_Step; eassumption | exact Ha'].
Qed.

Definition qindep (Q : state -> Prop) : Prop :=
  forall s t, agree s t -> Q t -> Q s.

Theorem aux_rule : forall G (P P' Q : state -> Prop) c,
    (forall s, P s -> exists t, agree s t /\ P' t) ->
    rgx (fun _ _ => False) G P' c Q -> aux_ok c -> qindep Q ->
    cvalid Forward Plain Over (@mkTriple ParImp P (erase c) Q).
Proof.
  intros G P P' Q c Hinit D Hok Hq. apply rgx_sound in D.
  apply cvalid_cvr. simpl. intros s s' HP Hr.
  destruct (Hinit s HP) as [t [Hag HP']].
  destruct (erase_runs c s s' t Hok Hag Hr) as [t' [Hm Ha']].
  apply (Hq s' t' Ha').
  exact (proj2 (D t (PSkip, t') HP' (smulti_reach _ _ _ _ (RRefl _ _) Hm))
               eq_refl).
Qed.

End Aux.

(** ** The counterexample, with ghosts *)

Local Open Scope string_scope.
Local Notation X := "x".
Local Notation D1 := "d1".
Local Notation D2 := "d2".

Definition ghost (y : var) : bool := String.eqb y D1 || String.eqb y D2.

Definition incg (d : var) : pcom :=
  PMulti [(X, APlus (AVar X) (ANum 1)); (d, ANum 1)].
Definition inc2g : pcom := PPar (incg D1) (incg D2).

Lemma erase_inc2g : erase ghost inc2g = inc2.
Proof. reflexivity. Qed.

(** The invariant shared by both threads, and what each may do. *)
Definition J (s : state) : Prop := s X = s D1 + s D2.
Definition keeps (d : var) : srel := fun s s' => J s -> J s' /\ s' d = s d.

Ltac upd := simpl in *; unfold J, keeps in *;
  repeat (rewrite ?update_eq; rewrite ?update_neq by discriminate).

Lemma thread1 :
  rgx (keeps D1) (keeps D2) (fun s => J s /\ s D1 = 0) (incg D1)
      (fun s => J s /\ s D1 = 1).
Proof.
  apply RGX_Multi.
  - intros s s' [HJ H0] HR. destruct (HR HJ) as [HJ' E]. split; congruence.
  - intros s s' [HJ H0] HR. destruct (HR HJ) as [HJ' E]. split; congruence.
  - intros s [HJ H0]. upd. repeat split; intros; upd; lia.
Qed.

Lemma thread2 :
  rgx (keeps D2) (keeps D1) (fun s => J s /\ s D2 = 0) (incg D2)
      (fun s => J s /\ s D2 = 1).
Proof.
  apply RGX_Multi.
  - intros s s' [HJ H0] HR. destruct (HR HJ) as [HJ' E]. split; congruence.
  - intros s s' [HJ H0] HR. destruct (HR HJ) as [HJ' E]. split; congruence.
  - intros s [HJ H0]. upd. repeat split; intros; upd; lia.
Qed.

(** The whole program, by the parallel rule: the conjunction of the
    threads' postconditions now implies [x = 2]. *)
Lemma inc2g_rg :
  rgx (fun _ _ => False) (fun _ _ => True)
    (fun s => J s /\ s D1 = 0 /\ s D2 = 0) inc2g (fun s => s X = 2).
Proof.
  eapply RGX_Cons; [| | | |
    apply (RGX_Par (fun _ _ => False) (fun _ _ => True)
             (keeps D1) (keeps D2) (keeps D2) (keeps D1));
    [| | | | exact thread1 | exact thread2]].
  - intros s [HJ [H1 H2]]. split; split; assumption.
  - auto.
  - auto.
  - intros s [[HJ H1] [_ H2]]. unfold J in HJ. lia.
  - auto.
  - intros s s' [[] | H]; exact H.
  - intros s s' [[] | H]; exact H.
  - auto.
Qed.

Lemma inc2g_aux_ok : aux_ok ghost inc2g.
Proof.
  simpl. repeat split; try (intros; exact I).
  - intros _ s t H. simpl. rewrite (H X eq_refl). reflexivity.
  - intros _ s t H. simpl. rewrite (H X eq_refl). reflexivity.
Qed.

(** [x := x+1 ∥ x := x+1] from [x = 0] ends in [x = 2], proved with
    Jones's rules and two ghost variables, against [inc2_not_rg]. *)
Theorem inc2_by_ghosts :
  cvalid Forward Plain Over
    (@mkTriple ParImp (fun s => s X = 0) inc2 (fun s => s X = 2)).
Proof.
  rewrite <- erase_inc2g.
  apply (aux_rule ghost (fun _ _ => True) _
           (fun s => J s /\ s D1 = 0 /\ s D2 = 0)).
  - intros s Hs. exists (update (update s D1 0) D2 0). split.
    + intros y Hy. unfold update. unfold ghost in Hy.
      apply orb_false_iff in Hy. destruct Hy as [H1 H2].
      rewrite String.eqb_sym in H1, H2. rewrite H1, H2. reflexivity.
    + upd. lia.
  - exact inc2g_rg.
  - exact inc2g_aux_ok.
  - intros s t H Ht. rewrite (H X eq_refl). exact Ht.
Qed.
