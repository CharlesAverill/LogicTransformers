(** * Textbook proof systems, primitive and complete

    The generated logics ([Core.Generate]) are complete because their
    rules are exact: each rule's conclusion is the precise image or
    preimage of its precondition or postcondition. This file shows that
    completeness does not depend on that. Here the familiar rules are the
    *primitive* rules of a logic, with an arbitrary consequence rule, and
    each system is proved sound and complete on its own, for the core
    language with any atomic actions:

    - [hl_text], Hoare logic: one axiom per construct, sequencing, choice,
      the *finitary* invariant rule [{I} c {I} ⟹ {I} c* {I}], consequence;
    - [nc_text], necessary conditions: the same shape backwards, with a
      backward invariant rule [{I} c {I} ⟹ {I} c* {I}];
    - [il_text], incorrectness logic: O'Hearn's rules, including the
      iteration-indexed loop rule [∀n ⟦X n⟧ c ⟦X (n+1)⟧ ⟹
      ⟦X 0⟧ c* ⟦∃n. X n⟧], left and right choice, and disjunction;
    - [sil_text], sufficient incorrectness: the backward counterpart, with
      a descending variant [∀n {X (n+1)} c {X n} ⟹ {∃n. X n} c* {X 0}].

    Completeness is relative in Cook's sense, with assertions as Rocq
    predicates. The proofs follow the textbook argument: derive the triple
    whose precondition or postcondition is the exact transformer, by
    induction on the program, then weaken with consequence. For HL the
    loop invariant is the weakest liberal precondition of the whole loop;
    for NC, the preimage of the whole loop. The IL and SIL loop rules
    keep their premise per iteration count: that is the loop rule as it
    appears in the literature, and under-approximate completeness needs
    it.

    Each system is packaged as a verified record ([vHL_text], [vIL_text],
    [vNC_text], [vSIL_text]), so it can be the source of any transformer
    ([IL_from_textbook]). The four systems and their soundness and
    completeness proofs are axiom-free. *)

From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Verified.
From LogicTransformers.Core Require Import Kernel VCore.

Section Textbook.

Context {Σ Act : Type} (act_sem : Act -> Σ -> Σ -> Prop).

Notation T := (KLang act_sem).
Notation kev := (kev act_sem).
Notation com := (kcom Σ Act).
Notation kt P c Q := (@mkTriple T P c Q).

Definition nop : @triple T -> Prop := fun _ => False.
Definition one (t1 : @triple T) : @triple T -> Prop := fun t => t = t1.
Definition two (t1 t2 : @triple T) : @triple T -> Prop :=
  fun t => t = t1 \/ t = t2.

(** The four validity notions, unfolded. *)
Lemma hlv : forall P c Q, cvalid Forward Plain Over (kt P c Q) <->
    (forall s s', P s -> kev c s s' -> Q s').
Proof. intros. simpl. unfold aimpl, img. firstorder. Qed.

Lemma ilv : forall P c Q, cvalid Forward Plain Under (kt P c Q) <->
    (forall s', Q s' -> exists s, P s /\ kev c s s').
Proof. intros. simpl. unfold aimpl, img. firstorder. Qed.

Lemma ncv : forall P c Q, cvalid Backward Plain Over (kt P c Q) <->
    (forall s s', kev c s s' -> Q s' -> P s).
Proof. intros. simpl. unfold aimpl, preimg. firstorder. Qed.

Lemma silv : forall P c Q, cvalid Backward Plain Under (kt P c Q) <->
    (forall s, P s -> exists s', kev c s s' /\ Q s').
Proof. intros. simpl. unfold aimpl, preimg. firstorder. Qed.

(** Exact transformers on core programs. *)
Definition kwlp (c : com) (Q : Σ -> Prop) : Σ -> Prop :=
  fun s => forall s', kev c s s' -> Q s'.
Definition ksp (c : com) (P : Σ -> Prop) : Σ -> Prop :=
  fun s' => exists s, P s /\ kev c s s'.
Definition kpre (c : com) (Q : Σ -> Prop) : Σ -> Prop :=
  fun s => exists s', kev c s s' /\ Q s'.

Ltac kinv H := inversion H; subst; clear H.

(** ** Hoare logic *)

Inductive hl_text : @ruleset T :=
  | HT_Skip : forall P, hl_text nop (kt P KSkip P)
  | HT_Act : forall Q a,
      hl_text nop (kt (fun s => forall s', act_sem a s s' -> Q s') (KAct a) Q)
  | HT_Assume : forall Q B,
      hl_text nop (kt (fun s => B s -> Q s) (KAssume B) Q)
  | HT_Seq : forall P R Q c1 c2,
      hl_text (two (kt P c1 R) (kt R c2 Q)) (kt P (KSeq c1 c2) Q)
  | HT_Choice : forall P Q c1 c2,
      hl_text (two (kt P c1 Q) (kt P c2 Q)) (kt P (KChoice c1 c2) Q)
  | HT_Star : forall I c, hl_text (one (kt I c I)) (kt I (KStar c) I)
  | HT_Cons : forall P P' Q Q' c,
      (forall s, P s -> P' s) -> (forall s, Q' s -> Q s) ->
      hl_text (one (kt P' c Q')) (kt P c Q).

Definition HL_text : @ProgramLogic T :=
  mkLogic (cvalid Forward Plain Over) (cvalid_proper _ _ _) hl_text.

Lemma hl_star_inv : forall (I : Σ -> Prop) c,
    (forall s s', I s -> kev c s s' -> I s') ->
    forall s s', kev (KStar c) s s' -> I s -> I s'.
Proof.
  intros I c H s s' Hs. remember (KStar c) as k eqn:Ek.
  induction Hs; inversion Ek; subst; intros HI; [exact HI |].
  apply IHHs2; [reflexivity | eapply H; eassumption].
Qed.

Theorem hl_text_lsound : locally_sound HL_text.
Proof.
  intros ps t HR Hps. simpl in *. destruct HR; apply hlv.
  - intros s s' HP Hk. kinv Hk. exact HP.
  - intros s s' HP Hk. kinv Hk. auto.
  - intros s s' HP Hk. kinv Hk. auto.
  - pose proof (proj1 (hlv _ _ _) (Hps _ (or_introl eq_refl))) as H1.
    pose proof (proj1 (hlv _ _ _) (Hps _ (or_intror eq_refl))) as H2.
    intros s s' HP Hk. kinv Hk. eauto.
  - pose proof (proj1 (hlv _ _ _) (Hps _ (or_introl eq_refl))) as H1.
    pose proof (proj1 (hlv _ _ _) (Hps _ (or_intror eq_refl))) as H2.
    intros s s' HP Hk. kinv Hk; eauto.
  - pose proof (proj1 (hlv _ _ _) (Hps _ eq_refl)) as H1.
    intros s s' HI Hk. exact (hl_star_inv I c H1 s s' Hk HI).
  - pose proof (proj1 (hlv _ _ _) (Hps _ eq_refl)) as H1. eauto.
Qed.

Lemma hl_cons_d : forall P P' Q Q' c,
    derivable hl_text (kt P' c Q') ->
    (forall s, P s -> P' s) -> (forall s, Q' s -> Q s) ->
    derivable hl_text (kt P c Q).
Proof.
  intros P P' Q Q' c D HP HQ.
  apply (D_Rule _ (one (kt P' c Q'))); [apply HT_Cons; assumption |].
  intros t ->. exact D.
Qed.

Lemma hl_wlp : forall c Q, derivable hl_text (kt (kwlp c Q) c Q).
Proof.
  induction c; intros Q.
  - apply (hl_cons_d _ Q _ Q); [| | auto].
    + apply (D_Rule _ nop); [apply HT_Skip | intros t []].
    + intros s H. apply H, KE_Skip.
  - apply (hl_cons_d _ (fun s => forall s', act_sem a s s' -> Q s') _ Q);
      [| | auto].
    + apply (D_Rule _ nop); [apply HT_Act | intros t []].
    + intros s H s' Ha. apply H, KE_Act, Ha.
  - apply (hl_cons_d _ (fun s => B s -> Q s) _ Q); [| | auto].
    + apply (D_Rule _ nop); [apply HT_Assume | intros t []].
    + intros s H HB. apply H, KE_Assume, HB.
  - apply (hl_cons_d _ (kwlp c1 (kwlp c2 Q)) _ Q); [| | auto].
    + apply (D_Rule _ (two (kt (kwlp c1 (kwlp c2 Q)) c1 (kwlp c2 Q))
                           (kt (kwlp c2 Q) c2 Q)));
        [apply HT_Seq | intros t [-> | ->]; auto].
    + intros s H s1 H1 s2 H2. apply H. eapply KE_Seq; eassumption.
  - apply (D_Rule _ (two (kt (kwlp (KChoice c1 c2) Q) c1 Q)
                         (kt (kwlp (KChoice c1 c2) Q) c2 Q)));
      [apply HT_Choice |].
    intros t [-> | ->].
    + apply (hl_cons_d _ (kwlp c1 Q) _ Q); [apply IHc1 | | auto].
      intros s H s' Hk. apply H, KE_ChoiceL, Hk.
    + apply (hl_cons_d _ (kwlp c2 Q) _ Q); [apply IHc2 | | auto].
      intros s H s' Hk. apply H, KE_ChoiceR, Hk.
  - set (I := kwlp (KStar c) Q).
    apply (hl_cons_d _ I _ I);
      [| auto | intros s H; exact (H s (KE_StarRefl _ _ s))].
    apply (D_Rule _ (one (kt I c I))); [apply HT_Star |]. intros t ->.
    apply (hl_cons_d _ (kwlp c I) _ I); [apply IHc | | auto].
    intros s H s1 H1 s2 H2. apply H. eapply KE_StarStep; eassumption.
Qed.

Theorem hl_text_complete : complete HL_text.
Proof.
  intros [P c Q] V0.
  pose proof (proj1 (hlv P c Q) V0) as V. clear V0.
  apply (hl_cons_d _ (kwlp c Q) _ Q); [apply hl_wlp | | auto].
  intros s HP s' Hk. exact (V s s' HP Hk).
Qed.

Definition vHL_text : VLogic T Forward Plain Over :=
  @mkVLogic T Forward Plain Over HL_text (fun t => iff_refl _)
    hl_text_lsound hl_text_complete.

(** ** Necessary conditions *)

Inductive nc_text : @ruleset T :=
  | NT_Skip : forall Q, nc_text nop (kt Q KSkip Q)
  | NT_Act : forall Q a,
      nc_text nop (kt (fun s => exists s', act_sem a s s' /\ Q s') (KAct a) Q)
  | NT_Assume : forall Q B,
      nc_text nop (kt (fun s => B s /\ Q s) (KAssume B) Q)
  | NT_Seq : forall P R Q c1 c2,
      nc_text (two (kt P c1 R) (kt R c2 Q)) (kt P (KSeq c1 c2) Q)
  | NT_Choice : forall P Q c1 c2,
      nc_text (two (kt P c1 Q) (kt P c2 Q)) (kt P (KChoice c1 c2) Q)
  | NT_Star : forall I c, nc_text (one (kt I c I)) (kt I (KStar c) I)
  | NT_Cons : forall P P' Q Q' c,
      (forall s, P' s -> P s) -> (forall s, Q s -> Q' s) ->
      nc_text (one (kt P' c Q')) (kt P c Q).

Definition NC_text : @ProgramLogic T :=
  mkLogic (cvalid Backward Plain Over) (cvalid_proper _ _ _) nc_text.

Lemma nc_star_inv : forall (I : Σ -> Prop) c,
    (forall s s', kev c s s' -> I s' -> I s) ->
    forall s s', kev (KStar c) s s' -> I s' -> I s.
Proof.
  intros I c H s s' Hs. remember (KStar c) as k eqn:Ek.
  induction Hs; inversion Ek; subst; intros HI; [exact HI |].
  eapply H; [eassumption | apply IHHs2; [reflexivity | exact HI]].
Qed.

Theorem nc_text_lsound : locally_sound NC_text.
Proof.
  intros ps t HR Hps. simpl in *. destruct HR; apply ncv.
  - intros s s' Hk HQ. kinv Hk. exact HQ.
  - intros s s' Hk HQ. kinv Hk. eauto.
  - intros s s' Hk HQ. kinv Hk. auto.
  - pose proof (proj1 (ncv _ _ _) (Hps _ (or_introl eq_refl))) as H1.
    pose proof (proj1 (ncv _ _ _) (Hps _ (or_intror eq_refl))) as H2.
    intros s s' Hk HQ. kinv Hk. eauto.
  - pose proof (proj1 (ncv _ _ _) (Hps _ (or_introl eq_refl))) as H1.
    pose proof (proj1 (ncv _ _ _) (Hps _ (or_intror eq_refl))) as H2.
    intros s s' Hk HQ. kinv Hk; eauto.
  - pose proof (proj1 (ncv _ _ _) (Hps _ eq_refl)) as H1.
    intros s s' Hk HI. exact (nc_star_inv I c H1 s s' Hk HI).
  - pose proof (proj1 (ncv _ _ _) (Hps _ eq_refl)) as H1. eauto.
Qed.

Lemma nc_cons_d : forall P P' Q Q' c,
    derivable nc_text (kt P' c Q') ->
    (forall s, P' s -> P s) -> (forall s, Q s -> Q' s) ->
    derivable nc_text (kt P c Q).
Proof.
  intros P P' Q Q' c D HP HQ.
  apply (D_Rule _ (one (kt P' c Q'))); [apply NT_Cons; assumption |].
  intros t ->. exact D.
Qed.

Lemma nc_pre : forall c Q, derivable nc_text (kt (kpre c Q) c Q).
Proof.
  induction c; intros Q.
  - apply (nc_cons_d _ Q _ Q); [| | auto].
    + apply (D_Rule _ nop); [apply NT_Skip | intros t []].
    + intros s H. exists s. split; [apply KE_Skip | exact H].
  - apply (nc_cons_d _ (fun s => exists s', act_sem a s s' /\ Q s') _ Q);
      [| | auto].
    + apply (D_Rule _ nop); [apply NT_Act | intros t []].
    + intros s [s' [Ha HQ]]. exists s'. split; [apply KE_Act, Ha | exact HQ].
  - apply (nc_cons_d _ (fun s => B s /\ Q s) _ Q); [| | auto].
    + apply (D_Rule _ nop); [apply NT_Assume | intros t []].
    + intros s [HB HQ]. exists s. split; [apply KE_Assume, HB | exact HQ].
  - apply (nc_cons_d _ (kpre c1 (kpre c2 Q)) _ Q); [| | auto].
    + apply (D_Rule _ (two (kt (kpre c1 (kpre c2 Q)) c1 (kpre c2 Q))
                           (kt (kpre c2 Q) c2 Q)));
        [apply NT_Seq | intros t [-> | ->]; auto].
    + intros s [s1 [H1 [s2 [H2 HQ]]]]. exists s2.
      split; [eapply KE_Seq; eassumption | exact HQ].
  - apply (D_Rule _ (two (kt (kpre (KChoice c1 c2) Q) c1 Q)
                         (kt (kpre (KChoice c1 c2) Q) c2 Q)));
      [apply NT_Choice |].
    intros t [-> | ->].
    + apply (nc_cons_d _ (kpre c1 Q) _ Q); [apply IHc1 | | auto].
      intros s [s' [Hk HQ]]. exists s'.
      split; [apply KE_ChoiceL, Hk | exact HQ].
    + apply (nc_cons_d _ (kpre c2 Q) _ Q); [apply IHc2 | | auto].
      intros s [s' [Hk HQ]]. exists s'.
      split; [apply KE_ChoiceR, Hk | exact HQ].
  - set (I := kpre (KStar c) Q).
    apply (nc_cons_d _ I _ I); [| auto |].
    + apply (D_Rule _ (one (kt I c I))); [apply NT_Star |]. intros t ->.
      apply (nc_cons_d _ (kpre c I) _ I); [apply IHc | | auto].
      intros s [s1 [H1 [s2 [H2 HQ]]]]. exists s2.
      split; [eapply KE_StarStep; eassumption | exact HQ].
    + intros s HQ. exists s. split; [apply KE_StarRefl | exact HQ].
Qed.

Theorem nc_text_complete : complete NC_text.
Proof.
  intros [P c Q] V0.
  pose proof (proj1 (ncv P c Q) V0) as V. clear V0.
  apply (nc_cons_d _ (kpre c Q) _ Q); [apply nc_pre | | auto].
  intros s [s' [Hk HQ]]. exact (V s s' Hk HQ).
Qed.

Definition vNC_text : VLogic T Backward Plain Over :=
  @mkVLogic T Backward Plain Over NC_text (fun t => iff_refl _)
    nc_text_lsound nc_text_complete.

(** ** Incorrectness logic *)

Inductive il_text : @ruleset T :=
  | IT_Skip : forall P, il_text nop (kt P KSkip P)
  | IT_Act : forall P a,
      il_text nop (kt P (KAct a) (fun s' => exists s, P s /\ act_sem a s s'))
  | IT_Assume : forall P B,
      il_text nop (kt P (KAssume B) (fun s => P s /\ B s))
  | IT_Seq : forall P R Q c1 c2,
      il_text (two (kt P c1 R) (kt R c2 Q)) (kt P (KSeq c1 c2) Q)
  | IT_ChoiceL : forall P Q c1 c2,
      il_text (one (kt P c1 Q)) (kt P (KChoice c1 c2) Q)
  | IT_ChoiceR : forall P Q c1 c2,
      il_text (one (kt P c2 Q)) (kt P (KChoice c1 c2) Q)
  | IT_Disj : forall P Q1 Q2 c,
      il_text (two (kt P c Q1) (kt P c Q2)) (kt P c (fun s => Q1 s \/ Q2 s))
  | IT_Star : forall (X : nat -> Σ -> Prop) c,
      il_text (fun t => exists n, t = kt (X n) c (X (S n)))
              (kt (X 0) (KStar c) (fun s => exists n, X n s))
  | IT_Cons : forall P P' Q Q' c,
      (forall s, P' s -> P s) -> (forall s, Q s -> Q' s) ->
      il_text (one (kt P' c Q')) (kt P c Q).

Definition IL_text : @ProgramLogic T :=
  mkLogic (cvalid Forward Plain Under) (cvalid_proper _ _ _) il_text.

Theorem il_text_lsound : locally_sound IL_text.
Proof.
  intros ps t HR Hps. simpl in *. destruct HR; apply ilv.
  - intros s' HP. exists s'. split; [exact HP | apply KE_Skip].
  - intros s' [s [HP Ha]]. exists s. split; [exact HP | apply KE_Act, Ha].
  - intros s' [HP HB]. exists s'. split; [exact HP | apply KE_Assume, HB].
  - pose proof (proj1 (ilv _ _ _) (Hps _ (or_introl eq_refl))) as H1.
    pose proof (proj1 (ilv _ _ _) (Hps _ (or_intror eq_refl))) as H2.
    intros s'' HQ. destruct (H2 s'' HQ) as [s' [HR Hk2]].
    destruct (H1 s' HR) as [s [HP Hk1]].
    exists s. split; [exact HP | eapply KE_Seq; eassumption].
  - pose proof (proj1 (ilv _ _ _) (Hps _ eq_refl)) as H1.
    intros s' HQ. destruct (H1 s' HQ) as [s [HP Hk]].
    exists s. split; [exact HP | apply KE_ChoiceL, Hk].
  - pose proof (proj1 (ilv _ _ _) (Hps _ eq_refl)) as H1.
    intros s' HQ. destruct (H1 s' HQ) as [s [HP Hk]].
    exists s. split; [exact HP | apply KE_ChoiceR, Hk].
  - pose proof (proj1 (ilv _ _ _) (Hps _ (or_introl eq_refl))) as H1.
    pose proof (proj1 (ilv _ _ _) (Hps _ (or_intror eq_refl))) as H2.
    intros s' [HQ | HQ]; [apply H1 | apply H2]; exact HQ.
  - assert (Hn : forall n s', X n s' ->
                 exists s, X 0 s /\ kev (KStar c) s s').
    { induction n as [|n IH]; intros s' Hx.
      - exists s'. split; [exact Hx | apply KE_StarRefl].
      - pose proof (proj1 (ilv _ _ _) (Hps _ (ex_intro _ n eq_refl))) as H1.
        destruct (H1 s' Hx) as [s1 [Hx1 Hk]].
        destruct (IH s1 Hx1) as [s [Hx0 Hs]].
        exists s. split; [exact Hx0 | eapply kev_star_snoc; eassumption]. }
    intros s' [n Hx]. exact (Hn n s' Hx).
  - pose proof (proj1 (ilv _ _ _) (Hps _ eq_refl)) as H1.
    intros s' HQ. destruct (H1 s' (H0 s' HQ)) as [s [HP Hk]].
    exists s. split; [apply H, HP | exact Hk].
Qed.

Lemma il_cons_d : forall P P' Q Q' c,
    derivable il_text (kt P' c Q') ->
    (forall s, P' s -> P s) -> (forall s, Q s -> Q' s) ->
    derivable il_text (kt P c Q).
Proof.
  intros P P' Q Q' c D HP HQ.
  apply (D_Rule _ (one (kt P' c Q'))); [apply IT_Cons; assumption |].
  intros t ->. exact D.
Qed.

Fixpoint kspn (c : com) (P : Σ -> Prop) (n : nat) : Σ -> Prop :=
  match n with
  | 0 => P
  | S m => ksp c (kspn c P m)
  end.

Lemma il_sp : forall c P, derivable il_text (kt P c (ksp c P)).
Proof.
  induction c; intros P.
  - apply (il_cons_d _ P _ P); [| auto |].
    + apply (D_Rule _ nop); [apply IT_Skip | intros t []].
    + intros s' [s [HP Hk]]. kinv Hk. exact HP.
  - apply (il_cons_d _ P _ (fun s' => exists s, P s /\ act_sem a s s'));
      [| auto |].
    + apply (D_Rule _ nop); [apply IT_Act | intros t []].
    + intros s' [s [HP Hk]]. kinv Hk. eauto.
  - apply (il_cons_d _ P _ (fun s => P s /\ B s)); [| auto |].
    + apply (D_Rule _ nop); [apply IT_Assume | intros t []].
    + intros s' [s [HP Hk]]. kinv Hk. auto.
  - apply (il_cons_d _ P _ (ksp c2 (ksp c1 P))); [| auto |].
    + apply (D_Rule _ (two (kt P c1 (ksp c1 P))
                           (kt (ksp c1 P) c2 (ksp c2 (ksp c1 P)))));
        [apply IT_Seq | intros t [-> | ->]; auto].
    + intros s'' [s [HP Hk]]. kinv Hk.
      exists s1. split; [exists s; split; assumption | assumption].
  - apply (il_cons_d _ P _ (fun s => ksp c1 P s \/ ksp c2 P s)); [| auto |].
    + apply (D_Rule _ (two (kt P (KChoice c1 c2) (ksp c1 P))
                           (kt P (KChoice c1 c2) (ksp c2 P))));
        [apply IT_Disj |].
      intros t [-> | ->].
      * apply (D_Rule _ (one (kt P c1 (ksp c1 P)))); [apply IT_ChoiceL |].
        intros t ->. apply IHc1.
      * apply (D_Rule _ (one (kt P c2 (ksp c2 P)))); [apply IT_ChoiceR |].
        intros t ->. apply IHc2.
    + intros s' [s [HP Hk]]. kinv Hk; [left | right]; exists s; auto.
  - apply (il_cons_d _ (kspn c P 0) _ (fun s => exists n, kspn c P n s));
      [| auto |].
    + apply (D_Rule _ (fun t => exists n,
                         t = kt (kspn c P n) c (kspn c P (S n))));
        [apply (IT_Star (kspn c P)) |].
      intros t [n ->]. apply IHc.
    + assert (Hs : forall s s', kev (KStar c) s s' ->
                   forall n, kspn c P n s -> exists m, kspn c P m s').
      { intros s s' Hk. remember (KStar c) as k eqn:Ek.
        induction Hk; inversion Ek; subst; intros n Hn; [eauto |].
        apply (IHHk2 eq_refl (S n)). exists s. split; assumption. }
      intros s' [s [HP Hk]]. exact (Hs s s' Hk 0 HP).
Qed.

Theorem il_text_complete : complete IL_text.
Proof.
  intros [P c Q] V0.
  pose proof (proj1 (ilv P c Q) V0) as V. clear V0.
  apply (il_cons_d _ P _ (ksp c P)); [apply il_sp | auto |].
  intros s' HQ. exact (V s' HQ).
Qed.

Definition vIL_text : VLogic T Forward Plain Under :=
  @mkVLogic T Forward Plain Under IL_text (fun t => iff_refl _)
    il_text_lsound il_text_complete.

(** ** Sufficient incorrectness *)

Inductive sil_text : @ruleset T :=
  | ST_Skip : forall Q, sil_text nop (kt Q KSkip Q)
  | ST_Act : forall Q a,
      sil_text nop (kt (fun s => exists s', act_sem a s s' /\ Q s') (KAct a) Q)
  | ST_Assume : forall Q B,
      sil_text nop (kt (fun s => B s /\ Q s) (KAssume B) Q)
  | ST_Seq : forall P R Q c1 c2,
      sil_text (two (kt P c1 R) (kt R c2 Q)) (kt P (KSeq c1 c2) Q)
  | ST_ChoiceL : forall P Q c1 c2,
      sil_text (one (kt P c1 Q)) (kt P (KChoice c1 c2) Q)
  | ST_ChoiceR : forall P Q c1 c2,
      sil_text (one (kt P c2 Q)) (kt P (KChoice c1 c2) Q)
  | ST_Disj : forall P1 P2 Q c,
      sil_text (two (kt P1 c Q) (kt P2 c Q)) (kt (fun s => P1 s \/ P2 s) c Q)
  | ST_Star : forall (X : nat -> Σ -> Prop) c,
      sil_text (fun t => exists n, t = kt (X (S n)) c (X n))
               (kt (fun s => exists n, X n s) (KStar c) (X 0))
  | ST_Cons : forall P P' Q Q' c,
      (forall s, P s -> P' s) -> (forall s, Q' s -> Q s) ->
      sil_text (one (kt P' c Q')) (kt P c Q).

Definition SIL_text : @ProgramLogic T :=
  mkLogic (cvalid Backward Plain Under) (cvalid_proper _ _ _) sil_text.

Theorem sil_text_lsound : locally_sound SIL_text.
Proof.
  intros ps t HR Hps. simpl in *. destruct HR; apply silv.
  - intros s HQ. exists s. split; [apply KE_Skip | exact HQ].
  - intros s [s' [Ha HQ]]. exists s'. split; [apply KE_Act, Ha | exact HQ].
  - intros s [HB HQ]. exists s. split; [apply KE_Assume, HB | exact HQ].
  - pose proof (proj1 (silv _ _ _) (Hps _ (or_introl eq_refl))) as H1.
    pose proof (proj1 (silv _ _ _) (Hps _ (or_intror eq_refl))) as H2.
    intros s HP. destruct (H1 s HP) as [s1 [Hk1 HR]].
    destruct (H2 s1 HR) as [s2 [Hk2 HQ]].
    exists s2. split; [eapply KE_Seq; eassumption | exact HQ].
  - pose proof (proj1 (silv _ _ _) (Hps _ eq_refl)) as H1.
    intros s HP. destruct (H1 s HP) as [s' [Hk HQ]].
    exists s'. split; [apply KE_ChoiceL, Hk | exact HQ].
  - pose proof (proj1 (silv _ _ _) (Hps _ eq_refl)) as H1.
    intros s HP. destruct (H1 s HP) as [s' [Hk HQ]].
    exists s'. split; [apply KE_ChoiceR, Hk | exact HQ].
  - pose proof (proj1 (silv _ _ _) (Hps _ (or_introl eq_refl))) as H1.
    pose proof (proj1 (silv _ _ _) (Hps _ (or_intror eq_refl))) as H2.
    intros s [HP | HP]; [apply H1 | apply H2]; exact HP.
  - assert (Hn : forall n s, X n s ->
                 exists s', kev (KStar c) s s' /\ X 0 s').
    { induction n as [|n IH]; intros s Hx.
      - exists s. split; [apply KE_StarRefl | exact Hx].
      - pose proof (proj1 (silv _ _ _) (Hps _ (ex_intro _ n eq_refl))) as H1.
        destruct (H1 s Hx) as [s1 [Hk Hx1]].
        destruct (IH s1 Hx1) as [s' [Hs Hx0]].
        exists s'. split; [eapply KE_StarStep; eassumption | exact Hx0]. }
    intros s [n Hx]. exact (Hn n s Hx).
  - pose proof (proj1 (silv _ _ _) (Hps _ eq_refl)) as H1.
    intros s HP. destruct (H1 s (H s HP)) as [s' [Hk HQ]].
    exists s'. split; [exact Hk | apply H0, HQ].
Qed.

Lemma sil_cons_d : forall P P' Q Q' c,
    derivable sil_text (kt P' c Q') ->
    (forall s, P s -> P' s) -> (forall s, Q' s -> Q s) ->
    derivable sil_text (kt P c Q).
Proof.
  intros P P' Q Q' c D HP HQ.
  apply (D_Rule _ (one (kt P' c Q'))); [apply ST_Cons; assumption |].
  intros t ->. exact D.
Qed.

Fixpoint kpren (c : com) (Q : Σ -> Prop) (n : nat) : Σ -> Prop :=
  match n with
  | 0 => Q
  | S m => kpre c (kpren c Q m)
  end.

Lemma sil_pre : forall c Q, derivable sil_text (kt (kpre c Q) c Q).
Proof.
  induction c; intros Q.
  - apply (sil_cons_d _ Q _ Q); [| | auto].
    + apply (D_Rule _ nop); [apply ST_Skip | intros t []].
    + intros s [s' [Hk HQ]]. kinv Hk. exact HQ.
  - apply (sil_cons_d _ (fun s => exists s', act_sem a s s' /\ Q s') _ Q);
      [| | auto].
    + apply (D_Rule _ nop); [apply ST_Act | intros t []].
    + intros s [s' [Hk HQ]]. kinv Hk. eauto.
  - apply (sil_cons_d _ (fun s => B s /\ Q s) _ Q); [| | auto].
    + apply (D_Rule _ nop); [apply ST_Assume | intros t []].
    + intros s [s' [Hk HQ]]. kinv Hk. auto.
  - apply (sil_cons_d _ (kpre c1 (kpre c2 Q)) _ Q); [| | auto].
    + apply (D_Rule _ (two (kt (kpre c1 (kpre c2 Q)) c1 (kpre c2 Q))
                           (kt (kpre c2 Q) c2 Q)));
        [apply ST_Seq | intros t [-> | ->]; auto].
    + intros s [s'' [Hk HQ]]. kinv Hk.
      exists s1. split; [assumption | exists s''; split; assumption].
  - apply (sil_cons_d _ (fun s => kpre c1 Q s \/ kpre c2 Q s) _ Q);
      [| | auto].
    + apply (D_Rule _ (two (kt (kpre c1 Q) (KChoice c1 c2) Q)
                           (kt (kpre c2 Q) (KChoice c1 c2) Q)));
        [apply ST_Disj |].
      intros t [-> | ->].
      * apply (D_Rule _ (one (kt (kpre c1 Q) c1 Q))); [apply ST_ChoiceL |].
        intros t ->. apply IHc1.
      * apply (D_Rule _ (one (kt (kpre c2 Q) c2 Q))); [apply ST_ChoiceR |].
        intros t ->. apply IHc2.
    + intros s [s' [Hk HQ]]. kinv Hk; [left | right]; exists s'; auto.
  - apply (sil_cons_d _ (fun s => exists n, kpren c Q n s) _ (kpren c Q 0));
      [| | auto].
    + apply (D_Rule _ (fun t => exists n,
                         t = kt (kpren c Q (S n)) c (kpren c Q n)));
        [apply (ST_Star (kpren c Q)) |].
      intros t [n ->]. apply IHc.
    + assert (Hs : forall s s', kev (KStar c) s s' -> Q s' ->
                   exists n, kpren c Q n s).
      { intros s s' Hk. remember (KStar c) as k eqn:Ek.
        induction Hk; inversion Ek; subst; intros HQ; [exists 0; exact HQ |].
        destruct (IHHk2 eq_refl HQ) as [n Hn].
        exists (S n). exists s1. split; assumption. }
      intros s [s' [Hk HQ]]. exact (Hs s s' Hk HQ).
Qed.

Theorem sil_text_complete : complete SIL_text.
Proof.
  intros [P c Q] V0.
  pose proof (proj1 (silv P c Q) V0) as V. clear V0.
  apply (sil_cons_d _ (kpre c Q) _ Q); [apply sil_pre | | auto].
  intros s HP. exact (V s HP).
Qed.

Definition vSIL_text : VLogic T Backward Plain Under :=
  @mkVLogic T Backward Plain Under SIL_text (fun t => iff_refl _)
    sil_text_lsound sil_text_complete.

(** ** Textbook logics as sources for transformers

    The textbook records are ordinary records, so they can start the
    pipeline. For example, incorrectness logic and sufficient
    incorrectness logic regenerated from textbook Hoare logic: *)
Definition IL_from_textbook : VLogic T Forward Plain Under :=
  vto act_sem vHL_text Forward Plain Under.
Definition SIL_from_textbook : VLogic T Backward Plain Under :=
  vto act_sem vHL_text Backward Plain Under.

End Textbook.
