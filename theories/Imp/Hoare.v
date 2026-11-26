(** * Hoare logic for Imp

    Two presentations of (partial-correctness) Hoare logic:

    - [hoare_valid] / [hoare_valid_ss]: the semantic definition, built
      directly on the big-step / small-step semantics.
    - [hoare_proof]: the axiomatic presentation, an inductive proof system.

    We prove the proof system sound and complete with respect to the
    semantics. Assertions are shallowly embedded ([state -> Prop]), so
    completeness is in the sense of Cook (relative to an oracle for the
    assertion language): the consequence rule uses semantic implication,
    and weakest preconditions are always expressible. *)

From Stdlib Require Import Bool.
From LogicTransformers.Imp Require Import Syntax BigStep SmallStep Equiv.

(** ** Assertions *)

Definition assertion := state -> Prop.

Definition assert_implies (P Q : assertion) : Prop :=
  forall st, P st -> Q st.

Declare Scope hoare_scope.
Open Scope hoare_scope.

Notation "P ->> Q" := (assert_implies P Q)
  (at level 80) : hoare_scope.

(** [Q] with [a] substituted for [x]. *)
Definition assn_sub (x : var) (a : aexp) (Q : assertion) : assertion :=
  fun st => Q (update st x (aeval st a)).

(** A boolean expression as an assertion. *)
Definition bassn (b : bexp) : assertion :=
  fun st => beval st b = true.

Lemma bassn_false : forall b st, ~ bassn b st -> beval st b = false.
Proof. intros b st H. apply not_true_is_false. exact H. Qed.

Lemma bassn_false' : forall b st, beval st b = false -> ~ bassn b st.
Proof. unfold bassn. congruence. Qed.

(** ** Semantic Hoare triples *)

Definition hoare_valid (P : assertion) (c : com) (Q : assertion) : Prop :=
  forall st st', P st -> ceval c st st' -> Q st'.

Definition hoare_valid_ss (P : assertion) (c : com) (Q : assertion)
  : Prop :=
  forall st st', P st -> cmulti c st CSkip st' -> Q st'.

Theorem hoare_valid_big_small : forall P c Q,
    hoare_valid P c Q <-> hoare_valid_ss P c Q.
Proof.
  unfold hoare_valid, hoare_valid_ss. split; intros H st st' HP Hc.
  - apply small_to_big in Hc. eauto.
  - apply big_to_small in Hc. eauto.
Qed.

(** ** Axiomatic Hoare logic *)

Inductive hoare_proof : assertion -> com -> assertion -> Prop :=
  | H_Skip : forall P,
      hoare_proof P CSkip P
  | H_Asgn : forall Q x a,
      hoare_proof (assn_sub x a Q) (CAsgn x a) Q
  | H_Seq : forall P Q R c1 c2,
      hoare_proof P c1 Q ->
      hoare_proof Q c2 R ->
      hoare_proof P (CSeq c1 c2) R
  | H_If : forall P Q b c1 c2,
      hoare_proof (fun st => P st /\ bassn b st) c1 Q ->
      hoare_proof (fun st => P st /\ ~ bassn b st) c2 Q ->
      hoare_proof P (CIf b c1 c2) Q
  | H_While : forall P b c,
      hoare_proof (fun st => P st /\ bassn b st) c P ->
      hoare_proof P (CWhile b c) (fun st => P st /\ ~ bassn b st)
  | H_Choice : forall P Q c1 c2,
      hoare_proof P c1 Q ->
      hoare_proof P c2 Q ->
      hoare_proof P (CChoice c1 c2) Q
  | H_Havoc : forall Q x,
      hoare_proof (fun st => forall n, Q (update st x n)) (CHavoc x) Q
  | H_Consequence : forall P P' Q Q' c,
      hoare_proof P' c Q' ->
      P ->> P' ->
      Q' ->> Q ->
      hoare_proof P c Q.

Lemma H_Consequence_pre : forall P P' Q c,
    hoare_proof P' c Q -> P ->> P' -> hoare_proof P c Q.
Proof. intros. eapply H_Consequence; eauto. intros st H'; exact H'. Qed.

Lemma H_Consequence_post : forall P Q Q' c,
    hoare_proof P c Q' -> Q' ->> Q -> hoare_proof P c Q.
Proof. intros. eapply H_Consequence; eauto. intros st H'; exact H'. Qed.

(** ** Soundness *)

Theorem hoare_sound : forall P c Q,
    hoare_proof P c Q -> hoare_valid P c Q.
Proof.
  intros P c Q Hp.
  induction Hp; intros st st' HP Hc.
  - (* Skip *)
    inversion Hc; subst. exact HP.
  - (* Asgn *)
    inversion Hc; subst. exact HP.
  - (* Seq *)
    inversion Hc; subst. eauto.
  - (* If *)
    inversion Hc; subst.
    + apply (IHHp1 st st'); [split |]; assumption.
    + apply (IHHp2 st st'); [split; [|apply bassn_false'] |]; assumption.
  - (* While: induction on the loop's execution *)
    remember (CWhile b c) as w eqn:Ew.
    revert HP. induction Hc; intros HP; inversion Ew; subst.
    + split; [assumption | apply bassn_false'; assumption].
    + apply IHHc2; [reflexivity |].
      apply (IHHp st st'); [split |]; assumption.
  - (* Choice *)
    inversion Hc; subst; eauto.
  - (* Havoc *)
    inversion Hc; subst. apply HP.
  - (* Consequence *)
    eauto.
Qed.

Corollary hoare_sound_ss : forall P c Q,
    hoare_proof P c Q -> hoare_valid_ss P c Q.
Proof. intros. apply hoare_valid_big_small, hoare_sound. assumption. Qed.

(** ** Completeness, via weakest (liberal) preconditions *)

Definition wp (c : com) (Q : assertion) : assertion :=
  fun st => forall st', ceval c st st' -> Q st'.

Lemma wp_valid : forall c Q, hoare_valid (wp c Q) c Q.
Proof. intros c Q st st' H Hc. exact (H st' Hc). Qed.

Lemma wp_weakest : forall P c Q, hoare_valid P c Q -> P ->> wp c Q.
Proof. intros P c Q H st HP st' Hc. eauto. Qed.

(** Every weakest-precondition triple is derivable. *)
Lemma wp_provable : forall c Q, hoare_proof (wp c Q) c Q.
Proof.
  induction c; intros Q.
  - (* Skip *)
    eapply H_Consequence_pre; [apply H_Skip |].
    intros st H. apply H. apply E_Skip.
  - (* Asgn *)
    eapply H_Consequence_pre; [apply H_Asgn |].
    intros st H. apply H. apply E_Asgn.
  - (* Seq *)
    eapply H_Consequence_pre; [eapply H_Seq; [apply IHc1 | apply IHc2] |].
    intros st H st' H1 st'' H2. apply H. eapply E_Seq; eassumption.
  - (* If *)
    apply H_If.
    + eapply H_Consequence_pre; [apply IHc1 |].
      intros st [H Hb] st' Hc. apply H. apply E_IfTrue; assumption.
    + eapply H_Consequence_pre; [apply IHc2 |].
      intros st [H Hb] st' Hc. apply H.
      apply E_IfFalse; [apply bassn_false |]; assumption.
  - (* While: the weakest precondition of the loop is an invariant *)
    set (I := wp (CWhile b c) Q).
    eapply H_Consequence_post.
    + apply H_While.
      eapply H_Consequence_pre; [apply (IHc I) |].
      intros st [HI Hb] st' Hc st'' Hw.
      apply HI. eapply E_WhileTrue; eassumption.
    + intros st [HI Hb]. apply HI.
      apply E_WhileFalse. apply bassn_false. assumption.
  - (* Choice *)
    apply H_Choice.
    + eapply H_Consequence_pre; [apply IHc1 |].
      intros st H st' Hc. apply H. apply E_ChoiceL; assumption.
    + eapply H_Consequence_pre; [apply IHc2 |].
      intros st H st' Hc. apply H. apply E_ChoiceR; assumption.
  - (* Havoc *)
    eapply H_Consequence_pre; [apply H_Havoc |].
    intros st H n. apply H. apply E_Havoc.
Qed.

Theorem hoare_complete : forall P c Q,
    hoare_valid P c Q -> hoare_proof P c Q.
Proof.
  intros P c Q H.
  eapply H_Consequence_pre; [apply wp_provable | apply wp_weakest; exact H].
Qed.

Corollary hoare_complete_ss : forall P c Q,
    hoare_valid_ss P c Q -> hoare_proof P c Q.
Proof. intros. apply hoare_complete, hoare_valid_big_small. assumption. Qed.

(** ** Main results *)

Theorem hoare_sound_complete : forall P c Q,
    hoare_proof P c Q <-> hoare_valid P c Q.
Proof. split; [apply hoare_sound | apply hoare_complete]. Qed.

Theorem hoare_sound_complete_ss : forall P c Q,
    hoare_proof P c Q <-> hoare_valid_ss P c Q.
Proof. split; [apply hoare_sound_ss | apply hoare_complete_ss]. Qed.
