(** * The Imp encoding preserves divergence

    [enc_diverges]: an Imp program can diverge from [s] iff its encoding
    can ([diverges c s ↔ kdiv (enc c) s]). Together with [enc_correct]
    (terminating runs), the encoding preserves the whole bottom-face
    semantics ([enc_semB]), so every bottom-face validity of an Imp triple
    equals that of its encoding ([enc_cvalid_bot]).

    Proof structure: induction on the program, so that subprograms come
    with ordinary induction hypotheses. Coinduction is needed only for
    [while], where the loop can iterate forever.

    [cvalid_cvr] states once, for any language, that cube validity only
    depends on the input/output relation; [cvr_transfer] moves it between
    relations that agree. *)

From LogicTransformers.Imp Require Import Syntax BigStep Diverge Lang LangBot.
From LogicTransformers.Logics Require Import Hoare.
From LogicTransformers.Framework Require Import Language ProgramLogic Cube.
From LogicTransformers.Core Require Import Kernel KernelBot ImpCore.

Notation ikdiv := (kdiv iact_sem).

(** ** Divergence is preserved *)

Lemma enc_diverges_1 : forall c s, diverges c s -> ikdiv (enc c) s.
Proof.
  induction c; intros s H; simpl.
  - exfalso. exact (diverges_skip s H).
  - exfalso. exact (diverges_asgn x a s H).
  - inversion H; subst.
    + apply KD_SeqL, IHc1. assumption.
    + eapply KD_SeqR; [apply enc_correct; eassumption | apply IHc2; assumption].
  - inversion H; subst.
    + apply KD_ChoiceL. eapply KD_SeqR; [apply KE_Assume; assumption |].
      apply IHc1. assumption.
    + apply KD_ChoiceR. eapply KD_SeqR; [apply KE_Assume |].
      * apply bassn_false'. assumption.
      * apply IHc2. assumption.
  - apply KD_SeqL. revert s H. cofix G. intros s H. inversion H; subst.
    + apply KD_StarBody. eapply KD_SeqR; [apply KE_Assume; assumption |].
      apply IHc. assumption.
    + eapply KD_StarIter.
      * eapply KE_Seq; [apply KE_Assume; eassumption |].
        apply enc_correct. eassumption.
      * apply G. assumption.
  - inversion H; subst; [apply KD_ChoiceL | apply KD_ChoiceR]; auto.
  - exfalso. exact (diverges_havoc x s H).
Qed.

Lemma enc_diverges_2 : forall c s, ikdiv (enc c) s -> diverges c s.
Proof.
  induction c; intros s H; simpl in H.
  - inversion H.
  - inversion H.
  - inversion H; subst.
    + apply Dv_SeqL, IHc1. assumption.
    + eapply Dv_SeqR; [apply enc_correct; eassumption | apply IHc2; assumption].
  - inversion H; subst;
      match goal with H' : ikdiv (KSeq _ _) _ |- _ => inversion H'; subst end;
      try match goal with H' : ikdiv (KAssume _) _ |- _ => inversion H' end;
      match goal with H' : kev iact_sem (KAssume _) _ _ |- _ =>
        inversion H'; subst end.
    + apply Dv_IfTrue; [assumption | apply IHc1; assumption].
    + apply Dv_IfFalse; [apply bassn_false; assumption | apply IHc2; assumption].
  - inversion H; subst;
      [| match goal with H' : ikdiv (KAssume _) _ |- _ => inversion H' end].
    match goal with H' : ikdiv (KStar _) _ |- _ => clear H; rename H' into H end.
    revert s H. cofix G. intros s H. inversion H; subst.
    + match goal with H' : ikdiv (KSeq _ _) _ |- _ => inversion H'; subst end;
        [match goal with H' : ikdiv (KAssume _) _ |- _ => inversion H' end |].
      match goal with H' : kev iact_sem (KAssume _) _ _ |- _ =>
        inversion H'; subst end.
      apply Dv_WhileBody; [assumption | apply IHc; assumption].
    + match goal with H' : kev iact_sem (KSeq _ _) _ _ |- _ =>
        inversion H'; subst end.
      match goal with H' : kev iact_sem (KAssume _) _ _ |- _ =>
        inversion H'; subst end.
      eapply Dv_WhileIter; [assumption | apply enc_correct; eassumption |].
      apply G. assumption.
  - inversion H; subst; [apply Dv_ChoiceL | apply Dv_ChoiceR]; auto.
  - inversion H.
Qed.

Theorem enc_diverges : forall c s, diverges c s <-> ikdiv (enc c) s.
Proof. split; [apply enc_diverges_1 | apply enc_diverges_2]. Qed.

(** The whole bottom-face semantics is preserved. *)
Theorem enc_semB : forall c o o',
    semB c o o' <-> semKB iact_sem (enc c) o o'.
Proof.
  intros c [s|] [s'|]; simpl;
    [apply enc_correct | apply enc_diverges | tauto | tauto].
Qed.

(** ** Validity only depends on the relation, in any language *)

Definition cvr {S : Type} (P Q : S -> Prop) d p a (R : S -> S -> Prop)
  : Prop :=
  match p with
  | Plain =>
      match d, a with
      | Forward, Over => forall s s', P s -> R s s' -> Q s'
      | Forward, Under => forall s', Q s' -> exists s, P s /\ R s s'
      | Backward, Over => forall s s', R s s' -> Q s' -> P s
      | Backward, Under => forall s, P s -> exists s', R s s' /\ Q s'
      end
  | Dual =>
      match d, a with
      | Forward, Over => forall s', (forall s, R s s' -> P s) -> Q s'
      | Forward, Under => forall s', Q s' -> forall s, R s s' -> P s
      | Backward, Over => forall s, (forall s', R s s' -> Q s') -> P s
      | Backward, Under => forall s, P s -> forall s', R s s' -> Q s'
      end
  end.

Lemma cvalid_cvr : forall (L : Language) (P Q : lstate L -> Prop) c d p a,
    cvalid d p a (@mkTriple L P c Q) <-> cvr P Q d p a (sem L c).
Proof.
  intros L P Q c d [] a; destruct d, a; simpl;
    unfold aimpl, img, preimg, dimg, wlp; simpl; firstorder.
Qed.

Lemma cvr_transfer : forall {S : Type} (R1 R2 : S -> S -> Prop) P Q d p a,
    (forall s s', R1 s s' <-> R2 s s') ->
    cvr P Q d p a R1 -> cvr P Q d p a R2.
Proof.
  intros S R1 R2 P Q d p a HR H. destruct p, d, a; simpl in *.
  - intros s s' HP Hr. apply (H s s' HP), HR, Hr.
  - intros s' HQ. destruct (H s' HQ) as [s [HP Hr]].
    exists s. split; [exact HP | apply HR, Hr].
  - intros s s' Hr HQ. apply (H s s'); [apply HR, Hr | exact HQ].
  - intros s HP. destruct (H s HP) as [s' [Hr HQ]].
    exists s'. split; [apply HR, Hr | exact HQ].
  - intros s' Hall. apply H. intros s Hr. apply Hall, HR, Hr.
  - intros s' HQ s Hr. apply (H s' HQ s), HR, Hr.
  - intros s Hall. apply H. intros s' Hr. apply Hall, HR, Hr.
  - intros s HP s' Hr. apply (H s HP s'), HR, Hr.
Qed.

(** ** Bottom-face validity transfers between Imp and its encoding *)

Theorem enc_cvalid_bot : forall d p a (P Q : option state -> Prop) c,
    cvalid d p a (@mkTriple ImpBot P c Q) <->
    cvalid d p a (@mkTriple (KLangB iact_sem) P (enc c) Q).
Proof.
  intros d p a P Q c. rewrite !cvalid_cvr. simpl.
  split; apply cvr_transfer; intros o o'; rewrite enc_semB; split; auto.
Qed.
