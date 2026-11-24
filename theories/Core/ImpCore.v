(** * Imp as an instance of the core language

    Atoms are assignment and havoc; [if] and [while] are the usual
    encodings:

<<
      if b c₁ c₂   ↦  (assume b ; c₁) ⊕ (assume ¬b ; c₂)
      while b c    ↦  (assume b ; c)* ; assume ¬b
>>

    [enc_correct]: the encoding preserves the big-step semantics, so every
    cube validity of an Imp triple equals that of its encoding
    ([enc_cvalid]). *)

From LogicTransformers.Imp Require Import Syntax BigStep Lang.
From LogicTransformers.Logics Require Import Hoare.
From LogicTransformers.Framework Require Import Language ProgramLogic Cube.
From LogicTransformers.Core Require Import Kernel.

Inductive iact := IAsgn (x : var) (a : aexp) | IHavoc (x : var).

Definition iact_sem (a : iact) (s s' : state) : Prop :=
  match a with
  | IAsgn x e => s' = update s x (aeval s e)
  | IHavoc x => exists n, s' = update s x n
  end.

Notation icom := (kcom state iact).
Notation ikev := (kev iact_sem).

Fixpoint enc (c : com) : icom :=
  match c with
  | CSkip => KSkip
  | CAsgn x a => KAct (IAsgn x a)
  | CSeq c1 c2 => KSeq (enc c1) (enc c2)
  | CIf b c1 c2 =>
      KChoice (KSeq (KAssume (bassn b)) (enc c1))
              (KSeq (KAssume (fun s => ~ bassn b s)) (enc c2))
  | CWhile b c =>
      KSeq (KStar (KSeq (KAssume (bassn b)) (enc c)))
           (KAssume (fun s => ~ bassn b s))
  | CChoice c1 c2 => KChoice (enc c1) (enc c2)
  | CHavoc x => KAct (IHavoc x)
  end.

Lemma enc_complete : forall c s s', ceval c s s' -> ikev (enc c) s s'.
Proof.
  intros c s s' H. induction H; simpl.
  - apply KE_Skip.
  - apply KE_Act. reflexivity.
  - eapply KE_Seq; eassumption.
  - apply KE_ChoiceL. eapply KE_Seq; [apply KE_Assume; exact H | exact IHceval].
  - apply KE_ChoiceR. eapply KE_Seq; [apply KE_Assume | exact IHceval].
    apply bassn_false'. exact H.
  - eapply KE_Seq; [apply KE_StarRefl | apply KE_Assume].
    apply bassn_false'. exact H.
  - simpl in IHceval2. inversion IHceval2; subst.
    eapply KE_Seq; [| eassumption].
    eapply KE_StarStep; [| eassumption].
    eapply KE_Seq; [apply KE_Assume; exact H | exact IHceval1].
  - apply KE_ChoiceL. exact IHceval.
  - apply KE_ChoiceR. exact IHceval.
  - apply KE_Act. exists n. reflexivity.
Qed.

Lemma enc_while_star : forall b c,
    (forall s s', ikev (enc c) s s' -> ceval c s s') ->
    forall s s1, ikev (KStar (KSeq (KAssume (bassn b)) (enc c))) s s1 ->
    forall s', ceval (CWhile b c) s1 s' -> ceval (CWhile b c) s s'.
Proof.
  intros b c IHc s s1 Hs.
  remember (KStar (KSeq (KAssume (bassn b)) (enc c))) as k eqn:Ek.
  induction Hs; inversion Ek; subst; intros s' Hw; [exact Hw |].
  match goal with H' : ikev (KSeq _ _) _ _ |- _ => inversion H'; subst end.
  match goal with H' : ikev (KAssume _) _ _ |- _ => inversion H'; subst end.
  eapply E_WhileTrue; [eassumption | apply IHc; eassumption |].
  apply IHHs2; auto.
Qed.

Lemma enc_sound : forall c s s', ikev (enc c) s s' -> ceval c s s'.
Proof.
  induction c; intros s s' H; simpl in H.
  - inversion H; subst. apply E_Skip.
  - inversion H; subst. simpl in *. subst. apply E_Asgn.
  - inversion H; subst. eapply E_Seq; eauto.
  - inversion H; subst;
      match goal with H' : ikev (KSeq _ _) _ _ |- _ => inversion H'; subst end;
      match goal with H' : ikev (KAssume _) _ _ |- _ => inversion H'; subst end.
    + apply E_IfTrue; auto.
    + apply E_IfFalse; [apply bassn_false; assumption | auto].
  - inversion H; subst.
    match goal with H' : ikev (KAssume _) _ _ |- _ => inversion H'; subst end.
    eapply enc_while_star; [exact IHc | eassumption |].
    apply E_WhileFalse, bassn_false. assumption.
  - inversion H; subst; [apply E_ChoiceL | apply E_ChoiceR]; auto.
  - inversion H; subst. simpl in *.
    match goal with H' : exists _, _ |- _ => destruct H' as [n ->] end.
    apply E_Havoc.
Qed.

Theorem enc_correct : forall c s s', ceval c s s' <-> ikev (enc c) s s'.
Proof. split; [apply enc_complete | apply enc_sound]. Qed.

Definition ICore : Language := KLang iact_sem.

(** Cube validity only depends on the input/output relation, so it
    transfers between two languages with the same states. *)
Definition cv_rel (P Q : state -> Prop) d p a (R : state -> state -> Prop)
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

Lemma cv_rel_transfer : forall R1 R2 P Q d p a,
    (forall s s', R1 s s' <-> R2 s s') ->
    cv_rel P Q d p a R1 -> cv_rel P Q d p a R2.
Proof.
  intros R1 R2 P Q d p a HR H. destruct p, d, a; simpl in *.
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

Ltac cv_unfold :=
  intros P Q c d p a; destruct p, d, a; simpl;
  unfold aimpl, img, preimg, dimg, wlp; simpl; firstorder.

Lemma cvalid_Imp_rel : forall (P Q : state -> Prop) c d p a,
    cvalid d p a (@mkTriple Imp P c Q) <-> cv_rel P Q d p a (ceval c).
Proof. cv_unfold. Qed.

Lemma cvalid_ICore_rel : forall (P Q : state -> Prop) c d p a,
    cvalid d p a (@mkTriple ICore P c Q) <-> cv_rel P Q d p a (ikev c).
Proof. cv_unfold. Qed.

Theorem enc_cvalid : forall d p a (P Q : state -> Prop) c,
    cvalid d p a (@mkTriple Imp P c Q) <->
    cvalid d p a (@mkTriple ICore P (enc c) Q).
Proof.
  intros d p a P Q c.
  rewrite cvalid_Imp_rel, cvalid_ICore_rel.
  split; apply cv_rel_transfer; intros s s'; rewrite enc_correct;
    split; auto.
Qed.
