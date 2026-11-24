(** * Equivalence of big-step and small-step semantics *)

From LogicTransformers.Imp Require Import Syntax BigStep SmallStep.

Theorem big_to_small : forall c st st',
    ceval c st st' -> cmulti c st CSkip st'.
Proof.
  intros c st st' H.
  induction H.
  - apply MS_Refl.
  - eapply MS_Step; [apply S_Asgn | apply MS_Refl].
  - eapply cmulti_trans; [apply cmulti_seq; eassumption |].
    eapply MS_Step; [apply S_SeqSkip | assumption].
  - eapply MS_Step; [apply S_IfTrue; assumption | assumption].
  - eapply MS_Step; [apply S_IfFalse; assumption | assumption].
  - eapply MS_Step; [apply S_While |].
    eapply MS_Step; [apply S_IfFalse; assumption | apply MS_Refl].
  - eapply MS_Step; [apply S_While |].
    eapply MS_Step; [apply S_IfTrue; assumption |].
    eapply cmulti_trans; [apply cmulti_seq; eassumption |].
    eapply MS_Step; [apply S_SeqSkip | assumption].
  - eapply MS_Step; [apply S_ChoiceL | assumption].
  - eapply MS_Step; [apply S_ChoiceR | assumption].
  - eapply MS_Step; [apply S_Havoc | apply MS_Refl].
Qed.

(** A single step can be "absorbed" by a big-step derivation. *)
Lemma step_ceval : forall c st c' st' st'',
    cstep c st c' st' -> ceval c' st' st'' -> ceval c st st''.
Proof.
  intros c st c' st' st'' Hs. revert st''.
  induction Hs; intros st'' Hc.
  - inversion Hc; subst. apply E_Asgn.
  - eapply E_Seq; [apply E_Skip | exact Hc].
  - inversion Hc; subst. eapply E_Seq; [apply IHHs; eassumption | eassumption].
  - apply E_IfTrue; assumption.
  - apply E_IfFalse; assumption.
  - inversion Hc; subst.
    + match goal with
      | H : ceval (CSeq _ _) _ _ |- _ => inversion H; subst
      end.
      eapply E_WhileTrue; eassumption.
    + match goal with
      | H : ceval CSkip _ _ |- _ => inversion H; subst
      end.
      apply E_WhileFalse; assumption.
  - apply E_ChoiceL; assumption.
  - apply E_ChoiceR; assumption.
  - inversion Hc; subst. apply E_Havoc.
Qed.

Theorem small_to_big : forall c st st',
    cmulti c st CSkip st' -> ceval c st st'.
Proof.
  intros c st st' H.
  remember CSkip as skip eqn:Eskip.
  induction H; subst.
  - apply E_Skip.
  - eapply step_ceval; [eassumption | auto].
Qed.

Theorem big_small_equiv : forall c st st',
    ceval c st st' <-> cmulti c st CSkip st'.
Proof. split; [apply big_to_small | apply small_to_big]. Qed.
