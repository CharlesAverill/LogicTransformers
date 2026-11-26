(** * Proof rules at the four dual corners, in any record

    [Core.Rules] gives rules at the four plain corners. This file gives
    them at the four dual corners, stated directly rather than by
    transport, for any core language and any record at the corner.
    Writing [R] for the program's relation:

    - backward dual under-approximation ([p̃re ⊆], the wlp corner): every
      run from [P] ends in [Q], the same validity as Hoare logic, with
      the same rules (backward atoms through wlp, invariant iteration);
    - forward dual under-approximation ([p̃ost ⊆]): every state that
      reaches [Q] comes from [P]; necessary-condition rules (atoms by
      preimage, a backward invariant);
    - forward dual over-approximation ([p̃ost ⊇], the complement of
      incorrectness logic): a state all of whose predecessors are in
      [P] is in [Q]; rules by the dual image, with an iteration rule
      that is the complement of O'Hearn's variant;
    - backward dual over-approximation ([p̃re ⊇], the complement of
      sufficient incorrectness logic): a state all of whose successors
      are in [Q] is in [P]; rules by wlp, with an iteration rule that is
      the complement of the descending variant.

    Each rule is proved once from the corner's validity, and the record's
    completeness makes it derivable. Constructive. *)

From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Relational Verified.
From LogicTransformers.Core Require Import Kernel Rules.

Section DualRules.

Context {Σ Act : Type} (act_sem : Act -> Σ -> Σ -> Prop).

Notation T := (KLang act_sem).
Notation kev := (kev act_sem).
Notation prov := (prov act_sem).

Lemma prov_cvr : forall d p a (V : VLogic T d p a) P c Q,
    prov V P c Q <-> cvr P Q d p a (kev c).
Proof.
  intros d p a V P c Q. unfold Rules.prov. rewrite vl_theory, cvalid_cvr.
  reflexivity.
Qed.

Lemma star_ind_fwd : forall c (Inv : Σ -> Prop),
    (forall s s', Inv s -> kev c s s' -> Inv s') ->
    forall s s', kev (KStar c) s s' -> Inv s -> Inv s'.
Proof.
  intros c Inv H s s' Hk. remember (KStar c) as k eqn:Ek.
  induction Hk; inversion Ek; subst; intros Hi; [exact Hi |].
  apply IHHk2; [reflexivity | eapply H; eassumption].
Qed.

Lemma star_ind_bwd : forall c (Inv : Σ -> Prop),
    (forall s s', kev c s s' -> Inv s' -> Inv s) ->
    forall s s', kev (KStar c) s s' -> Inv s' -> Inv s.
Proof.
  intros c Inv H s s' Hk. remember (KStar c) as k eqn:Ek.
  induction Hk; inversion Ek; subst; intros Hi; [exact Hi |].
  eapply H; [eassumption | apply IHHk2; [reflexivity | exact Hi]].
Qed.

Ltac go H := rewrite prov_cvr in *; simpl in *; H.

(** ** Backward dual under-approximation: every run from P ends in Q *)

Section BDU.
Variable V : VLogic T Backward Dual Under.

Lemma bdu_skip : forall Q, prov V Q KSkip Q.
Proof. intros. go idtac. intros s HP s' Hk. inversion Hk; subst. exact HP. Qed.

Lemma bdu_act : forall Q a,
    prov V (fun s => forall s', act_sem a s s' -> Q s') (KAct a) Q.
Proof. intros. go idtac. intros s HP s' Hk. inversion Hk; subst. auto. Qed.

Lemma bdu_assume : forall Q B, prov V (fun s => B s -> Q s) (KAssume B) Q.
Proof. intros. go idtac. intros s HP s' Hk. inversion Hk; subst. auto. Qed.

Lemma bdu_seq : forall P R Q c1 c2,
    prov V P c1 R -> prov V R c2 Q -> prov V P (KSeq c1 c2) Q.
Proof.
  intros P R Q c1 c2 H1 H2. go idtac. intros s HP s'' Hk.
  inversion Hk; subst. eapply H2; [eapply H1 |]; eassumption.
Qed.

Lemma bdu_choice : forall P Q c1 c2,
    prov V P c1 Q -> prov V P c2 Q -> prov V P (KChoice c1 c2) Q.
Proof.
  intros P Q c1 c2 H1 H2. go idtac. intros s HP s' Hk.
  inversion Hk; subst; [eapply H1 | eapply H2]; eassumption.
Qed.

Lemma bdu_star : forall I c, prov V I c I -> prov V I (KStar c) I.
Proof.
  intros I c H. go idtac. intros s HI s' Hk.
  exact (star_ind_fwd c I (fun s s' Hi Hc => H s Hi s' Hc) s s' Hk HI).
Qed.

Lemma bdu_cons : forall P P' Q Q' c,
    (forall s, P s -> P' s) -> (forall s, Q' s -> Q s) ->
    prov V P' c Q' -> prov V P c Q.
Proof.
  intros P P' Q Q' c HP HQ H. go idtac. intros s Hp s' Hk.
  apply HQ, (H s (HP s Hp) s' Hk).
Qed.
End BDU.

(** ** Forward dual under-approximation: whatever reaches Q came from P *)

Section FDU.
Variable V : VLogic T Forward Dual Under.

Lemma fdu_skip : forall Q, prov V Q KSkip Q.
Proof. intros. go idtac. intros s' HQ s Hk. inversion Hk; subst. exact HQ. Qed.

Lemma fdu_act : forall Q a,
    prov V (fun s => exists s', act_sem a s s' /\ Q s') (KAct a) Q.
Proof. intros. go idtac. intros s' HQ s Hk. inversion Hk; subst. eauto. Qed.

Lemma fdu_assume : forall Q B, prov V (fun s => B s /\ Q s) (KAssume B) Q.
Proof. intros. go idtac. intros s' HQ s Hk. inversion Hk; subst. auto. Qed.

Lemma fdu_seq : forall P R Q c1 c2,
    prov V P c1 R -> prov V R c2 Q -> prov V P (KSeq c1 c2) Q.
Proof.
  intros P R Q c1 c2 H1 H2. go idtac. intros s'' HQ s Hk.
  inversion Hk; subst. eapply H1; [eapply H2 |]; eassumption.
Qed.

Lemma fdu_choice : forall P1 P2 Q c1 c2,
    prov V P1 c1 Q -> prov V P2 c2 Q ->
    prov V (fun s => P1 s \/ P2 s) (KChoice c1 c2) Q.
Proof.
  intros P1 P2 Q c1 c2 H1 H2. go idtac. intros s' HQ s Hk.
  inversion Hk; subst; [left; eapply H1 | right; eapply H2]; eassumption.
Qed.

Lemma fdu_star : forall I c, prov V I c I -> prov V I (KStar c) I.
Proof.
  intros I c H. go idtac. intros s' HI s Hk.
  exact (star_ind_bwd c I (fun s s' Hc Hi => H s' Hi s Hc) s s' Hk HI).
Qed.

Lemma fdu_cons : forall P P' Q Q' c,
    (forall s, P' s -> P s) -> (forall s, Q s -> Q' s) ->
    prov V P' c Q' -> prov V P c Q.
Proof.
  intros P P' Q Q' c HP HQ H. go idtac. intros s' Hq s Hk.
  apply HP, (H s' (HQ s' Hq) s Hk).
Qed.
End FDU.

(** ** Forward dual over-approximation: all predecessors in P gives Q *)

Section FDO.
Variable V : VLogic T Forward Dual Over.

Lemma fdo_skip : forall P, prov V P KSkip P.
Proof. intros. go idtac. intros s' H. apply H, KE_Skip. Qed.

Lemma fdo_act : forall P a,
    prov V P (KAct a) (fun s' => forall s, act_sem a s s' -> P s).
Proof. intros. go idtac. intros s' H s Ha. apply H, KE_Act, Ha. Qed.

Lemma fdo_assume : forall P B, prov V P (KAssume B) (fun s => B s -> P s).
Proof. intros. go idtac. intros s' H HB. apply H, KE_Assume, HB. Qed.

Lemma fdo_seq : forall P R Q c1 c2,
    prov V P c1 R -> prov V R c2 Q -> prov V P (KSeq c1 c2) Q.
Proof.
  intros P R Q c1 c2 H1 H2. go idtac. intros s'' H. apply H2.
  intros s' Hk2. apply H1. intros s Hk1. apply H. eapply KE_Seq; eassumption.
Qed.

Lemma fdo_choice : forall P Q1 Q2 c1 c2,
    prov V P c1 Q1 -> prov V P c2 Q2 ->
    prov V P (KChoice c1 c2) (fun s => Q1 s /\ Q2 s).
Proof.
  intros P Q1 Q2 c1 c2 H1 H2. go idtac. intros s' H. split.
  - apply H1. intros s Hk. apply H, KE_ChoiceL, Hk.
  - apply H2. intros s Hk. apply H, KE_ChoiceR, Hk.
Qed.

(** The complement of O'Hearn's variant. *)
Lemma fdo_star : forall (Y : nat -> Σ -> Prop) c,
    (forall n, prov V (Y n) c (Y (S n))) ->
    prov V (Y 0) (KStar c) (fun s => forall n, Y n s).
Proof.
  intros Y c H. go idtac. intros s' Hall n. revert s' Hall.
  induction n as [| n IH]; intros s' Hall.
  - apply Hall, KE_StarRefl.
  - apply (proj1 (prov_cvr _ _ _ V _ _ _) (H n)).
    intros s Hk. apply IH. intros s0 Hs. apply Hall.
    eapply kev_star_snoc; eassumption.
Qed.

Lemma fdo_cons : forall P P' Q Q' c,
    (forall s, P s -> P' s) -> (forall s, Q' s -> Q s) ->
    prov V P' c Q' -> prov V P c Q.
Proof.
  intros P P' Q Q' c HP HQ H. go idtac. intros s' K.
  apply HQ, H. intros s Hk. apply HP, K, Hk.
Qed.
End FDO.

(** ** Backward dual over-approximation: all successors in Q gives P *)

Section BDO.
Variable V : VLogic T Backward Dual Over.

Lemma bdo_skip : forall Q, prov V Q KSkip Q.
Proof. intros. go idtac. intros s H. apply H, KE_Skip. Qed.

Lemma bdo_act : forall Q a,
    prov V (fun s => forall s', act_sem a s s' -> Q s') (KAct a) Q.
Proof. intros. go idtac. intros s H s' Ha. apply H, KE_Act, Ha. Qed.

Lemma bdo_assume : forall Q B, prov V (fun s => B s -> Q s) (KAssume B) Q.
Proof. intros. go idtac. intros s H HB. apply H, KE_Assume, HB. Qed.

Lemma bdo_seq : forall P R Q c1 c2,
    prov V P c1 R -> prov V R c2 Q -> prov V P (KSeq c1 c2) Q.
Proof.
  intros P R Q c1 c2 H1 H2. go idtac. intros s H. apply H1.
  intros s' Hk1. apply H2. intros s'' Hk2. apply H.
  eapply KE_Seq; eassumption.
Qed.

Lemma bdo_choice : forall P1 P2 Q c1 c2,
    prov V P1 c1 Q -> prov V P2 c2 Q ->
    prov V (fun s => P1 s /\ P2 s) (KChoice c1 c2) Q.
Proof.
  intros P1 P2 Q c1 c2 H1 H2. go idtac. intros s H. split.
  - apply H1. intros s' Hk. apply H, KE_ChoiceL, Hk.
  - apply H2. intros s' Hk. apply H, KE_ChoiceR, Hk.
Qed.

(** The complement of the descending variant. *)
Lemma bdo_star : forall (Y : nat -> Σ -> Prop) c,
    (forall n, prov V (Y (S n)) c (Y n)) ->
    prov V (fun s => forall n, Y n s) (KStar c) (Y 0).
Proof.
  intros Y c H. go idtac. intros s Hall n. revert s Hall.
  induction n as [| n IH]; intros s Hall.
  - apply Hall, KE_StarRefl.
  - apply (proj1 (prov_cvr _ _ _ V _ _ _) (H n)).
    intros s' Hk. apply IH. intros s'' Hs. apply Hall.
    eapply KE_StarStep; eassumption.
Qed.

Lemma bdo_cons : forall P P' Q Q' c,
    (forall s, P' s -> P s) -> (forall s, Q s -> Q' s) ->
    prov V P' c Q' -> prov V P c Q.
Proof.
  intros P P' Q Q' c HP HQ H. go idtac. intros s K.
  apply HP, H. intros s' Hk. apply HQ, K, Hk.
Qed.
End BDO.

End DualRules.
