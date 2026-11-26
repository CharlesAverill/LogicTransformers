(** * Sufficient incorrectness logic for Imp: the rules and the generated logic

    [sil P c Q] is sufficient incorrectness logic (Ascari, Bruni, Gori and
    Logozzo) for Imp: from every state in [P], some run of [c] ends in
    [Q]. Its rules work backwards:
    - the empty precondition, [skip], disjunction, consequence (pre
      strengthened, post weakened);
    - backward assignment [<<Q[a/x]>> x := a <<Q>>], and havoc
      [<<∃n. Q[n/x]>> x := * <<Q>>];
    - sequencing, either branch of [if] (with its guard in the
      precondition) and of choice;
    - [while] by a descending variant: if each [X (n+1)] state passes
      the guard and reaches [X n] by one iteration, and [X 0] states
      fail the guard, then from [∃n. X n] some run of the loop ends in
      [X 0].

    [sil_sound], [sil_complete]: sound and complete (Cook's argument with
    the possible precondition, the preimage). [sil_iff_generated]: it
    proves exactly what the generated logic at that corner
    ([Examples.Common.SILv] for Imp's atoms) proves of the encoded
    program. *)

From LogicTransformers.Imp Require Import Syntax BigStep Lang.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Verified.
From LogicTransformers.Core Require Import Kernel ImpCore.
From LogicTransformers.Imp Require Import Hoare.
From LogicTransformers.Examples Require Import Common.

Inductive sil : assertion -> com -> assertion -> Prop :=
  | SI_Empty : forall c Q, sil (fun _ => False) c Q
  | SI_Skip : forall Q, sil Q CSkip Q
  | SI_Asgn : forall Q x a, sil (assn_sub x a Q) (CAsgn x a) Q
  | SI_Havoc : forall Q x,
      sil (fun st => exists n, Q (update st x n)) (CHavoc x) Q
  | SI_Seq : forall P R Q c1 c2,
      sil P c1 R -> sil R c2 Q -> sil P (CSeq c1 c2) Q
  | SI_IfT : forall P Q b c1 c2,
      sil P c1 Q -> sil (fun st => P st /\ bassn b st) (CIf b c1 c2) Q
  | SI_IfF : forall P Q b c1 c2,
      sil P c2 Q -> sil (fun st => P st /\ ~ bassn b st) (CIf b c1 c2) Q
  | SI_ChoiceL : forall P Q c1 c2, sil P c1 Q -> sil P (CChoice c1 c2) Q
  | SI_ChoiceR : forall P Q c1 c2, sil P c2 Q -> sil P (CChoice c1 c2) Q
  | SI_While : forall (X : nat -> assertion) b c,
      (forall n, sil (X (S n)) c (X n)) ->
      (forall n st, X (S n) st -> bassn b st) ->
      (forall st, X 0 st -> ~ bassn b st) ->
      sil (fun st => exists n, X n st) (CWhile b c) (X 0)
  | SI_Disj : forall P1 P2 Q c,
      sil P1 c Q -> sil P2 c Q -> sil (fun st => P1 st \/ P2 st) c Q
  | SI_Cons : forall P P' Q Q' c,
      P ->> P' -> Q' ->> Q -> sil P' c Q' -> sil P c Q.

Definition sil_valid (P : assertion) (c : com) (Q : assertion) : Prop :=
  forall st, P st -> exists st', ceval c st st' /\ Q st'.

Theorem sil_sound : forall P c Q, sil P c Q -> sil_valid P c Q.
Proof.
  intros P c Q H. induction H; intros st HP.
  - contradiction.
  - exists st. split; [apply E_Skip | exact HP].
  - exists (update st x (aeval st a)). split; [apply E_Asgn | exact HP].
  - destruct HP as [n HQ]. exists (update st x n).
    split; [apply E_Havoc | exact HQ].
  - destruct (IHsil1 st HP) as [st1 [H1 HR]].
    destruct (IHsil2 st1 HR) as [st2 [H2 HQ]].
    exists st2. split; [eapply E_Seq; eassumption | exact HQ].
  - destruct HP as [HP Hb]. destruct (IHsil st HP) as [st' [Hc HQ]].
    exists st'. split; [apply E_IfTrue; assumption | exact HQ].
  - destruct HP as [HP Hb]. destruct (IHsil st HP) as [st' [Hc HQ]].
    exists st'. split; [apply E_IfFalse; [apply bassn_false, Hb | exact Hc]
                       | exact HQ].
  - destruct (IHsil st HP) as [st' [Hc HQ]].
    exists st'. split; [apply E_ChoiceL, Hc | exact HQ].
  - destruct (IHsil st HP) as [st' [Hc HQ]].
    exists st'. split; [apply E_ChoiceR, Hc | exact HQ].
  - destruct HP as [n Hx]. revert st Hx.
    induction n as [| n IHn]; intros st Hx.
    + exists st. split; [apply E_WhileFalse, bassn_false, H2, Hx | exact Hx].
    + destruct (H0 n st Hx) as [st1 [Hc Hx1]].
      destruct (IHn st1 Hx1) as [st2 [Hw HQ]].
      exists st2. split; [eapply E_WhileTrue; [apply H1 with n, Hx | exact Hc
                                              | exact Hw] | exact HQ].
  - destruct HP as [HP | HP]; [apply IHsil1 | apply IHsil2]; exact HP.
  - destruct (IHsil st (H st HP)) as [st' [Hc HQ]].
    exists st'. split; [exact Hc | apply H0, HQ].
Qed.

(** ** Completeness *)

Definition wpp (c : com) (Q : assertion) : assertion :=
  fun st => exists st', ceval c st st' /\ Q st'.

Fixpoint witer (b : bexp) (c : com) (Q : assertion) (n : nat) : assertion :=
  match n with
  | 0 => fun st => Q st /\ ~ bassn b st
  | S n => fun st => bassn b st /\ wpp c (witer b c Q n) st
  end.

Lemma while_witer : forall b c st st', ceval (CWhile b c) st st' ->
    forall Q, Q st' -> exists n, witer b c Q n st.
Proof.
  intros b c st st' H. remember (CWhile b c) as w eqn:Ew.
  induction H; inversion Ew; subst; intros Q HQ.
  - exists 0. split; [exact HQ | apply bassn_false', H].
  - destruct (IHceval2 eq_refl Q HQ) as [n Hn].
    exists (S n). split; [exact H |]. exists st'. split; assumption.
Qed.

Lemma witer_while : forall b c Q n st, witer b c Q n st ->
    exists st', ceval (CWhile b c) st st' /\ witer b c Q 0 st'.
Proof.
  intros b c Q n. induction n as [| n IH]; intros st Hw.
  - exists st. split; [apply E_WhileFalse, bassn_false, (proj2 Hw) | exact Hw].
  - destruct Hw as [Hb [st1 [Hc Hw]]].
    destruct (IH st1 Hw) as [st2 [Hw2 H2]].
    exists st2. split; [eapply E_WhileTrue; eassumption | exact H2].
Qed.

Lemma sil_wpp : forall c Q, sil (wpp c Q) c Q.
Proof.
  induction c as [| x a | c1 IH1 c2 IH2 | b c1 IH1 c2 IH2 | b c IH
                  | c1 IH1 c2 IH2 | x]; intros Q.
  - eapply SI_Cons; [| | apply SI_Skip]; [| intros st H; exact H].
    intros st [st' [Hc HQ]]. inversion Hc; subst. exact HQ.
  - eapply SI_Cons; [| | apply SI_Asgn]; [| intros st H; exact H].
    intros st [st' [Hc HQ]]. inversion Hc; subst. exact HQ.
  - eapply SI_Cons; [| | eapply SI_Seq; [apply IH1 | apply IH2]];
      [| intros st H; exact H].
    intros st [st'' [Hc HQ]]. inversion Hc; subst.
    exists st'. split; [| exists st''; split]; assumption.
  - eapply SI_Cons; [| |
      apply (SI_Disj (fun st => wpp c1 Q st /\ bassn b st)
                     (fun st => wpp c2 Q st /\ ~ bassn b st) Q (CIf b c1 c2));
      [apply (SI_IfT (wpp c1 Q)), IH1 | apply (SI_IfF (wpp c2 Q)), IH2]];
      [| intros st H; exact H].
    intros st [st' [Hc HQ]]. inversion Hc; subst.
    + left. split; [exists st'; split; assumption | assumption].
    + right. split; [exists st'; split; assumption |].
      apply bassn_false'; assumption.
  - eapply SI_Cons; [| | apply (SI_While (witer b c Q))].
    + intros st [st' [Hc HQ]]. exact (while_witer b c st st' Hc Q HQ).
    + intros st [HQ _]. exact HQ.
    + intros n. eapply SI_Cons; [| | apply IH]; [| intros st H; exact H].
      intros st [_ Hw]. exact Hw.
    + intros n st [Hb _]. exact Hb.
    + intros st [_ Hn]. exact Hn.
  - eapply SI_Cons; [| |
      apply (SI_Disj (wpp c1 Q) (wpp c2 Q) Q (CChoice c1 c2));
      [apply SI_ChoiceL, IH1 | apply SI_ChoiceR, IH2]];
      [| intros st H; exact H].
    intros st [st' [Hc HQ]]. inversion Hc; subst;
      [left | right]; exists st'; split; assumption.
  - eapply SI_Cons; [| | apply SI_Havoc]; [| intros st H; exact H].
    intros st [st' [Hc HQ]]. inversion Hc; subst. eauto.
Qed.

Theorem sil_complete : forall P c Q, sil_valid P c Q -> sil P c Q.
Proof.
  intros P c Q V. eapply SI_Cons; [| | apply sil_wpp];
    [| intros st H; exact H].
  intros st HP. exact (V st HP).
Qed.

Theorem sil_iff_generated : forall P c Q,
    sil P c Q <->
    derivable (rules (vl_logic (SILv iact_sem)))
      (@mkTriple ICore P (enc c) Q).
Proof.
  intros P c Q. rewrite vl_theory, <- enc_cvalid, cvalid_Imp_rel. simpl.
  split; [apply sil_sound | apply sil_complete].
Qed.
