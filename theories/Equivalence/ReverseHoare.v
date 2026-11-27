(** * Reverse Hoare logic (node 10 of Cousot's figure)

    De Vries and Koutavas's reverse Hoare logic (SEFM 2011) has the same
    validity as O'Hearn's incorrectness logic without error outcomes:
    [[P] c [Q]] says every state in [Q] is reached from [P]. Its rules
    differ: choice and conditionals combine both branches' reachable
    states, loops use a backward variant with the exit test, and there is
    no rule for the empty postcondition or for unrolling.

    [rh] is that rule set for Imp, as reconstructed from the paper's
    presentation. [rh_sound] embeds each rule in O'Hearn's system
    ([ImpIL.ohil]); [rh_complete] is Cook's argument with strongest
    postconditions; [rh_iff_generated]: it proves exactly what the
    generated incorrectness logic proves of the encoded program. *)

From LogicTransformers.Imp Require Import Syntax BigStep Lang Hoare.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Verified.
From LogicTransformers.Core Require Import Kernel ImpCore.
From LogicTransformers.Examples Require Import Common.
From LogicTransformers.Equivalence Require Import ImpIL.

Definition sassn := state -> Prop.

Inductive rh : sassn -> com -> sassn -> Prop :=
  | RH_Skip : forall P, rh P CSkip P
  | RH_Asgn : forall P x a,
      rh P (CAsgn x a)
         (fun s => exists v, P (update s x v) /\
                             s x = aeval (update s x v) a)
  | RH_Havoc : forall P x, rh P (CHavoc x) (fun s => exists v, P (update s x v))
  | RH_Seq : forall P R Q c1 c2, rh P c1 R -> rh R c2 Q -> rh P (CSeq c1 c2) Q
  | RH_Choice : forall P Q1 Q2 c1 c2,
      rh P c1 Q1 -> rh P c2 Q2 ->
      rh P (CChoice c1 c2) (fun s => Q1 s \/ Q2 s)
  | RH_If : forall P Q1 Q2 b c1 c2,
      rh (fun s => P s /\ bassn b s) c1 Q1 ->
      rh (fun s => P s /\ ~ bassn b s) c2 Q2 ->
      rh P (CIf b c1 c2) (fun s => Q1 s \/ Q2 s)
  | RH_While : forall (X : nat -> sassn) b c,
      (forall n, rh (fun s => X n s /\ bassn b s) c (X (S n))) ->
      rh (X 0) (CWhile b c) (fun s => exists n, X n s /\ ~ bassn b s)
  | RH_Disj : forall P1 Q1 P2 Q2 c,
      rh P1 c Q1 -> rh P2 c Q2 ->
      rh (fun s => P1 s \/ P2 s) c (fun s => Q1 s \/ Q2 s)
  | RH_Cons : forall P P' Q Q' c,
      (forall s, P s -> P' s) -> (forall s, Q' s -> Q s) ->
      rh P c Q -> rh P' c Q'.

Ltac same := exact (fun _ k => k).

Lemma rh_ohil : forall P c Q, rh P c Q -> ohil P c Q.
Proof.
  intros P c Q H. induction H.
  - apply OI_Skip.
  - apply OI_Asgn.
  - apply OI_Havoc.
  - eapply OI_Seq; eassumption.
  - eapply OI_Cons; [| same | apply (OI_Disj P Q1 P Q2)];
      [intros s [K | K]; exact K | apply OI_ChoiceL | apply OI_ChoiceR];
      assumption.
  - eapply OI_Cons; [| same | apply (OI_Disj P Q1 P Q2)];
      [intros s [K | K]; exact K | apply OI_IfT | apply OI_IfF];
      assumption.
  - apply OI_Variant. assumption.
  - apply OI_Disj; assumption.
  - eapply OI_Cons; eassumption.
Qed.

Theorem rh_sound : forall P c Q, rh P c Q -> il_valid P c Q.
Proof. intros. apply ohil_sound, rh_ohil. assumption. Qed.

Lemma rh_sp : forall c P, rh P c (sp c P).
Proof.
  induction c as [| x a | c1 IH1 c2 IH2 | b c1 IH1 c2 IH2 | b c IH
                  | c1 IH1 c2 IH2 | x]; intros P.
  - eapply RH_Cons; [same | | apply RH_Skip].
    intros s' [s [HP Hc]]. inversion Hc; subst. exact HP.
  - eapply RH_Cons; [same | | apply RH_Asgn].
    intros s' [s [HP Hc]]. inversion Hc; subst.
    exists (s x). rewrite update_shadow, update_same, update_eq.
    split; [exact HP | reflexivity].
  - eapply RH_Seq; [apply IH1 |].
    eapply RH_Cons; [same | | apply IH2].
    intros s'' [s [HP Hc]]. inversion Hc; subst.
    exists st'. split; [exists s; split |]; assumption.
  - eapply RH_Cons; [same | | apply RH_If; [apply IH1 | apply IH2]].
    intros s' [s [HP Hc]]. inversion Hc; subst.
    + left. exists s. split; [split |]; assumption.
    + right. exists s. split; [split; [| apply bassn_false'] |]; assumption.
  - eapply RH_Cons; [same | | apply (RH_While (witer b c P))].
    + intros s' [s [HP Hc]]. exact (while_witer b c s s' Hc P 0 HP).
    + intros n. apply IH.
  - eapply RH_Cons; [same | | apply RH_Choice; [apply IH1 | apply IH2]].
    intros s' [s [HP Hc]]. inversion Hc; subst;
      [left | right]; exists s; split; assumption.
  - eapply RH_Cons; [same | | apply RH_Havoc].
    intros s' [s [HP Hc]]. inversion Hc; subst.
    exists (s x). rewrite update_shadow, update_same. exact HP.
Qed.

Theorem rh_complete : forall P c Q, il_valid P c Q -> rh P c Q.
Proof.
  intros P c Q V. eapply RH_Cons; [same | | apply rh_sp].
  intros s' HQ. exact (V s' HQ).
Qed.

Theorem rh_iff_generated : forall P c Q,
    rh P c Q <->
    derivable (rules (vl_logic (ILv iact_sem)))
      (@mkTriple ICore P (enc c) Q).
Proof.
  intros P c Q. rewrite vl_theory, <- enc_cvalid, cvalid_Imp_rel. simpl.
  split; [apply rh_sound | apply rh_complete].
Qed.
