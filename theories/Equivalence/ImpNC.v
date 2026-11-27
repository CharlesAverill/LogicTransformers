(** * Necessary-condition logic for Imp (node 11 of Cousot's figure)

    A necessary-condition triple [(P, c, Q)] says that [P] is necessary
    for [c] to end in [Q]: every state from which some run ends in [Q]
    satisfies [P] (Cousot, Cousot, Fähndrich and Logozzo 2013; Ascari et
    al. 2023). [nc] gives backward rules in that style:

    - assignment and havoc by substitution and an existential;
    - [if] and choice combine the branches' necessary conditions;
    - [while] by a backward invariant [I]: exits in [Q] are in [I], and
      a state that passes the test and can reach [I] in one iteration is
      in [I];
    - consequence weakens the precondition and strengthens the
      postcondition.

    [nc_sound], [nc_complete]: sound and complete (Cook's argument with
    the possible precondition). [nc_iff_generated]: it proves exactly
    what the generated logic at that corner proves of the encoded
    program. The rules are reconstructed in the style of these papers,
    not copied from them. Constructive. *)

From LogicTransformers.Imp Require Import Syntax BigStep Lang Hoare.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Verified.
From LogicTransformers.Core Require Import Kernel ImpCore.
From LogicTransformers.Examples Require Import Common.

Definition sassn := state -> Prop.

Inductive nc : sassn -> com -> sassn -> Prop :=
  | NC_Skip : forall Q, nc Q CSkip Q
  | NC_Asgn : forall Q x a, nc (assn_sub x a Q) (CAsgn x a) Q
  | NC_Havoc : forall Q x,
      nc (fun s => exists n, Q (update s x n)) (CHavoc x) Q
  | NC_Seq : forall P R Q c1 c2, nc P c1 R -> nc R c2 Q -> nc P (CSeq c1 c2) Q
  | NC_If : forall P1 P2 Q b c1 c2,
      nc P1 c1 Q -> nc P2 c2 Q ->
      nc (fun s => (bassn b s /\ P1 s) \/ (~ bassn b s /\ P2 s))
         (CIf b c1 c2) Q
  | NC_Choice : forall P1 P2 Q c1 c2,
      nc P1 c1 Q -> nc P2 c2 Q ->
      nc (fun s => P1 s \/ P2 s) (CChoice c1 c2) Q
  | NC_While : forall (I J Q : sassn) b c,
      nc J c I ->
      (forall s, ~ bassn b s -> Q s -> I s) ->
      (forall s, bassn b s -> J s -> I s) ->
      nc I (CWhile b c) Q
  | NC_Cons : forall P P' Q Q' c,
      (forall s, P' s -> P s) -> (forall s, Q s -> Q' s) ->
      nc P' c Q' -> nc P c Q.

Definition nc_valid (P : sassn) (c : com) (Q : sassn) : Prop :=
  forall s s', ceval c s s' -> Q s' -> P s.

Theorem nc_sound : forall P c Q, nc P c Q -> nc_valid P c Q.
Proof.
  intros P c Q H. induction H; intros s t Hc HQ.
  - inversion Hc; subst. exact HQ.
  - inversion Hc; subst. exact HQ.
  - inversion Hc; subst. eauto.
  - inversion Hc; subst. eapply IHnc1; [eassumption |].
    eapply IHnc2; eassumption.
  - inversion Hc; subst.
    + left. split; [assumption | eapply IHnc1; eassumption].
    + right. split; [apply bassn_false'; assumption |].
      eapply IHnc2; eassumption.
  - inversion Hc; subst; [left; eapply IHnc1 | right; eapply IHnc2];
      eassumption.
  - remember (CWhile b c) as w eqn:Ew. induction Hc; inversion Ew; subst.
    + apply H0; [apply bassn_false'; assumption | exact HQ].
    + apply H1; [assumption |]. eapply IHnc; [eassumption |].
      apply IHHc2; [reflexivity | exact HQ].
  - apply H, (IHnc s t Hc (H0 t HQ)).
Qed.

(** The possible precondition: some run ends in [Q]. *)
Definition ppre (c : com) (Q : sassn) : sassn :=
  fun s => exists t, ceval c s t /\ Q t.

Ltac same := exact (fun _ k => k).

Lemma nc_ppre : forall c Q, nc (ppre c Q) c Q.
Proof.
  induction c as [| x a | c1 IH1 c2 IH2 | b c1 IH1 c2 IH2 | b c IH
                  | c1 IH1 c2 IH2 | x]; intros Q.
  - eapply NC_Cons; [| same | apply NC_Skip].
    intros s HQ. exists s. split; [apply E_Skip | exact HQ].
  - eapply NC_Cons; [| same | apply NC_Asgn].
    intros s HQ. eexists. split; [apply E_Asgn | exact HQ].
  - eapply NC_Cons;
      [| same | eapply NC_Seq; [apply (IH1 (ppre c2 Q)) | apply IH2]].
    intros s [m [H1 [t [H2 HQ]]]]. exists t.
    split; [eapply E_Seq; eassumption | exact HQ].
  - eapply NC_Cons; [| same | apply (NC_If _ _ Q b c1 c2 (IH1 Q) (IH2 Q))].
    intros s [[Hb [t [Hc HQ]]] | [Hb [t [Hc HQ]]]]; exists t;
      (split; [| exact HQ]); [apply E_IfTrue | apply E_IfFalse];
      try assumption; apply bassn_false, Hb.
  - apply (NC_While _ (ppre c (ppre (CWhile b c) Q))); [apply IH | |].
    + intros s Hb HQ. exists s. split; [apply E_WhileFalse, bassn_false, Hb
                                       | exact HQ].
    + intros s Hb [m [Hc [t [Hw HQ]]]]. exists t.
      split; [eapply E_WhileTrue; eassumption | exact HQ].
  - eapply NC_Cons; [| same | apply (NC_Choice _ _ Q c1 c2 (IH1 Q) (IH2 Q))].
    intros s [[t [Hc HQ]] | [t [Hc HQ]]]; exists t;
      split; [apply E_ChoiceL | | apply E_ChoiceR |]; assumption.
  - eapply NC_Cons; [| same | apply NC_Havoc].
    intros s [n HQ]. eexists. split; [apply E_Havoc | exact HQ].
Qed.

Theorem nc_complete : forall P c Q, nc_valid P c Q -> nc P c Q.
Proof.
  intros P c Q V. eapply NC_Cons; [| same | apply nc_ppre].
  intros s [t [Hc HQ]]. exact (V s t Hc HQ).
Qed.

Theorem nc_iff_generated : forall P c Q,
    nc P c Q <->
    derivable (rules (vl_logic (NCv iact_sem)))
      (@mkTriple ICore P (enc c) Q).
Proof.
  intros P c Q. rewrite vl_theory, <- enc_cvalid, cvalid_Imp_rel. simpl.
  split; [apply nc_sound | apply nc_complete].
Qed.
