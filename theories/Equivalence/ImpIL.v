(** * Incorrectness logic for Imp: O'Hearn's rules and the generated logic

    [ohil] is O'Hearn's incorrectness logic (POPL 2020) for Imp,
    without error outcomes: [[P] c [Q]] says every state in [Q] is
    reached by a run of [c] from a state in [P]. Its rules:
    - the empty postcondition, [skip], disjunction, consequence (pre
      weakened, post strengthened);
    - forward assignment [[P] x := a [∃x'. P[x'/x] ∧ x = a[x'/x]]], and
      havoc [[P] x := * [∃x'. P[x'/x]]];
    - sequencing, either branch of [if] and of choice;
    - [while] by unrolling, and by the backward variant: if
      [[X n ∧ b] c [X (n+1)]] for every [n], then
      [[X 0] while b c [∃n. X n ∧ ¬b]].

    [ohil_sound], [ohil_complete]: sound and complete (Cook's argument
    with strongest postconditions). [ohil_iff_generated]: it proves
    exactly the triples that the generated incorrectness logic
    ([Examples.Common.ILv] for Imp's atoms) proves of the encoded
    program.

    The forward rules state the pre-state through an update of the
    post-state, so completeness uses [functional_extensionality]; the
    generated logic uses [classic]. *)

From Stdlib Require Import String FunctionalExtensionality.
From LogicTransformers.Imp Require Import Syntax BigStep Lang.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Verified.
From LogicTransformers.Core Require Import Kernel ImpCore.
From LogicTransformers.Imp Require Import Hoare.
From LogicTransformers.Examples Require Import Common.

Lemma update_shadow : forall st x v w,
    update (update st x v) x w = update st x w.
Proof.
  intros. apply functional_extensionality. intros y. unfold update.
  destruct (String.eqb x y); reflexivity.
Qed.

Lemma update_same : forall st x, update st x (st x) = st.
Proof.
  intros. apply functional_extensionality. intros y. unfold update.
  destruct (String.eqb_spec x y); subst; reflexivity.
Qed.

(** ** The rules *)

Inductive ohil : assertion -> com -> assertion -> Prop :=
  | OI_Empty : forall P c, ohil P c (fun _ => False)
  | OI_Skip : forall P, ohil P CSkip P
  | OI_Asgn : forall P x a,
      ohil P (CAsgn x a)
        (fun st => exists v, P (update st x v) /\
                             st x = aeval (update st x v) a)
  | OI_Havoc : forall P x,
      ohil P (CHavoc x) (fun st => exists v, P (update st x v))
  | OI_Seq : forall P R Q c1 c2,
      ohil P c1 R -> ohil R c2 Q -> ohil P (CSeq c1 c2) Q
  | OI_IfT : forall P Q b c1 c2,
      ohil (fun st => P st /\ bassn b st) c1 Q -> ohil P (CIf b c1 c2) Q
  | OI_IfF : forall P Q b c1 c2,
      ohil (fun st => P st /\ ~ bassn b st) c2 Q -> ohil P (CIf b c1 c2) Q
  | OI_ChoiceL : forall P Q c1 c2, ohil P c1 Q -> ohil P (CChoice c1 c2) Q
  | OI_ChoiceR : forall P Q c1 c2, ohil P c2 Q -> ohil P (CChoice c1 c2) Q
  | OI_Unroll : forall P Q b c,
      ohil P (CIf b (CSeq c (CWhile b c)) CSkip) Q ->
      ohil P (CWhile b c) Q
  | OI_Variant : forall (X : nat -> assertion) b c,
      (forall n, ohil (fun st => X n st /\ bassn b st) c (X (S n))) ->
      ohil (X 0) (CWhile b c)
           (fun st => exists n, X n st /\ ~ bassn b st)
  | OI_Disj : forall P1 Q1 P2 Q2 c,
      ohil P1 c Q1 -> ohil P2 c Q2 ->
      ohil (fun st => P1 st \/ P2 st) c (fun st => Q1 st \/ Q2 st)
  | OI_Cons : forall P P' Q Q' c,
      P ->> P' -> Q' ->> Q -> ohil P c Q -> ohil P' c Q'.

Definition il_valid (P : assertion) (c : com) (Q : assertion) : Prop :=
  forall st', Q st' -> exists st, P st /\ ceval c st st'.

(** ** Soundness *)

(** Iterations of a loop body whose guard holds. *)
Inductive biter (b : bexp) (c : com) : state -> state -> Prop :=
  | BI_Refl : forall st, biter b c st st
  | BI_Step : forall st st1 st2,
      bassn b st -> ceval c st st1 -> biter b c st1 st2 -> biter b c st st2.

Lemma biter_snoc : forall b c st st1 st2,
    biter b c st st1 -> bassn b st1 -> ceval c st1 st2 -> biter b c st st2.
Proof.
  intros b c st st1 st2 H. induction H; intros Hb Hc.
  - eapply BI_Step; [exact Hb | exact Hc | apply BI_Refl].
  - eapply BI_Step; [eassumption | eassumption | apply IHbiter; assumption].
Qed.

Lemma biter_while : forall b c st st',
    biter b c st st' -> ~ bassn b st' -> ceval (CWhile b c) st st'.
Proof.
  intros b c st st' H Hn. induction H.
  - apply E_WhileFalse, bassn_false, Hn.
  - eapply E_WhileTrue; [exact H | exact H0 | apply IHbiter, Hn].
Qed.

Lemma while_unroll : forall b c st st',
    ceval (CIf b (CSeq c (CWhile b c)) CSkip) st st' ->
    ceval (CWhile b c) st st'.
Proof.
  intros b c st st' H. inversion H; subst.
  - inversion H6; subst. eapply E_WhileTrue; eassumption.
  - inversion H6; subst. apply E_WhileFalse. assumption.
Qed.

Theorem ohil_sound : forall P c Q, ohil P c Q -> il_valid P c Q.
Proof.
  intros P c Q H. induction H; intros st' HQ.
  - contradiction.
  - exists st'. split; [exact HQ | apply E_Skip].
  - destruct HQ as [v [HP He]]. exists (update st' x v).
    split; [exact HP |].
    replace st' with (update (update st' x v) x
                        (aeval (update st' x v) a)) at 2.
    + apply E_Asgn.
    + rewrite update_shadow, <- He. apply update_same.
  - destruct HQ as [v HP]. exists (update st' x v). split; [exact HP |].
    replace st' with (update (update st' x v) x (st' x)) at 2.
    + apply E_Havoc.
    + rewrite update_shadow. apply update_same.
  - destruct (IHohil2 st' HQ) as [st1 [HR H2]].
    destruct (IHohil1 st1 HR) as [st [HP H1]].
    exists st. split; [exact HP | eapply E_Seq; eassumption].
  - destruct (IHohil st' HQ) as [st [[HP Hb] Hc]].
    exists st. split; [exact HP | apply E_IfTrue; assumption].
  - destruct (IHohil st' HQ) as [st [[HP Hb] Hc]].
    exists st. split; [exact HP | apply E_IfFalse; [|assumption]].
    apply bassn_false, Hb.
  - destruct (IHohil st' HQ) as [st [HP Hc]].
    exists st. split; [exact HP | apply E_ChoiceL, Hc].
  - destruct (IHohil st' HQ) as [st [HP Hc]].
    exists st. split; [exact HP | apply E_ChoiceR, Hc].
  - destruct (IHohil st' HQ) as [st [HP Hc]].
    exists st. split; [exact HP | apply while_unroll, Hc].
  - destruct HQ as [n [Hx Hn]].
    assert (G : forall n st', X n st' -> exists st, X 0 st /\ biter b c st st').
    { induction n0 as [| n0 IHn]; intros st1 Hx1.
      - exists st1. split; [exact Hx1 | apply BI_Refl].
      - destruct (H0 n0 st1 Hx1) as [st2 [[Hx2 Hb] Hc]].
        destruct (IHn st2 Hx2) as [st [Hx0 Hi]].
        exists st. split; [exact Hx0 | eapply biter_snoc; eassumption]. }
    destruct (G n st' Hx) as [st [Hx0 Hi]].
    exists st. split; [exact Hx0 | apply biter_while; assumption].
  - destruct HQ as [HQ | HQ];
      [destruct (IHohil1 st' HQ) as [st [HP Hc]]
      | destruct (IHohil2 st' HQ) as [st [HP Hc]]]; eauto.
  - destruct (IHohil st' (H0 st' HQ)) as [st [HP Hc]].
    exists st. split; [apply H, HP | exact Hc].
Qed.

(** ** Completeness *)

Definition sp (c : com) (P : assertion) : assertion :=
  fun st' => exists st, P st /\ ceval c st st'.

Fixpoint witer (b : bexp) (c : com) (P : assertion) (n : nat) : assertion :=
  match n with
  | 0 => P
  | S n => sp c (fun st => witer b c P n st /\ bassn b st)
  end.

Lemma while_witer : forall b c st st', ceval (CWhile b c) st st' ->
    forall P n, witer b c P n st ->
    exists m, witer b c P m st' /\ ~ bassn b st'.
Proof.
  intros b c st st' H. remember (CWhile b c) as w eqn:Ew.
  induction H; inversion Ew; subst; intros P n Hw.
  - exists n. split; [exact Hw | apply bassn_false', H].
  - apply (IHceval2 eq_refl P (S n)). exists st. split; [split |]; assumption.
Qed.

Lemma ohil_sp : forall c P, ohil P c (sp c P).
Proof.
  induction c as [| x a | c1 IH1 c2 IH2 | b c1 IH1 c2 IH2 | b c IH
                  | c1 IH1 c2 IH2 | x]; intros P.
  - eapply OI_Cons; [| | apply OI_Skip]; [intros st H; exact H |].
    intros st' [st [HP Hc]]. inversion Hc; subst. exact HP.
  - eapply OI_Cons; [| | apply OI_Asgn]; [intros st H; exact H |].
    intros st' [st [HP Hc]]. inversion Hc; subst.
    exists (st x). rewrite update_shadow, update_same, update_eq.
    split; [exact HP | reflexivity].
  - eapply OI_Seq; [apply IH1 |].
    eapply OI_Cons; [| | apply IH2]; [intros st H; exact H |].
    intros st'' [st [HP Hc]]. inversion Hc; subst.
    exists st'. split; [exists st; split |]; assumption.
  - eapply OI_Cons;
      [| | apply (OI_Disj P (sp c1 (fun st => P st /\ bassn b st))
                          P (sp c2 (fun st => P st /\ ~ bassn b st))
                          (CIf b c1 c2));
           [apply OI_IfT, IH1 | apply OI_IfF, IH2]];
      [intros st [H | H]; exact H |].
    intros st' [st [HP Hc]]. inversion Hc; subst.
    + left. exists st. split; [split |]; assumption.
    + right. exists st. split; [split; [| apply bassn_false'] |]; assumption.
  - eapply OI_Cons; [| | apply (OI_Variant (witer b c P))].
    + intros st H. exact H.
    + intros st' [st [HP Hc]]. exact (while_witer b c st st' Hc P 0 HP).
    + intros n. apply IH.
  - eapply OI_Cons;
      [| | apply (OI_Disj P (sp c1 P) P (sp c2 P) (CChoice c1 c2));
           [apply OI_ChoiceL, IH1 | apply OI_ChoiceR, IH2]];
      [intros st [H | H]; exact H |].
    intros st' [st [HP Hc]]. inversion Hc; subst.
    + left. exists st. split; assumption.
    + right. exists st. split; assumption.
  - eapply OI_Cons; [| | apply OI_Havoc]; [intros st H; exact H |].
    intros st' [st [HP Hc]]. inversion Hc; subst.
    exists (st x). rewrite update_shadow, update_same. exact HP.
Qed.

Theorem ohil_complete : forall P c Q, il_valid P c Q -> ohil P c Q.
Proof.
  intros P c Q V. eapply OI_Cons; [| | apply ohil_sp];
    [intros st H; exact H |].
  intros st' HQ. exact (V st' HQ).
Qed.

(** ** Against the generated logic *)

Theorem ohil_iff_generated : forall P c Q,
    ohil P c Q <->
    derivable (rules (vl_logic (ILv iact_sem)))
      (@mkTriple ICore P (enc c) Q).
Proof.
  intros P c Q. rewrite vl_theory, <- enc_cvalid, cvalid_Imp_rel. simpl.
  split; [apply ohil_sound | apply ohil_complete].
Qed.
