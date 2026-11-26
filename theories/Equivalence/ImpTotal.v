(** * Total correctness for Imp: the textbook rules and the generated logic

    [tc P c Q] is total-correctness Hoare logic for Imp: from every
    state in [P], every run of [c] terminates, in [Q]. Its rules are the
    partial-correctness ones with a different loop rule, in the style of
    Apt and of Cousot's well-founded variants: an invariant [I] and a
    well-founded relation [R] such that one iteration from a state [s0]
    re-establishes [I] and moves [R]-below [s0]. Because Imp has havoc
    (unbounded nondeterminism), the variant must range over a general
    well-founded relation, not the naturals.

    [tc_sound], [tc_complete]: sound and complete for total correctness.
    Completeness takes as variant "one more iteration of the body", which
    is well-founded because the loop cannot diverge; building an infinite
    run otherwise uses [classic]. [tc_iff_generated]: it proves exactly
    what the generated nontermination-aware Hoare logic
    ([Examples.Common.HLbv] for Imp's atoms) proves of the encoded
    program, with ⊥ excluded from the postcondition. *)

From Stdlib Require Import Classical.
From LogicTransformers.Imp Require Import Syntax BigStep Diverge LangBot.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Relational Verified.
From LogicTransformers.Core Require Import Kernel KernelBot ImpCore ImpCoreBot.
From LogicTransformers.Imp Require Import Hoare.
From LogicTransformers.Examples Require Import Common.

Inductive tc : assertion -> com -> assertion -> Prop :=
  | TC_Skip : forall P, tc P CSkip P
  | TC_Asgn : forall Q x a, tc (assn_sub x a Q) (CAsgn x a) Q
  | TC_Havoc : forall Q x,
      tc (fun st => forall n, Q (update st x n)) (CHavoc x) Q
  | TC_Seq : forall P R Q c1 c2, tc P c1 R -> tc R c2 Q -> tc P (CSeq c1 c2) Q
  | TC_If : forall P Q b c1 c2,
      tc (fun st => P st /\ bassn b st) c1 Q ->
      tc (fun st => P st /\ ~ bassn b st) c2 Q -> tc P (CIf b c1 c2) Q
  | TC_Choice : forall P Q c1 c2,
      tc P c1 Q -> tc P c2 Q -> tc P (CChoice c1 c2) Q
  | TC_While : forall (I : assertion) (R : state -> state -> Prop) b c,
      well_founded R ->
      (forall st0, tc (fun st => I st /\ bassn b st /\ st = st0) c
                      (fun st => I st /\ R st st0)) ->
      tc I (CWhile b c) (fun st => I st /\ ~ bassn b st)
  | TC_Cons : forall P P' Q Q' c,
      P ->> P' -> Q' ->> Q -> tc P' c Q' -> tc P c Q.

Definition tc_valid (P : assertion) (c : com) (Q : assertion) : Prop :=
  forall st, P st -> (forall st', ceval c st st' -> Q st') /\ ~ diverges c st.

(** ** Soundness *)

Lemma while_sound : forall (I : assertion) R b c, well_founded R ->
    (forall st0, tc_valid (fun st => I st /\ bassn b st /\ st = st0) c
                          (fun st => I st /\ R st st0)) ->
    tc_valid I (CWhile b c) (fun st => I st /\ ~ bassn b st).
Proof.
  intros I R b c Hwf H st HI. split.
  - intros st' Hc. remember (CWhile b c) as w eqn:Ew.
    induction Hc; inversion Ew; subst.
    + split; [exact HI | apply bassn_false', H0].
    + apply IHHc2; [| reflexivity].
      exact (proj1 (proj1 (H st st (conj HI (conj H0 eq_refl))) _ Hc1)).
  - induction (Hwf st) as [st _ IH]. intros Hd.
    inversion Hd as [| | | | ? ? ? Hb Hdc | ? ? ? st1 Hb Hc Hdw | |]; subst.
    + exact (proj2 (H st st (conj HI (conj Hb eq_refl))) Hdc).
    + destruct (proj1 (H st st (conj HI (conj Hb eq_refl))) _ Hc) as [HI1 HR].
      exact (IH st1 HR HI1 Hdw).
Qed.

Ltac bv := match goal with H : beval _ _ = _ |- _ => exact H end.

Theorem tc_sound : forall P c Q, tc P c Q -> tc_valid P c Q.
Proof.
  intros P c Q H. induction H; intros st HP.
  - split; [intros st' Hc; inversion Hc; subst; exact HP
           | apply diverges_skip].
  - split; [intros st' Hc; inversion Hc; subst; exact HP
           | apply diverges_asgn].
  - split; [intros st' Hc; inversion Hc; subst; apply HP
           | apply diverges_havoc].
  - destruct (IHtc1 st HP) as [K1 D1]. split.
    + intros st'' Hc. inversion Hc; subst.
      eapply (proj1 (IHtc2 _ (K1 _ ltac:(eassumption)))); eassumption.
    + intros Hd. inversion Hd; subst; [contradiction |].
      eapply (proj2 (IHtc2 _ (K1 _ ltac:(eassumption)))); eassumption.
  - split.
    + intros st' Hc. inversion Hc; subst.
      * eapply (proj1 (IHtc1 st (conj HP ltac:(bv)))); eassumption.
      * eapply (proj1 (IHtc2 st (conj HP (bassn_false' _ _
                 ltac:(bv))))); eassumption.
    + intros Hd. inversion Hd; subst.
      * eapply (proj2 (IHtc1 st (conj HP ltac:(bv)))); eassumption.
      * eapply (proj2 (IHtc2 st (conj HP (bassn_false' _ _
                 ltac:(bv))))); eassumption.
  - split.
    + intros st' Hc. inversion Hc; subst;
        [eapply (proj1 (IHtc1 st HP)) | eapply (proj1 (IHtc2 st HP))];
        eassumption.
    + intros Hd. inversion Hd; subst;
        [eapply (proj2 (IHtc1 st HP)) | eapply (proj2 (IHtc2 st HP))];
        eassumption.
  - apply (while_sound I R b c H H1 st HP).
  - destruct (IHtc st (H st HP)) as [K D].
    split; [intros st' Hc; apply H0, K, Hc | exact D].
Qed.

(** ** Completeness *)

Definition wpt (c : com) (Q : assertion) : assertion :=
  fun st => (forall st', ceval c st st' -> Q st') /\ ~ diverges c st.

(** From a state that is not well-founded for "one more iteration", the
    loop runs forever. *)
Lemma not_acc_diverges : forall b c (I : assertion) st,
    ~ Acc (fun st1 st0 => I st0 /\ bassn b st0 /\ ceval c st0 st1) st ->
    diverges (CWhile b c) st.
Proof.
  intros b c I. cofix CH. intros st Hn.
  assert (Hx : exists st1, (I st /\ bassn b st /\ ceval c st st1) /\
     ~ Acc (fun st1 st0 => I st0 /\ bassn b st0 /\ ceval c st0 st1) st1).
  { apply NNPP. intros Hno. apply Hn. constructor. intros y Hy.
    apply NNPP. intros Hy'. apply Hno. exists y. auto. }
  destruct Hx as [st1 [[_ [Hb Hc]] Hn1]].
  exact (Dv_WhileIter b c st st1 Hb Hc (CH st1 Hn1)).
Qed.

Lemma tc_wpt : forall c Q, tc (wpt c Q) c Q.
Proof.
  induction c as [| x a | c1 IH1 c2 IH2 | b c1 IH1 c2 IH2 | b c IH
                  | c1 IH1 c2 IH2 | x]; intros Q.
  - eapply TC_Cons; [| | apply TC_Skip]; [| intros st H; exact H].
    intros st [K _]. apply K, E_Skip.
  - eapply TC_Cons; [| | apply TC_Asgn]; [| intros st H; exact H].
    intros st [K _]. apply K, E_Asgn.
  - eapply TC_Cons; [| | eapply TC_Seq; [apply (IH1 (wpt c2 Q)) | apply IH2]];
      [| intros st H; exact H].
    intros st [K D]. split.
    + intros st' H1. split.
      * intros st'' H2. apply K. eapply E_Seq; eassumption.
      * intros Hd. apply D. eapply Dv_SeqR; eassumption.
    + intros Hd. apply D. apply Dv_SeqL, Hd.
  - apply TC_If.
    + eapply TC_Cons; [| | apply IH1]; [| intros st H; exact H].
      intros st [[K D] Hb]. split.
      * intros st' Hc. apply K, E_IfTrue; assumption.
      * intros Hd. apply D, Dv_IfTrue; assumption.
    + eapply TC_Cons; [| | apply IH2]; [| intros st H; exact H].
      intros st [[K D] Hb]. apply bassn_false in Hb. split.
      * intros st' Hc. apply K, E_IfFalse; assumption.
      * intros Hd. apply D, Dv_IfFalse; assumption.
  - set (I := wpt (CWhile b c) Q).
    set (R := fun st1 st0 => I st0 /\ bassn b st0 /\ ceval c st0 st1).
    eapply TC_Cons; [| | apply (TC_While I R b c)];
      [intros st H; exact H | |  |].
    + intros st [[K _] Hn]. apply K, E_WhileFalse, bassn_false, Hn.
    + intros st. destruct (classic (Acc R st)) as [A | A]; [exact A |].
      destruct (classic (I st)) as [HI | HI].
      * exfalso. exact (proj2 HI (not_acc_diverges b c I st A)).
      * constructor. intros y [HI' _]. contradiction.
    + intros st0. eapply TC_Cons; [| | apply IH]; [| intros st H; exact H].
      intros st [[K D] [Hb ->]]. split.
      * intros st1 Hc. split; [split |].
        -- intros st' Hw. apply K. eapply E_WhileTrue; eassumption.
        -- intros Hd. apply D. eapply Dv_WhileIter; eassumption.
        -- split; [split; assumption | split; assumption].
      * intros Hd. apply D, Dv_WhileBody; assumption.
  - apply TC_Choice.
    + eapply TC_Cons; [| | apply IH1]; [| intros st H; exact H].
      intros st [K D]. split.
      * intros st' Hc. apply K, E_ChoiceL, Hc.
      * intros Hd. apply D, Dv_ChoiceL, Hd.
    + eapply TC_Cons; [| | apply IH2]; [| intros st H; exact H].
      intros st [K D]. split.
      * intros st' Hc. apply K, E_ChoiceR, Hc.
      * intros Hd. apply D, Dv_ChoiceR, Hd.
  - eapply TC_Cons; [| | apply TC_Havoc]; [| intros st H; exact H].
    intros st [K _] n. apply K, E_Havoc.
Qed.

Theorem tc_complete : forall P c Q, tc_valid P c Q -> tc P c Q.
Proof.
  intros P c Q V. eapply TC_Cons; [| | apply tc_wpt];
    [| intros st H; exact H].
  intros st HP. exact (V st HP).
Qed.

(** ** Against the generated logic *)

Definition someP (P : assertion) (o : option state) : Prop :=
  match o with Some s => P s | None => False end.

Lemma tc_valid_cvalid : forall P c Q,
    tc_valid P c Q <->
    cvalid Forward Plain Over (@mkTriple ImpBot (someP P) c (someP Q)).
Proof.
  intros P c Q. rewrite cvalid_cvr. simpl. split.
  - intros V [s|] [s'|] HP Hs; simpl in *; try contradiction.
    + exact (proj1 (V s HP) s' Hs).
    + exact (proj2 (V s HP) Hs).
  - intros V s HP. split.
    + intros s' Hc. exact (V (Some s) (Some s') HP Hc).
    + intros Hd. exact (V (Some s) None HP Hd).
Qed.

Theorem tc_iff_generated : forall P c Q,
    tc P c Q <->
    derivable (rules (vl_logic (HLbv iact_sem)))
      (@mkTriple (KLangB iact_sem) (someP P) (enc c) (someP Q)).
Proof.
  intros P c Q. rewrite vl_theory, <- enc_cvalid_bot, <- tc_valid_cvalid.
  split; [apply tc_sound | apply tc_complete].
Qed.
