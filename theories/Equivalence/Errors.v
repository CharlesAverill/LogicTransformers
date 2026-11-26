(** * O'Hearn's ok/error triples: his rules and the generated logic

    [ohl P c Q E] is O'Hearn's incorrectness logic (POPL 2020) with both
    outcomes, [[P] c [ok: Q] [er: E]], over the language with errors of
    [Core.Errors], for any atomic actions. Its rules: the empty
    postcondition, [skip], [error], atoms, [assume], sequencing (errors
    short-circuit), either branch of choice, disjunction, consequence,
    iterating zero times, unrolling, and the iteration-indexed variant.

    [ohl_sound], [ohl_complete]: sound and complete for O'Hearn's
    validity (Cook's argument with the strongest postcondition of each
    outcome). [ohl_iff_generated]: it proves exactly what the generated
    incorrectness logic proves of the translated program. *)

From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Verified Abstraction.
From LogicTransformers.Core Require Import Kernel Rules Errors.
From LogicTransformers.Examples Require Import Common.

Section OHL.

Context {Σ Act : Type} (act_sem : Act -> Σ -> Σ -> Prop).

Notation ecom := (@ecom Σ Act).
Notation okr := (okr act_sem).
Notation err := (err act_sem).

Inductive ohl : (Σ -> Prop) -> ecom -> (Σ -> Prop) -> (Σ -> Prop) -> Prop :=
  | OH_Empty : forall P c, ohl P c (fun _ => False) (fun _ => False)
  | OH_Skip : forall P, ohl P XSkip P (fun _ => False)
  | OH_Error : forall P, ohl P XError (fun _ => False) P
  | OH_Act : forall P a,
      ohl P (XAct a) (fun s' => exists s, P s /\ act_sem a s s')
          (fun _ => False)
  | OH_Assume : forall P B,
      ohl P (XAssume B) (fun s => P s /\ B s) (fun _ => False)
  | OH_Seq : forall P R Q E1 E2 c1 c2,
      ohl P c1 R E1 -> ohl R c2 Q E2 ->
      ohl P (XSeq c1 c2) Q (fun s => E1 s \/ E2 s)
  | OH_ChoiceL : forall P Q E c1 c2, ohl P c1 Q E -> ohl P (XChoice c1 c2) Q E
  | OH_ChoiceR : forall P Q E c1 c2, ohl P c2 Q E -> ohl P (XChoice c1 c2) Q E
  | OH_Disj : forall P Q1 Q2 E1 E2 c,
      ohl P c Q1 E1 -> ohl P c Q2 E2 ->
      ohl P c (fun s => Q1 s \/ Q2 s) (fun s => E1 s \/ E2 s)
  | OH_Cons : forall P P' Q Q' E E' c,
      (forall s, P' s -> P s) -> (forall s, Q s -> Q' s) ->
      (forall s, E s -> E' s) -> ohl P' c Q' E' -> ohl P c Q E
  | OH_IterZero : forall P c, ohl P (XStar c) P (fun _ => False)
  | OH_Unroll : forall P Q E c,
      ohl P (XSeq (XStar c) c) Q E -> ohl P (XStar c) Q E
  | OH_Variant : forall (X : nat -> Σ -> Prop) c,
      (forall n, ohl (X n) c (X (S n)) (fun _ => False)) ->
      ohl (X 0) (XStar c) (fun s => exists n, X n s) (fun _ => False).

Notation V := (ILv (esem act_sem)).
Notation ohprov := (ohprov act_sem V).

Theorem ohl_sound : forall P c Q E, ohl P c Q E -> oh_valid act_sem P c Q E.
Proof.
  intros P c Q E H. apply (oh_iff act_sem V). induction H.
  - apply (oh_iff act_sem V). split; intros _ [].
  - apply oh_skip.
  - apply oh_error.
  - apply oh_act.
  - apply oh_assume.
  - eapply oh_seq; eassumption.
  - apply oh_choice_l; assumption.
  - apply oh_choice_r; assumption.
  - apply oh_disj; assumption.
  - eapply oh_cons; eassumption.
  - apply (oh_iff act_sem V). split; [| intros _ []].
    intros s' HP. exists s'. split; [exact HP | apply rtc_refl].
  - apply oh_unroll; assumption.
  - apply oh_star; assumption.
Qed.

(** ** Completeness *)

Definition spo (c : ecom) (P : Σ -> Prop) : Σ -> Prop :=
  fun s' => exists s, P s /\ okr c s s'.
Definition spe (c : ecom) (P : Σ -> Prop) : Σ -> Prop :=
  fun s' => exists s, P s /\ err c s s'.

Fixpoint oiter (c : ecom) (P : Σ -> Prop) (n : nat) : Σ -> Prop :=
  match n with 0 => P | S n => spo c (oiter c P n) end.

Lemma rtc_oiter : forall c s s', rtc (okr c) s s' ->
    forall P n, oiter c P n s -> exists m, oiter c P m s'.
Proof.
  intros c s s' H. induction H; intros P n Hn; [eauto |].
  apply (IHrtc P (S n)). exists s. split; assumption.
Qed.

Lemma oiter_rtc : forall c P n s', oiter c P n s' ->
    exists s, P s /\ rtc (okr c) s s'.
Proof.
  intros c P n. induction n as [| n IH]; intros s' H.
  - exists s'. split; [exact H | apply rtc_refl].
  - destruct H as [s1 [H1 Hc]]. destruct (IH s1 H1) as [s [HP Hr]].
    exists s. split; [exact HP |].
    clear -Hr Hc. induction Hr.
    + eapply rtc_step; [exact Hc | apply rtc_refl].
    + eapply rtc_step; [eassumption | apply IHHr, Hc].
Qed.

Ltac same := intros ? H; exact H.

Lemma ohl_sp : forall c P, ohl P c (spo c P) (spe c P).
Proof.
  induction c as [| a | B | c1 IH1 c2 IH2 | c1 IH1 c2 IH2 | c IH |];
    intros P.
  - eapply OH_Cons; [same | | | apply OH_Skip].
    + intros s' [s [HP E]]. simpl in E. subst. exact HP.
    + intros s' [s [_ []]].
  - eapply OH_Cons; [same | | | apply OH_Act]; [same |].
    intros s' [s [_ []]].
  - eapply OH_Cons; [same | | | apply OH_Assume].
    + intros s' [s [HP [E HB]]]. subst. split; assumption.
    + intros s' [s [_ []]].
  - eapply OH_Cons; [same | | | eapply OH_Seq; [apply IH1 | apply IH2]].
    + intros s'' [s [HP [s' [H1 H2]]]].
      exists s'. split; [exists s; split |]; assumption.
    + intros s' [s [HP [He | [s1 [H1 H2]]]]].
      * left. exists s. split; assumption.
      * right. exists s1. split; [exists s; split |]; assumption.
  - eapply OH_Cons;
      [| | | apply (OH_Disj P (spo c1 P) (spo c2 P) (spe c1 P) (spe c2 P)
                           (XChoice c1 c2));
             [apply OH_ChoiceL, IH1 | apply OH_ChoiceR, IH2]];
      [same | |].
    + intros s' [s [HP [H | H]]]; [left | right]; exists s; split; assumption.
    + intros s' [s [HP [H | H]]]; [left | right]; exists s; split; assumption.
  - (* iteration: the variant for normal outcomes, unrolling for errors *)
    set (X := oiter c P).
    assert (Hv : ohl P (XStar c) (fun s => exists n, X n s) (fun _ => False)).
    { apply (OH_Variant X c). intros n.
      eapply OH_Cons; [same | same | intros ? [] | apply IH]. }
    assert (Hu : ohl P (XStar c) (spo c (fun s => exists n, X n s))
                   (fun s => False \/ spe c (fun s => exists n, X n s) s)).
    { apply OH_Unroll. eapply OH_Seq; [exact Hv | apply IH]. }
    eapply OH_Cons; [| | | exact (OH_Disj _ _ _ _ _ _ Hv Hu)]; [same | |].
    + intros s' [s [HP Hr]]. left. exact (rtc_oiter c s s' Hr P 0 HP).
    + intros s' [s [HP [s1 [Hr He]]]]. right. right.
      exists s1. split; [exact (rtc_oiter c s s1 Hr P 0 HP) | exact He].
  - eapply OH_Cons; [same | | | apply OH_Error].
    + intros s' [s [_ []]].
    + intros s' [s [HP E]]. simpl in E. subst. exact HP.
Qed.

Theorem ohl_complete : forall P c Q E,
    oh_valid act_sem P c Q E -> ohl P c Q E.
Proof.
  intros P c Q E [VQ VE]. eapply OH_Cons; [same | | | apply ohl_sp].
  - intros s' HQ. exact (VQ s' HQ).
  - intros s' HE. exact (VE s' HE).
Qed.

Theorem ohl_iff_generated : forall P c Q E, ohl P c Q E <-> ohprov P c Q E.
Proof.
  intros P c Q E. rewrite (oh_iff act_sem V).
  split; [apply ohl_sound | apply ohl_complete].
Qed.

End OHL.
