(** * Error outcomes: O'Hearn's incorrectness logic, in the cube

    O'Hearn's incorrectness logic (POPL 2020) has two kinds of outcome.
    A command either finishes normally ([ok]) or stops with an error
    ([er]), and a triple [[P] c [ok: Q] [er: E]] says that every state in
    [Q] is reached normally, and every state in [E] erroneously, by some
    run from [P].

    This file brings that logic into the cube without new metatheory:

    - [ecom]: a structural language with errors ([XError]) over any
      atomic actions; [okr] and [err] give O'Hearn's denotational
      semantics, one relation per outcome, exactly as in his paper;
    - [enc]: its translation into the core, whose states are tagged
      [Ok s] or [Err s]; an error propagates unchanged through the rest
      of the program ([err_absorb], [err_pass]);
    - [enc_osem]: the translation's runs are exactly O'Hearn's semantics;
    - [oh_iff]: in any record at the IL corner, O'Hearn's triple
      [[P] c [ok: Q] [er: E]] is the core IL triple with precondition
      [Ok P] and postcondition [Ok Q ∨ Err E];
    - O'Hearn's rules as lemmas in any such record: skip, error, atoms,
      assume, sequencing (errors short-circuit), choice, disjunction,
      consequence, iteration, and unrolling a loop to expose an error.

    Every other corner works the same way. For example, SIL triples with
    an [Err] postcondition are Ascari et al.'s sufficient incorrectness
    triples about errors, and HL triples with an [Err E] post constrain
    which errors can happen. All of it is axiom-free. *)

From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Verified Abstraction.
From LogicTransformers.Core Require Import Kernel Rules.

Inductive res (Σ : Type) : Type :=
  | Ok (s : Σ)
  | Err (s : Σ).

Arguments Ok {Σ}.
Arguments Err {Σ}.

Inductive eact (Act : Type) : Type :=
  | EAct (a : Act)
  | ERaise.

Arguments EAct {Act}.
Arguments ERaise {Act}.

Section Errors.

Context {Σ Act : Type} (act_sem : Act -> Σ -> Σ -> Prop).

(** ** The language with errors *)

Inductive ecom : Type :=
  | XSkip
  | XAct (a : Act)
  | XAssume (B : Σ -> Prop)
  | XSeq (c1 c2 : ecom)
  | XChoice (c1 c2 : ecom)
  | XStar (c : ecom)
  | XError.

(** O'Hearn's semantics: normal and erroneous outcomes. *)
Fixpoint okr (c : ecom) : Σ -> Σ -> Prop :=
  match c with
  | XSkip => fun s s' => s' = s
  | XAct a => act_sem a
  | XAssume B => fun s s' => s' = s /\ B s
  | XSeq c1 c2 => rcomp (okr c1) (okr c2)
  | XChoice c1 c2 => runion (okr c1) (okr c2)
  | XStar c => rtc (okr c)
  | XError => fun _ _ => False
  end.

Fixpoint err (c : ecom) : Σ -> Σ -> Prop :=
  match c with
  | XSkip | XAct _ | XAssume _ => fun _ _ => False
  | XSeq c1 c2 => runion (err c1) (rcomp (okr c1) (err c2))
  | XChoice c1 c2 => runion (err c1) (err c2)
  | XStar c => rcomp (rtc (okr c)) (err c)
  | XError => fun s s' => s' = s
  end.

Definition osem (c : ecom) (s : Σ) (r : res Σ) : Prop :=
  match r with
  | Ok s' => okr c s s'
  | Err s' => err c s s'
  end.

(** ** The translation into the core *)

Definition esem (e : eact Act) (r r' : res Σ) : Prop :=
  match e, r with
  | EAct a, Ok s => exists s', act_sem a s s' /\ r' = Ok s'
  | ERaise, Ok s => r' = Err s
  | _, Err s => r' = Err s
  end.

(** Tests let errors through, so an error reaches the end of the run. *)
Definition okt (B : Σ -> Prop) (r : res Σ) : Prop :=
  match r with Ok s => B s | Err _ => True end.

Fixpoint enc (c : ecom) : kcom (res Σ) (eact Act) :=
  match c with
  | XSkip => KSkip
  | XAct a => KAct (EAct a)
  | XAssume B => KAssume (okt B)
  | XSeq c1 c2 => KSeq (enc c1) (enc c2)
  | XChoice c1 c2 => KChoice (enc c1) (enc c2)
  | XStar c => KStar (enc c)
  | XError => KAct ERaise
  end.

Notation kev := (kev esem).

Lemma err_absorb : forall c s r, kev (enc c) (Err s) r -> r = Err s.
Proof.
  induction c; intros s r H; simpl in H.
  - inversion H; subst. reflexivity.
  - inversion H; subst. assumption.
  - inversion H; subst. reflexivity.
  - inversion H; subst.
    match goal with H1 : kev (enc c1) _ _ |- _ =>
      apply IHc1 in H1; subst end.
    eauto.
  - inversion H; subst; eauto.
  - remember (KStar (enc c)) as k eqn:Ek. remember (Err s) as x eqn:Ex.
    revert s Ex. induction H; inversion Ek; subst; intros s0 Ex; subst;
      [reflexivity |].
    match goal with H1 : kev (enc c) _ _ |- _ =>
      apply IHc in H1; subst end.
    exact (IHkev2 eq_refl s0 eq_refl).
  - inversion H; subst. assumption.
Qed.

Lemma err_pass : forall c s, kev (enc c) (Err s) (Err s).
Proof.
  induction c; intros s; simpl.
  - apply KE_Skip.
  - apply KE_Act. reflexivity.
  - apply KE_Assume. exact I.
  - eapply KE_Seq; [apply IHc1 | apply IHc2].
  - apply KE_ChoiceL, IHc1.
  - apply KE_StarRefl.
  - apply KE_Act. reflexivity.
Qed.

Lemma star_ok_prefix : forall c s s1 r,
    rtc (fun x y => kev (enc c) (Ok x) (Ok y)) s s1 ->
    kev (KStar (enc c)) (Ok s1) r -> kev (KStar (enc c)) (Ok s) r.
Proof.
  intros c s s1 r H. induction H as [x | x x1 x2 Hx _ IH]; intros Hr;
    [exact Hr | eapply KE_StarStep; [exact Hx | apply IH, Hr]].
Qed.

(** The translation's runs from a normal state are O'Hearn's semantics. *)
Theorem enc_osem : forall c s r, kev (enc c) (Ok s) r <-> osem c s r.
Proof.
  induction c; intros s r; simpl.
  - split.
    + intros H. inversion H; subst. reflexivity.
    + destruct r; simpl; [intros -> | intros []]; apply KE_Skip.
  - split.
    + intros H. inversion H; subst.
      match goal with H1 : esem _ _ _ |- _ =>
        destruct H1 as [s' [Ha ->]] end. exact Ha.
    + destruct r as [s'|s']; simpl; [intros Ha | intros []].
      apply KE_Act. exists s'. auto.
  - split.
    + intros H. inversion H; subst. simpl. auto.
    + destruct r as [s'|s']; simpl; [intros [-> HB] | intros []].
      apply KE_Assume. exact HB.
  - split.
    + intros H. inversion H; subst.
      match goal with H1 : kev (enc c1) _ ?y, H2 : kev (enc c2) ?y _ |- _ =>
        rename H1 into Ha; rename H2 into Hb; destruct y as [s1|s1] end.
      * apply IHc1 in Ha. apply IHc2 in Hb.
        destruct r as [s'|s']; simpl in *.
        -- exists s1. auto.
        -- right. exists s1. auto.
      * apply IHc1 in Ha. apply err_absorb in Hb. subst. simpl. left. exact Ha.
    + destruct r as [s'|s']; simpl.
      * intros [s1 [H1 H2]]. eapply KE_Seq;
          [apply (IHc1 s (Ok s1)), H1 | apply (IHc2 s1 (Ok s')), H2].
      * intros [H1 | [s1 [H1 H2]]].
        -- eapply KE_Seq; [apply (IHc1 s (Err s')), H1 | apply err_pass].
        -- eapply KE_Seq;
             [apply (IHc1 s (Ok s1)), H1 | apply (IHc2 s1 (Err s')), H2].
  - split.
    + intros H. inversion H; subst;
        match goal with H1 : kev _ (Ok s) r |- _ => rename H1 into Ha end.
      * apply IHc1 in Ha. destruct r; simpl in *; left; exact Ha.
      * apply IHc2 in Ha. destruct r; simpl in *; right; exact Ha.
    + destruct r as [s'|s']; simpl; intros [H | H];
        [apply KE_ChoiceL, (IHc1 s (Ok s')), H
        | apply KE_ChoiceR, (IHc2 s (Ok s')), H
        | apply KE_ChoiceL, (IHc1 s (Err s')), H
        | apply KE_ChoiceR, (IHc2 s (Err s')), H].
  - split.
    + intros H. remember (KStar (enc c)) as k eqn:Ek.
      remember (Ok s) as x eqn:Ex. revert s Ex.
      induction H; inversion Ek; subst; intros s0 Ex; subst.
      * apply rtc_refl.
      * destruct s1 as [s1|s1].
        -- apply IHc in H. specialize (IHkev2 eq_refl s1 eq_refl).
           destruct s2 as [s2|s2]; simpl in *.
           ++ eapply rtc_step; eassumption.
           ++ destruct IHkev2 as [m [Hm He]].
              exists m. split; [eapply rtc_step; eassumption | exact He].
        -- apply IHc in H. apply (err_absorb (XStar c)) in H0. subst. simpl.
           exists s0. split; [apply rtc_refl | exact H].
    + assert (Hok : forall x y, rtc (okr c) x y ->
                    rtc (fun a b => kev (enc c) (Ok a) (Ok b)) x y).
      { intros x y Hr. induction Hr as [x | x x1 x2 H _ IH];
          [apply rtc_refl |
           eapply rtc_step; [apply (IHc x (Ok x1)), H | exact IH]]. }
      destruct r as [s'|s']; simpl.
      * intros Hr. apply (star_ok_prefix c s s');
          [apply Hok, Hr | apply KE_StarRefl].
      * intros [s1 [Hr He]]. apply (star_ok_prefix c s s1); [apply Hok, Hr |].
        eapply KE_StarStep; [apply (IHc s1 (Err s')), He | apply KE_StarRefl].
  - split.
    + intros H. inversion H; subst.
      match goal with H1 : esem _ _ _ |- _ => simpl in H1; subst end.
      reflexivity.
    + destruct r as [s'|s']; simpl; [intros [] | intros ->].
      apply KE_Act. reflexivity.
Qed.

(** ** O'Hearn's triples *)

Definition okP (P : Σ -> Prop) (r : res Σ) : Prop :=
  match r with Ok s => P s | Err _ => False end.
Definition oker (Q E : Σ -> Prop) (r : res Σ) : Prop :=
  match r with Ok s => Q s | Err s => E s end.

(** O'Hearn's validity of [[P] c [ok: Q] [er: E]]. *)
Definition oh_valid (P : Σ -> Prop) (c : ecom) (Q E : Σ -> Prop) : Prop :=
  (forall s', Q s' -> exists s, P s /\ okr c s s') /\
  (forall s', E s' -> exists s, P s /\ err c s s').

Section Triples.

Variable V : VLogic (KLang esem) Forward Plain Under.

Definition ohprov (P : Σ -> Prop) (c : ecom) (Q E : Σ -> Prop) : Prop :=
  prov esem V (okP P) (enc c) (oker Q E).

Theorem oh_iff : forall P c Q E, ohprov P c Q E <-> oh_valid P c Q E.
Proof.
  intros P c Q E. unfold ohprov. rewrite il_iff. split.
  - intros H. split.
    + intros s' HQ.
      destruct (H (Ok s') HQ) as [[s|s] [HP Hk]]; [| contradiction].
      exists s. split; [exact HP | exact (proj1 (enc_osem c s (Ok s')) Hk)].
    + intros s' HE.
      destruct (H (Err s') HE) as [[s|s] [HP Hk]]; [| contradiction].
      exists s. split; [exact HP | exact (proj1 (enc_osem c s (Err s')) Hk)].
  - intros [HQ HE] [s'|s'] H.
    + destruct (HQ s' H) as [s [HP Hr]].
      exists (Ok s). split; [exact HP | apply (enc_osem c s (Ok s')), Hr].
    + destruct (HE s' H) as [s [HP Hr]].
      exists (Ok s). split; [exact HP | apply (enc_osem c s (Err s')), Hr].
Qed.

Definition FF : Σ -> Prop := fun _ => False.

Lemma oh_skip : forall P, ohprov P XSkip P FF.
Proof.
  intros P. apply oh_iff. split; [| intros s' []].
  intros s' HP. exists s'. split; [exact HP | reflexivity].
Qed.

Lemma oh_error : forall P, ohprov P XError FF P.
Proof.
  intros P. apply oh_iff. split; [intros s' [] |].
  intros s' HP. exists s'. split; [exact HP | reflexivity].
Qed.

Lemma oh_act : forall P a,
    ohprov P (XAct a) (fun s' => exists s, P s /\ act_sem a s s') FF.
Proof.
  intros P a. apply oh_iff. split; [| intros s' []].
  intros s' [s [HP Ha]]. exists s. auto.
Qed.

Lemma oh_assume : forall P B,
    ohprov P (XAssume B) (fun s => P s /\ B s) FF.
Proof.
  intros P B. apply oh_iff. split; [| intros s' []].
  intros s' [HP HB]. exists s'. simpl. auto.
Qed.

(** Sequencing: errors of [c1] short-circuit [c2]. *)
Lemma oh_seq : forall P R Q E1 E2 c1 c2,
    ohprov P c1 R E1 -> ohprov R c2 Q E2 ->
    ohprov P (XSeq c1 c2) Q (fun s => E1 s \/ E2 s).
Proof.
  intros P R Q E1 E2 c1 c2 H1 H2. apply oh_iff in H1, H2. apply oh_iff.
  destruct H1 as [R1 E1'], H2 as [R2 E2']. split.
  - intros s'' HQ. destruct (R2 s'' HQ) as [s' [HR H2]].
    destruct (R1 s' HR) as [s [HP H1]].
    exists s. split; [exact HP | exists s'; auto].
  - intros s' [HE | HE].
    + destruct (E1' s' HE) as [s [HP H]]. exists s. split; [exact HP |].
      left. exact H.
    + destruct (E2' s' HE) as [s1 [HR H2]].
      destruct (R1 s1 HR) as [s [HP H1]].
      exists s. split; [exact HP | right; exists s1; auto].
Qed.

Lemma oh_choice_l : forall P Q E c1 c2,
    ohprov P c1 Q E -> ohprov P (XChoice c1 c2) Q E.
Proof.
  intros P Q E c1 c2 H. apply oh_iff in H. apply oh_iff.
  destruct H as [HQ HE]. split.
  - intros s' H. destruct (HQ s' H) as [s [HP Hr]].
    exists s. split; [exact HP | left; exact Hr].
  - intros s' H. destruct (HE s' H) as [s [HP Hr]].
    exists s. split; [exact HP | left; exact Hr].
Qed.

Lemma oh_choice_r : forall P Q E c1 c2,
    ohprov P c2 Q E -> ohprov P (XChoice c1 c2) Q E.
Proof.
  intros P Q E c1 c2 H. apply oh_iff in H. apply oh_iff.
  destruct H as [HQ HE]. split.
  - intros s' H. destruct (HQ s' H) as [s [HP Hr]].
    exists s. split; [exact HP | right; exact Hr].
  - intros s' H. destruct (HE s' H) as [s [HP Hr]].
    exists s. split; [exact HP | right; exact Hr].
Qed.

Lemma oh_disj : forall P Q1 Q2 E1 E2 c,
    ohprov P c Q1 E1 -> ohprov P c Q2 E2 ->
    ohprov P c (fun s => Q1 s \/ Q2 s) (fun s => E1 s \/ E2 s).
Proof.
  intros P Q1 Q2 E1 E2 c H1 H2. apply oh_iff in H1, H2. apply oh_iff.
  destruct H1 as [A1 B1], H2 as [A2 B2].
  split; intros s' [H | H]; auto.
Qed.

Lemma oh_cons : forall P P' Q Q' E E' c,
    (forall s, P' s -> P s) -> (forall s, Q s -> Q' s) ->
    (forall s, E s -> E' s) ->
    ohprov P' c Q' E' -> ohprov P c Q E.
Proof.
  intros P P' Q Q' E E' c HP HQ HE H. apply oh_iff in H. apply oh_iff.
  destruct H as [A B]. split.
  - intros s' H. destruct (A s' (HQ s' H)) as [s [H1 H2]]. eauto.
  - intros s' H. destruct (B s' (HE s' H)) as [s [H1 H2]]. eauto.
Qed.

(** Iteration, normal outcomes: O'Hearn's iteration-indexed rule. *)
Lemma oh_star : forall (X : nat -> Σ -> Prop) c,
    (forall n, ohprov (X n) c (X (S n)) FF) ->
    ohprov (X 0) (XStar c) (fun s => exists n, X n s) FF.
Proof.
  intros X c H. apply oh_iff. split; [| intros s' []].
  assert (G : forall n s', X n s' -> exists s, X 0 s /\ rtc (okr c) s s').
  { induction n as [|n IH]; intros s' Hx.
    - exists s'. split; [exact Hx | apply rtc_refl].
    - destruct (proj1 (proj1 (oh_iff _ _ _ _) (H n)) s' Hx) as [s1 [Hx1 Hr]].
      destruct (IH s1 Hx1) as [s [Hx0 Hs]].
      exists s. split; [exact Hx0 |].
      clear -Hs Hr. induction Hs as [x | x x1 x2 Hx _ IHs].
      + apply (rtc_step _ x s' s'); [exact Hr | apply rtc_refl].
      + apply (rtc_step _ x x1 s'); [exact Hx | apply IHs, Hr]. }
  intros s' [n Hx]. exact (G n s' Hx).
Qed.

(** Unrolling: what one more iteration reaches, the loop reaches. This
    is how an error raised inside a loop is exposed. *)
Lemma oh_unroll : forall P Q E c,
    ohprov P (XSeq (XStar c) c) Q E -> ohprov P (XStar c) Q E.
Proof.
  intros P Q E c H. apply oh_iff in H. apply oh_iff.
  destruct H as [A B]. split.
  - intros s' HQ. destruct (A s' HQ) as [s [HP [s1 [H1 H2]]]].
    exists s. split; [exact HP |]. simpl.
    clear -H1 H2. induction H1 as [x | x x1 x2 Hx _ IH].
    + apply (rtc_step _ x s' s'); [exact H2 | apply rtc_refl].
    + apply (rtc_step _ x x1 s'); [exact Hx | apply IH, H2].
  - intros s' HE. destruct (B s' HE) as [s [HP [H | [s1 [H1 H2]]]]].
    + exists s. split; [exact HP | exact H].
    + exists s. split; [exact HP |]. exists s1. split; [exact H1 | exact H2].
Qed.

End Triples.

End Errors.
