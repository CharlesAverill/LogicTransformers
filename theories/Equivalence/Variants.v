(** * Natural-number variants are incomplete under unbounded nondeterminism

    Cousot notes that variant functions into ω are "sound but
    incomplete" for total correctness when nondeterminism is unbounded,
    and that well-founded sets restore completeness. This file proves
    both halves for Imp.

    [tcn] is total-correctness Hoare logic with the textbook loop rule
    over natural-number variants. [tcn_sound]: it is sound (each
    derivation is one in [ImpTotal.tc]).

    The loop [wloop]: while the flag [f] is set, havoc [x] and clear the
    flag; otherwise count [x] down to zero. From [f = 1] it always
    terminates ([wloop_total], by a lexicographic well-founded variant
    in [ImpTotal.tc]), but the number of iterations is unbounded from the
    start state, so no natural-number variant exists
    ([wloop_not_tcn]). Constructive. *)

From Stdlib Require Import String Arith Lia Wellfounded Relations.
From LogicTransformers.Imp Require Import Syntax BigStep Diverge.
From LogicTransformers.Imp Require Import Hoare.
From LogicTransformers.Equivalence Require Import ImpTotal.

Inductive tcn : assertion -> com -> assertion -> Prop :=
  | TN_Skip : forall P, tcn P CSkip P
  | TN_Asgn : forall Q x a, tcn (assn_sub x a Q) (CAsgn x a) Q
  | TN_Havoc : forall Q x,
      tcn (fun st => forall n, Q (update st x n)) (CHavoc x) Q
  | TN_Seq : forall P R Q c1 c2,
      tcn P c1 R -> tcn R c2 Q -> tcn P (CSeq c1 c2) Q
  | TN_If : forall P Q b c1 c2,
      tcn (fun st => P st /\ bassn b st) c1 Q ->
      tcn (fun st => P st /\ ~ bassn b st) c2 Q -> tcn P (CIf b c1 c2) Q
  | TN_Choice : forall P Q c1 c2,
      tcn P c1 Q -> tcn P c2 Q -> tcn P (CChoice c1 c2) Q
  | TN_While : forall (I : assertion) (m : state -> nat) b c,
      (forall n0, tcn (fun st => I st /\ bassn b st /\ m st = n0) c
                      (fun st => I st /\ m st < n0)) ->
      tcn I (CWhile b c) (fun st => I st /\ ~ bassn b st)
  | TN_Cons : forall P P' Q Q' c,
      P ->> P' -> Q' ->> Q -> tcn P' c Q' -> tcn P c Q.

(** ** Soundness: every natural-number variant is a well-founded one *)

Lemma tcn_tc : forall P c Q, tcn P c Q -> tc P c Q.
Proof.
  intros P c Q H. induction H.
  - apply TC_Skip.
  - apply TC_Asgn.
  - apply TC_Havoc.
  - eapply TC_Seq; eassumption.
  - apply TC_If; assumption.
  - apply TC_Choice; assumption.
  - apply (TC_While I (fun s1 s0 => m s1 < m s0)).
    + apply (wf_inverse_image _ _ lt m), lt_wf.
    + intros st0. eapply TC_Cons; [| | apply (H0 (m st0))].
      * intros st [Hi [Hb ->]]. auto.
      * intros st [Hi Hm]. auto.
  - eapply TC_Cons; eassumption.
Qed.

Theorem tcn_sound : forall P c Q, tcn P c Q -> tc_valid P c Q.
Proof. intros. apply tc_sound, tcn_tc. assumption. Qed.

(** ** The loop *)

Local Open Scope string_scope.
Local Notation X := "x".
Local Notation Fl := "f".

Definition wguard : bexp :=
  BNot (BAnd (BEq (AVar X) (ANum 0)) (BEq (AVar Fl) (ANum 0))).
Definition wbody : com :=
  CIf (BEq (AVar Fl) (ANum 1))
      (CSeq (CHavoc X) (CAsgn Fl (ANum 0)))
      (CAsgn X (AMinus (AVar X) (ANum 1))).
Definition wloop : com := CWhile wguard wbody.

Ltac upd := repeat (rewrite ?update_eq; rewrite ?update_neq by discriminate).

(** It terminates, by the lexicographic variant (flag, then x). *)
Theorem wloop_total :
  tc (fun s => s Fl = 1) wloop (fun _ => True).
Proof.
  eapply TC_Cons; [| | apply (TC_While (fun s => s Fl <= 1)
     (fun s1 s0 => s1 Fl < s0 Fl \/ (s1 Fl = s0 Fl /\ s1 X < s0 X)))].
  - intros s H. lia.
  - intros s _. exact I.
  - apply (wf_incl state _
      (fun s1 s0 : state => lexprod nat (fun _ : nat => nat) lt
         (fun _ : nat => lt)
         (existT (fun _ : nat => nat) (s1 Fl) (s1 X))
         (existT (fun _ : nat => nat) (s0 Fl) (s0 X)))).
    + intros s1 s0 [H | [E H]].
      * apply left_lex. exact H.
      * rewrite E. apply right_lex. exact H.
    + apply (wf_inverse_image state _ _
               (fun s : state => existT (fun _ : nat => nat) (s Fl) (s X))).
      apply wf_lexprod; intros; apply lt_wf.
  - intros st0. apply tc_complete. intros s [Hi [Hb ->]]. split.
    + intros s' Hc. unfold wbody in Hc. inversion Hc; subst.
      * match goal with H : beval _ (BEq (AVar Fl) (ANum 1)) = true |- _ =>
          simpl in H; apply Nat.eqb_eq in H end.
        match goal with H : ceval (CSeq _ _) _ _ |- _ => inversion H; subst end.
        match goal with H : ceval (CHavoc _) _ _ |- _ => inversion H; subst end.
        match goal with H : ceval (CAsgn _ _) _ _ |- _ =>
          inversion H; subst end.
        simpl. upd. lia.
      * match goal with H : beval _ (BEq (AVar Fl) (ANum 1)) = false |- _ =>
          simpl in H; apply Nat.eqb_neq in H end.
        match goal with H : ceval (CAsgn _ _) _ _ |- _ =>
          inversion H; subst end.
        simpl. upd.
        assert (E0 : st0 Fl = 0) by lia.
        unfold bassn in Hb. simpl in Hb. rewrite E0 in Hb.
        destruct (st0 X) eqn:Ex; [discriminate | lia].
    + intros Hd. inversion Hd; subst.
      * match goal with H : diverges (CSeq _ _) _ |- _ =>
          inversion H; subst end;
          match goal with H : diverges _ _ |- _ => inversion H end.
      * match goal with H : diverges _ _ |- _ => inversion H end.
Qed.

(** ** No natural-number variant *)

Lemma tcn_while_inv : forall P b c Q, tcn P (CWhile b c) Q ->
    exists (I : assertion) (m : state -> nat),
      (forall s, P s -> I s) /\
      (forall s s', I s -> bassn b s -> ceval c s s' -> I s' /\ m s' < m s).
Proof.
  intros P b c Q H. remember (CWhile b c) as w eqn:Ew.
  induction H; inversion Ew; subst.
  - exists I, m. split; [auto |]. intros s s' Hi Hb Hc.
    exact (proj1 (tcn_sound _ _ _ (H (m s)) s (conj Hi (conj Hb eq_refl)))
                 s' Hc).
  - destruct (IHtcn eq_refl) as [I [m [HP HB]]].
    exists I, m. split; [intros s Hs; apply HP, H, Hs | exact HB].
Qed.

Theorem wloop_not_tcn : forall Q, ~ tcn (fun s => s Fl = 1) wloop Q.
Proof.
  intros Q H. destruct (tcn_while_inv _ _ _ _ H) as [I [m [HP HB]]].
  (* counting down from x = k forces the variant to be at least k *)
  assert (Count : forall k s, I s -> s Fl = 0 -> s X = k -> k <= m s).
  { induction k as [| k IH]; intros s Hi Hf Hx; [lia |].
    assert (Hb : bassn wguard s).
    { unfold bassn. simpl. rewrite Hf, Hx. reflexivity. }
    assert (Hc : ceval wbody s
                   (update s X (aeval s (AMinus (AVar X) (ANum 1))))).
    { apply E_IfFalse; [simpl; rewrite Hf; reflexivity | apply E_Asgn]. }
    destruct (HB _ _ Hi Hb Hc) as [Hi' Hm].
    assert (k <= m (update s X (aeval s (AMinus (AVar X) (ANum 1))))).
    { apply IH; [exact Hi' | upd; exact Hf | upd; simpl; lia]. }
    lia. }
  set (s0 := update empty_state Fl 1).
  assert (Hi0 : I s0) by (apply HP; unfold s0; upd; reflexivity).
  set (n := S (m s0)).
  set (s1 := update (update s0 X n) Fl (aeval (update s0 X n) (ANum 0))).
  assert (Hc : ceval wbody s0 s1).
  { apply E_IfTrue; [reflexivity |].
    eapply E_Seq; [apply E_Havoc | apply E_Asgn]. }
  assert (Hb0 : bassn wguard s0) by (unfold bassn; reflexivity).
  destruct (HB _ _ Hi0 Hb0 Hc) as [Hi1 Hm1].
  assert (n <= m s1)
    by (apply Count; [exact Hi1 | unfold s1; upd; reflexivity
                     | unfold s1; upd; reflexivity]).
  unfold n in *. lia.
Qed.
