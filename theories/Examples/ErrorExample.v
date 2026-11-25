(** * Proving that a bug is reachable, with O'Hearn's rules

    Two programs over Imp's atomic actions ([Core.ImpCore]) with an
    [error] command, proved with the rules of [Core.Errors] in the IL
    record computed by the transformers ([Examples.Common]).

    - [guess]: [havoc x; (assume x = 42; error) ⊕ assume x ≠ 42].
      Every state with [x = 42] is reached as an error, and every state
      with [x ≠ 42] is reached normally.
    - [count3]: [x := 0; (x := x + 1; ((assume x = 3; error) ⊕ skip))*].
      The error inside the loop is reachable after three iterations. The
      proof unrolls the loop once ([oh_unroll]) and uses the
      iteration-indexed rule for the first two iterations ([oh_star]).

    The results are then read back as O'Hearn's validity, stated with
    his two-outcome semantics ([oh_iff]). Showing that a run ends in an
    exact state needs [functional_extensionality], because Imp states
    are functions. *)

From Stdlib Require Import String Arith Lia FunctionalExtensionality.
From LogicTransformers.Imp Require Import Syntax.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Verified Abstraction.
From LogicTransformers.Core Require Import Kernel Rules ImpCore Errors.
From LogicTransformers.Examples Require Import Common.

Local Open Scope string_scope.
Local Notation X := "x".

Notation esemI := (esem iact_sem).
Notation V := (ILv esemI).
Notation OH := (ohprov iact_sem V).

Lemma upd_same : forall (s : state) x, update s x (s x) = s.
Proof.
  intros s x. apply functional_extensionality. intros z. unfold update.
  destruct (String.eqb_spec x z); subst; reflexivity.
Qed.

Lemma upd_upd : forall (s : state) x v w,
    update (update s x v) x w = update s x w.
Proof.
  intros s x v w. apply functional_extensionality. intros z. unfold update.
  destruct (String.eqb x z); reflexivity.
Qed.

(** ** A guessed value *)

Definition guess : ecom :=
  XSeq (XAct (IHavoc X))
       (XChoice (XSeq (XAssume (fun s => s X = 42)) XError)
                (XAssume (fun s => s X <> 42))).

Theorem guess_IL : OH (fun _ => True) guess
                      (fun s => s X <> 42) (fun s => s X = 42).
Proof.
  apply (oh_cons _ _ _ (fun _ => True) _ (fun s => s X <> 42) _
           (fun s => FF s \/ s X = 42));
    [auto | auto | intros s H; right; exact H |].
  apply (oh_seq _ _ _ (fun _ => True)).
  - apply (oh_cons _ _ _ (fun _ => True) _
             (fun s' => exists s, True /\ iact_sem (IHavoc X) s s') _ FF);
      [auto | | auto | apply oh_act].
    intros s' _. exists s'. split; [exact I |]. exists (s' X).
    symmetry. apply upd_same.
  - apply (oh_cons _ _ _ (fun _ => True) _
             (fun s => FF s \/ s X <> 42) _ (fun s => s X = 42 \/ FF s));
      [auto | intros s H; right; exact H | intros s H; left; exact H |].
    apply oh_disj.
    + apply oh_choice_l.
      apply (oh_cons _ _ _ (fun _ => True) _ FF _
               (fun s => FF s \/ (True /\ s X = 42)));
        [auto | auto | intros s H; right; split; [exact I | exact H] |].
      apply (oh_seq _ _ _ (fun s => True /\ s X = 42));
        [apply oh_assume | apply oh_error].
    + apply oh_choice_r.
      apply (oh_cons _ _ _ (fun _ => True) _ (fun s => True /\ s X <> 42)
               _ FF);
        [auto | intros s H; split; [exact I | exact H] | auto |].
      apply oh_assume.
Qed.

(** Read back as O'Hearn's validity, with his two-outcome semantics. *)
Corollary guess_bug_reachable :
  forall s', s' X = 42 ->
  exists s, err iact_sem guess s s'.
Proof.
  intros s' H.
  destruct (proj2 (proj1 (oh_iff _ _ _ _ _ _) guess_IL) s' H) as [s [_ Hs]].
  exists s. exact Hs.
Qed.

(** ** An error inside a loop *)

Definition body : ecom :=
  XSeq (XAct (IAsgn X (APlus (AVar X) (ANum 1))))
       (XChoice (XSeq (XAssume (fun s => s X = 3)) XError) XSkip).

Definition count3 : ecom :=
  XSeq (XAct (IAsgn X (ANum 0))) (XStar body).

(** The states before iteration [n]: [x = n], for the first three. *)
Definition Xn (n : nat) (s : state) : Prop := n <= 2 /\ s X = n.

Local Notation incr := (IAsgn X (APlus (AVar X) (ANum 1))).

Lemma body_step : forall n, OH (Xn n) body (Xn (S n)) FF.
Proof.
  intros n. unfold body.
  set (R := fun s' => exists s, Xn n s /\ iact_sem incr s s').
  apply (oh_cons _ _ _ (Xn n) _ R _ (fun s => FF s \/ FF s));
    [auto | | intros s [] |].
  - intros s' [Hn Hx]. exists (update s' X n).
    split; [split; [lia | apply update_eq] |].
    cbn [iact_sem aeval]. rewrite update_eq, upd_upd.
    replace (n + 1) with (s' X) by lia. symmetry. apply upd_same.
  - apply (oh_seq _ _ _ R); [apply oh_act | apply oh_choice_r, oh_skip].
Qed.

(** From [x <= 2], one more iteration raises the error at [x = 3]. *)
Lemma body_err : OH (fun s => exists n, Xn n s) body FF (fun s => s X = 3).
Proof.
  unfold body.
  set (R := fun s' => exists s, (exists n, Xn n s) /\ iact_sem incr s s').
  apply (oh_cons _ _ _ (fun s => exists n, Xn n s) _ FF _
           (fun s => FF s \/ (FF s \/ (R s /\ s X = 3))));
    [auto | auto | |].
  - intros s' Hx. right. right. split; [| exact Hx].
    exists (update s' X 2).
    split; [exists 2; split; [lia | apply update_eq] |].
    cbn [iact_sem aeval]. rewrite update_eq, upd_upd.
    replace (2 + 1) with (s' X) by lia. symmetry. apply upd_same.
  - apply (oh_seq _ _ _ R); [apply oh_act |].
    apply oh_choice_l.
    apply (oh_seq _ _ _ (fun s => R s /\ s X = 3));
      [apply oh_assume | apply oh_error].
Qed.

Theorem count3_error : OH (fun _ => True) count3 FF (fun s => s X = 3).
Proof.
  unfold count3.
  apply (oh_cons _ _ _ (fun _ => True) _ FF _ (fun s => FF s \/ s X = 3));
    [auto | auto | intros s H; right; exact H |].
  apply (oh_seq _ _ _ (Xn 0)).
  - apply (oh_cons _ _ _ (fun _ => True) _
             (fun s' => exists s, True /\ iact_sem (IAsgn X (ANum 0)) s s')
             _ FF); [auto | | auto | apply oh_act].
    intros s' [_ Hx]. exists s'. split; [exact I |]. cbn [iact_sem aeval].
    rewrite <- Hx. symmetry. apply upd_same.
  - apply oh_unroll.
    apply (oh_cons _ _ _ (Xn 0) _ FF _ (fun s => FF s \/ s X = 3));
      [auto | auto | intros s H; right; exact H |].
    apply (oh_seq _ _ _ (fun s => exists n, Xn n s));
      [apply oh_star; exact body_step | exact body_err].
Qed.

(** Read back with O'Hearn's semantics: every state with [x = 3] is an
    erroneous outcome of [count3]. *)
Corollary count3_bug_reachable :
  forall s', s' X = 3 -> exists s, err iact_sem count3 s s'.
Proof.
  intros s' H.
  destruct (proj2 (proj1 (oh_iff _ _ _ _ _ _) count3_error) s' H)
    as [s [_ Hs]].
  exists s. exact Hs.
Qed.
