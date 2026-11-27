(** * Swapping two cells, in the generated separation logic

<<
      {x ↦ a * y ↦ b}
        t := [x]; u := [y]; [x] := u; [y] := t
      {x ↦ b * y ↦ a}
>>

    The proof applies only rules of the generated Hoare logic for the
    heap language ([Separation.Heap]): the small axioms for load and
    store, sequencing, consequence, and the frame rule, which frames
    away the cell each step does not touch. Side conditions are facts
    about stores (which variables a step writes). *)

From Stdlib Require Import String List FunctionalExtensionality.
Import ListNotations.
From LogicTransformers.Imp Require Import Syntax.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Verified.
From LogicTransformers.Core Require Import Kernel Rules.
From LogicTransformers.Separation Require Import Heap.

Local Open Scope string_scope.
Local Notation X := "x".
Local Notation Y := "y".
Local Notation T := "t".
Local Notation U := "u".

Definition swap : hcmd :=
  CSeq' (CAct (HLoad T (AVar X)))
  (CSeq' (CAct (HLoad U (AVar Y)))
  (CSeq' (CAct (HStore (AVar X) (AVar U)))
         (CAct (HStore (AVar Y) (AVar T))))).

Section Swap.

Variable V : VLogic (KLang hsem) Forward Plain Over.
Variables a b : nat.

Local Notation px v := (pts (AVar X) v).
Local Notation py v := (pts (AVar Y) v).

(** One framed step: frame [F] away, apply the small axiom, frame back. *)
Lemma step : forall (P P' Q Q' F : hprop) c,
    (forall s h, P s h -> star P' F s h) -> sl V P' c Q' ->
    indep (wr c) F -> (forall s h, star Q' F s h -> Q s h) -> sl V P c Q.
Proof.
  intros P P' Q Q' F c HP H HF HQ.
  eapply sl_cons; [exact HP | exact HQ | apply frame_rule; assumption].
Qed.

Lemma notin : forall x y : var, x <> y -> ~ In x [y].
Proof. intros x y H [E | []]. apply H. symmetry. exact E. Qed.

Ltac ne := intros ?; discriminate.

Theorem swap_correct :
  sl V (star (px a) (py b)) swap (star (px b) (py a)).
Proof.
  unfold swap.
  set (F2 := fun s h => True /\ s T = a /\ px a s h).
  (* t := [x], framing y |-> b *)
  apply (sl_seq V _ (star F2 (py b))).
  { apply (step _ (pure (fun _ => True) (px a)) _ F2 (py b)).
    - intros s h H. eapply star_mono; [| | exact H]; unfold pure; auto.
    - apply sl_load; [intros; simpl; apply update_neq; discriminate | auto].
    - intros s s' h E H. unfold pts in *. simpl in *.
      rewrite (E Y (notin Y T ltac:(discriminate))). exact H.
    - auto. }
  set (G2 := fun s h => True /\ s U = b /\ py b s h).
  (* u := [y], framing the first cell *)
  apply (sl_seq V _ (star G2 F2)).
  { apply (step _ (pure (fun _ => True) (py b)) _ G2 F2).
    - intros s h H. apply star_comm in H.
      eapply star_mono; [| | exact H]; unfold pure; auto.
    - apply sl_load; [intros; simpl; apply update_neq; discriminate | auto].
    - intros s s' h E [_ [Ht Hx]]. unfold pts in *. simpl in *.
      split; [exact I |].
      rewrite (E T (notin T U ltac:(discriminate))),
              (E X (notin X U ltac:(discriminate))). auto.
    - auto. }
  set (R3 := fun s => s U = b /\ s T = a).
  (* [x] := u, framing the second cell *)
  apply (sl_seq V _ (star (pure R3 (px b)) (pure R3 (py b)))).
  { apply (step _ (fun s h => R3 s /\ exists v, px v s h)
              _ (fun s h => R3 s /\ px (aeval s (AVar U)) s h)
              (pure R3 (py b))).
    - intros s h H. destruct H as [h1 [h2 [D [E [[_ [Hu Hy]] [_ [Ht Hx]]]]]]].
      exists h2, h1. split; [apply disj_sym, D |].
      split; [rewrite E; apply hunion_comm, D |].
      split; [split; [split; auto | exists a; exact Hx] |].
      split; [split; auto | exact Hy].
    - apply sl_store.
    - intros s s' h E H. simpl in E.
      replace s' with s by (apply functional_extensionality; intros x;
                            symmetry; apply E; intros []).
      exact H.
    - intros s h H. eapply star_mono; [| | exact H]; [| auto].
      intros s0 h0 [Hr Hp]. split; [exact Hr |].
      unfold pts in *. simpl in *. rewrite (proj1 Hr) in Hp. exact Hp. }
  (* [y] := t, framing the first cell *)
  apply (step _ (fun s h => R3 s /\ exists v, py v s h)
            _ (fun s h => R3 s /\ py (aeval s (AVar T)) s h)
            (pure R3 (px b))).
  - intros s h H. apply star_comm in H.
    eapply star_mono; [| | exact H]; [| auto].
    intros s0 h0 [Hr Hp]. split; [exact Hr | exists b; exact Hp].
  - apply sl_store.
  - intros s s' h E H. simpl in E.
    replace s' with s by (apply functional_extensionality; intros x;
                          symmetry; apply E; intros []).
    exact H.
  - intros s h H. apply star_comm.
    eapply star_mono; [| | exact H]; [| intros s0 h0 [_ Hp]; exact Hp].
    intros s0 h0 [Hr Hp]. unfold pts in *. simpl in *.
    rewrite (proj2 Hr) in Hp. exact Hp.
Qed.

End Swap.
