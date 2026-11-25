(** * The lost update, compositionally

    [Examples.RaceExample] finds the lost update with the cube's IL record,
    by following one global run step by step. Here the same bug is found
    with the compositional concurrent incorrectness logic of
    [ParImp.ConcurrentIL], following the program's structure:

<<
      race  =  a := x ; x := a + 1   ∥   b := x ; x := b + 1
>>

    One phase-splitting step ([CI_ParSplit]) separates the two reads from
    the two writes. Each phase runs its two assignments one after the
    other ([CI_ParSeqL]), and each assignment is one rule. The result is
    entered into the cube ([cil_derive_IL]).

    Landing on exactly the target state uses [functional_extensionality],
    through [RaceExample.st6_lost]. *)

From Stdlib Require Import String.
From LogicTransformers.Imp Require Import Syntax.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Relational Verified.
From LogicTransformers.Core Require Import Kernel SmallStepCore.
From LogicTransformers.ParImp Require Import ParImp ConcurrentIL.
From LogicTransformers.Examples Require Import Common RaceExample.

Local Open Scope string_scope.
Local Notation X := "x".
Local Notation A := "a".
Local Notation B := "b".

(** The four intermediate assertions: images of the precondition under
    each assignment, in the order the proof schedules them. *)
Definition Post1 (s1 : state) : Prop :=
  exists s, s X = 0 /\ s1 = update s A (aeval s (AVar X)).
Definition Post2 (s2 : state) : Prop :=
  exists s1, Post1 s1 /\ s2 = update s1 B (aeval s1 (AVar X)).
Definition Post3 (s3 : state) : Prop :=
  exists s2, Post2 s2 /\ s3 = update s2 X (aeval s2 (APlus (AVar A) (ANum 1))).
Definition Post4 (s4 : state) : Prop :=
  exists s3, Post3 s3 /\ s4 = update s3 X (aeval s3 (APlus (AVar B) (ANum 1))).

Theorem race_cil : cil (fun s => s X = 0) race Lost.
Proof.
  unfold race.
  apply (CI_Cons _ (fun s => s X = 0) _ Post4); [auto | |].
  - intros s' [Hx [Ha Hb]].
    set (s := update s' X 0).
    exists (st5 s). split.
    + exists (st2 s). split; [| reflexivity].
      exists (st1 s). split; [| reflexivity].
      exists s. split; [apply update_eq | reflexivity].
    + symmetry. exact (st6_lost s' Hx Ha Hb).
  - apply (CI_ParSplit _ Post2).
    + apply (CI_ParSeqL _ Post1); apply CI_Asgn.
    + apply (CI_ParSeqL _ Post3); apply CI_Asgn.
Qed.

(** The same bug as [RaceExample.race_lost_update], for concurrent Imp. *)
Corollary race_lost_update_cil :
  cvalid Forward Plain Under (@mkTriple ParImp (fun s => s X = 0) race Lost).
Proof. exact (cil_il _ _ _ race_cil). Qed.

(** And a derivation in the cube's IL record. *)
Corollary race_IL_from_cil :
  derivable (rules (vl_logic (ILv pact_sem)))
    (@mkTriple (KLang pact_sem) (fun k => snd k X = 0) (penc race)
       (liftG snd pfin Forward Plain Under Lost)).
Proof. exact (cil_derive_IL (ILv pact_sem) _ _ _ race_cil). Qed.
