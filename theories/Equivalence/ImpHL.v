(** * Hoare logic for Imp: the textbook rules and the generated logic

    [ImpCube.Hoare.hoare_proof] is the textbook Hoare logic for Imp:
    backward assignment [{Q[a/x]} x := a {Q}], the invariant rule for
    [while], and consequence. The generated Hoare logic is the record
    [Examples.Common.HLv] for Imp's atoms, applied to the encoding of
    the program ([Core.ImpCore.enc]).

    [hoare_iff_generated]: the two prove exactly the same triples. Both
    are sound and complete for partial correctness, and the encoding
    preserves the semantics. Constructive. *)

From LogicTransformers.Imp Require Import Syntax BigStep Lang.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Verified.
From LogicTransformers.Core Require Import Kernel ImpCore.
From LogicTransformers.Imp Require Import Hoare.
From LogicTransformers.Examples Require Import Common.

Theorem hoare_iff_generated : forall P c Q,
    hoare_proof P c Q <->
    derivable (rules (vl_logic (HLv iact_sem)))
      (@mkTriple ICore P (enc c) Q).
Proof.
  intros P c Q. rewrite hoare_sound_complete, vl_theory, <- enc_cvalid.
  rewrite cvalid_Imp_rel. simpl. reflexivity.
Qed.
