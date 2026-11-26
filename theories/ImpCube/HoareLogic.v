(** * Hoare logic as a cube logic

    [HL] is the forward/over-approximate vertex with the whole Imp rule
    pool (plus HL consequence). Every pool rule is HL-sound. Completeness
    comes from the exactness of the [sym] subset, and we show that [HL]
    derives exactly the triples that [Hoare.hoare_proof] derives. *)

From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube CubeLogic.
From LogicTransformers.Imp Require Import Syntax BigStep Lang.
From LogicTransformers.Imp Require Import Hoare.
From LogicTransformers.ImpCube Require Import ImpRules.

Definition HL_C : CubeLogic Imp :=
  mkCubeLogic Forward Over rule_name imp_rule (fun _ => True).

Definition HL : ProgramLogic Imp := to_logic HL_C.

Lemma HL_valid_iff : forall P c Q,
    valid HL (ht P c Q) <-> hoare_valid P c Q.
Proof. intros P c Q. exact (hl_valid_iff (ht P c Q)). Qed.

Theorem HL_locally_sound : locally_sound HL.
Proof.
  apply cl_locally_sound. intros ps c [r [_ HR]] Hprem.
  exact (imp_rule_over_sound r ps c HR Hprem).
Qed.

Theorem HL_sound : sound HL.
Proof. apply locally_sound_sound, HL_locally_sound. Qed.

Theorem HL_complete : complete HL.
Proof.
  apply exact_complete. intros P c.
  eapply derivable_mono; [| apply sym_exact].
  intros ps c' [r [_ HR]]. exists r. split; [exact I | exact HR].
Qed.

Theorem HL_iff_hoare_proof : forall P c Q,
    derivable (rules HL) (ht P c Q) <-> hoare_proof P c Q.
Proof.
  intros P c Q. rewrite hoare_sound_complete, <- HL_valid_iff.
  split; [apply HL_sound | apply HL_complete].
Qed.
