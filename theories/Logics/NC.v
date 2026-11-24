(** * Necessary-condition logic for Imp, obtained from Hoare logic

    [NC] is not defined by hand. It is [HL] run through the complement
    edge: its validity is the backward/over-approximate vertex of the
    cube, and its rules are the complements of the Hoare rules. Local
    soundness, soundness and completeness come from the edge theorems. *)

From Stdlib Require Import Classical.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Transformer.
From LogicTransformers.Imp Require Import Syntax BigStep Lang.
From LogicTransformers.Logics Require Import ImpRules HoareLogic.
From LogicTransformers.Transformers Require Import Complement.

Definition NC : ProgramLogic Imp := run_edge hl_to_nc HL.

(** An NC triple [(P, c, Q)] says: every state that can reach [Q] by
    running [c] satisfies [P], so [P] is necessary for reaching [Q]. *)
Lemma NC_valid_iff : forall P c Q,
    valid NC (ht P c Q) <->
    (forall st st', ceval c st st' -> Q st' -> P st).
Proof. intros P c Q. exact (nc_valid_iff (ht P c Q)). Qed.

Theorem NC_locally_sound : locally_sound NC.
Proof.
  apply run_edge_locally_sound; [reflexivity | apply HL_locally_sound].
Qed.

Theorem NC_sound : sound NC.
Proof. apply run_edge_sound; [reflexivity | apply HL_locally_sound]. Qed.

Theorem NC_complete : complete NC.
Proof. apply run_edge_complete; [reflexivity | apply HL_complete]. Qed.

(** ** Example: the NC sequencing rule, derived structurally

    The NC rules are the complemented Hoare rules. Here the sequencing
    rule is obtained from [HR_Seq] directly, without going through
    soundness and completeness. *)

Lemma ht_compl_compl : forall P c Q,
    triple_equiv (ht P c Q) (complement (ht (compl P) c (compl Q))).
Proof.
  intros. apply triple_equiv_sym, (complement_involutive (ht P c Q)).
Qed.

Lemma NC_seq : forall P Q R c1 c2,
    derivable (rules NC) (ht P c1 Q) ->
    derivable (rules NC) (ht Q c2 R) ->
    derivable (rules NC) (ht P (CSeq c1 c2) R).
Proof.
  intros P Q R c1 c2 D1 D2.
  eapply D_Equiv; [| apply triple_equiv_sym, ht_compl_compl].
  eapply D_Rule.
  - exists (prem2 (ht (compl P) c1 (compl Q)) (ht (compl Q) c2 (compl R))).
    eexists. split; [left; exists RSeq; split; [exact I | apply IR_Seq] |].
    split; [reflexivity |]. intros t. reflexivity.
  - intros t [t0 [[-> | ->] ->]];
      (eapply D_Equiv; [| apply ht_compl_compl]; assumption).
Qed.
