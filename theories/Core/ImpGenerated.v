(** * Imp through the generated logics

    Instantiating the generator with Imp's atoms (assignment, havoc) and
    encoding Imp programs into the core language gives sound and complete
    HL, IL and SIL for Imp, with no Imp-specific rules: an Imp triple is
    valid iff its encoding is derivable in the generated logic. *)

From LogicTransformers.Imp Require Import Syntax BigStep Lang.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube CubeLogic.
From LogicTransformers.Core Require Import Kernel ImpCore Generate CoreCube.

Lemma iact_refl : forall a s s', iact_sem a s s' <-> iact_sem a s s'.
Proof. intros. split; auto. Qed.

Ltac via_core d a S C :=
  intros P Q c; split; intros H;
  [ apply (C _ _ iact_sem iact_sem iact_refl);
    exact (proj1 (enc_cvalid d Plain a P Q c) H)
  | apply (proj2 (enc_cvalid d Plain a P Q c));
    exact (locally_sound_sound _
             (cl_locally_sound _ (S _ _ iact_sem iact_sem iact_refl)) _ H) ].

Theorem imp_HL_generated : forall (P Q : state -> Prop) c,
    cube_valid Forward Over (@mkTriple Imp P c Q) <->
    derivable (cl_rules (GHL iact_sem iact_sem)) (@mkTriple ICore P (enc c) Q).
Proof. via_core Forward Over @GHL_base_sound @GHL_complete. Qed.

Theorem imp_IL_generated : forall (P Q : state -> Prop) c,
    cube_valid Forward Under (@mkTriple Imp P c Q) <->
    derivable (cl_rules (GIL iact_sem iact_sem)) (@mkTriple ICore P (enc c) Q).
Proof. via_core Forward Under @GIL_base_sound @GIL_complete. Qed.

Theorem imp_SIL_generated : forall (P Q : state -> Prop) c,
    cube_valid Backward Under (@mkTriple Imp P c Q) <->
    derivable (cl_rules (GSIL iact_sem iact_sem)) (@mkTriple ICore P (enc c) Q).
Proof. via_core Backward Under @GSIL_base_sound @GSIL_complete. Qed.
