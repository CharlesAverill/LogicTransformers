(** * Generated logics prove what the textbook logics prove

    For the core language, with any atomic actions, the logic generated
    at each of the sixteen corners ([Examples.Common]: HL generated from
    the semantics, every other corner by transformers) proves exactly
    the triples that the textbook logic at that corner proves
    ([Core.TextbookCube]: textbook rule systems for HL, IL, NC, SIL,
    HL⊥, IL⊥ and SIL⊥, and the other nine corners from those by
    complement and Galois).

    Each equivalence is an instance of [vl_same_theorems]: two sound and
    complete logics at the same corner have the same theorems.

    The published rule sets for concrete languages (Hoare logic and
    incorrectness logic for Imp, adversarial logic, ...) are compared in
    the other files of this directory. *)

From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Verified.
From LogicTransformers.Core Require Import Kernel KernelBot TextbookCube.
From LogicTransformers.Examples Require Import Common.

Section Core.

Context {Σ Act : Type} (act_sem : Act -> Σ -> Σ -> Prop).

Notation T := (KLang act_sem).
Notation B := (KLangB act_sem).

(** [same V1 V2]: the two logics derive the same triples. *)
Definition same {L : Language} {d p a} (V1 V2 : VLogic L d p a) : Prop :=
  forall t, derivable (rules (vl_logic V1)) t <->
            derivable (rules (vl_logic V2)) t.

Theorem gen_text_HL : same (HLv act_sem) (tHL act_sem).
Proof. intro. apply vl_same_theorems. Qed.

Theorem gen_text_IL : same (ILv act_sem) (tIL act_sem).
Proof. intro. apply vl_same_theorems. Qed.

Theorem gen_text_NC : same (NCv act_sem) (tNC act_sem).
Proof. intro. apply vl_same_theorems. Qed.

Theorem gen_text_SIL : same (SILv act_sem) (tSIL act_sem).
Proof. intro. apply vl_same_theorems. Qed.

Theorem gen_text_PreDU : same (PreDUv act_sem) (tPreDU act_sem).
Proof. intro. apply vl_same_theorems. Qed.

Theorem gen_text_PostDU : same (PostDUv act_sem) (tPostDU act_sem).
Proof. intro. apply vl_same_theorems. Qed.

Theorem gen_text_PostDO : same (PostDOv act_sem) (tPostDO act_sem).
Proof. intro. apply vl_same_theorems. Qed.

Theorem gen_text_PreDO : same (PreDOv act_sem) (tPreDO act_sem).
Proof. intro. apply vl_same_theorems. Qed.

Theorem gen_text_HLb : same (HLbv act_sem) (tHLb act_sem).
Proof. intro. apply vl_same_theorems. Qed.

Theorem gen_text_ILb : same (ILbv act_sem) (tILb act_sem).
Proof. intro. apply vl_same_theorems. Qed.

Theorem gen_text_SILb : same (SILbv act_sem) (tSILb act_sem).
Proof. intro. apply vl_same_theorems. Qed.

Theorem gen_text_NCb : same (NCbv act_sem) (tNCb act_sem).
Proof. intro. apply vl_same_theorems. Qed.

Theorem gen_text_PreDUb : same (PreDUbv act_sem) (tPreDUb act_sem).
Proof. intro. apply vl_same_theorems. Qed.

Theorem gen_text_PostDUb : same (PostDUbv act_sem) (tPostDUb act_sem).
Proof. intro. apply vl_same_theorems. Qed.

Theorem gen_text_PostDOb : same (PostDObv act_sem) (tPostDOb act_sem).
Proof. intro. apply vl_same_theorems. Qed.

Theorem gen_text_PreDOb : same (PreDObv act_sem) (tPreDOb act_sem).
Proof. intro. apply vl_same_theorems. Qed.

(** All sixteen at once. *)
Theorem gen_text_cube :
    same (HLv act_sem) (tHL act_sem) /\
    same (ILv act_sem) (tIL act_sem) /\
    same (NCv act_sem) (tNC act_sem) /\
    same (SILv act_sem) (tSIL act_sem) /\
    same (PreDUv act_sem) (tPreDU act_sem) /\
    same (PostDUv act_sem) (tPostDU act_sem) /\
    same (PostDOv act_sem) (tPostDO act_sem) /\
    same (PreDOv act_sem) (tPreDO act_sem) /\
    same (HLbv act_sem) (tHLb act_sem) /\
    same (ILbv act_sem) (tILb act_sem) /\
    same (SILbv act_sem) (tSILb act_sem) /\
    same (NCbv act_sem) (tNCb act_sem) /\
    same (PreDUbv act_sem) (tPreDUb act_sem) /\
    same (PostDUbv act_sem) (tPostDUb act_sem) /\
    same (PostDObv act_sem) (tPostDOb act_sem) /\
    same (PreDObv act_sem) (tPreDOb act_sem).
Proof.
  repeat split; apply vl_same_theorems.
Qed.

End Core.
