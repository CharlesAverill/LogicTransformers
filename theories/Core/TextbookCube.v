(** * The whole cube from textbook rules

    All sixteen corners, for the core language with any atomic actions,
    with no generated exact rules anywhere. Seven corners have textbook
    proof systems of their own:
    - ordinary face: HL, IL, NC, SIL ([Core.Textbook]);
    - nontermination-aware face: HL⊥ ([Core.TextbookBot]), IL⊥
      ([Core.TextbookILBot]), SIL⊥ ([Core.TextbookSILBot]).

    The other nine are computed from those by the language-generic
    complement and Galois transformers ([Framework.Verified]), whose
    rules are the textbook rules complemented. Every record carries its
    soundness and completeness proofs, so each is a sound and complete
    proof system for its corner. *)

From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Verified.
From LogicTransformers.Core Require Import
  Kernel KernelBot Textbook TextbookBot TextbookILBot TextbookSILBot.

Section TextbookCube.

Context {Σ Act : Type} (act_sem : Act -> Σ -> Σ -> Prop).

Notation T := (KLang act_sem).
Notation B := (KLangB act_sem).

(** ** Ordinary face *)

Definition tHL : VLogic T Forward Plain Over := vHL_text act_sem.
Definition tIL : VLogic T Forward Plain Under := vIL_text act_sem.
Definition tNC : VLogic T Backward Plain Over := vNC_text act_sem.
Definition tSIL : VLogic T Backward Plain Under := vSIL_text act_sem.
Definition tPreDU : VLogic T Backward Dual Under := vgalois_hl tHL.
Definition tPostDU : VLogic T Forward Dual Under := vcomplement_FPO tHL.
Definition tPostDO : VLogic T Forward Dual Over := vcomplement_FPU tIL.
Definition tPreDO : VLogic T Backward Dual Over := vcomplement_BPU tSIL.

(** ** Nontermination-aware face *)

Definition tHLb : VLogic B Forward Plain Over := vHLB_text act_sem.
Definition tILb : VLogic B Forward Plain Under := vILB_text act_sem.
Definition tSILb : VLogic B Backward Plain Under := vSILB_text act_sem.
Definition tPostDUb : VLogic B Forward Dual Under := vcomplement_FPO tHLb.
Definition tNCb : VLogic B Backward Plain Over := vgalois_dimg_nc tPostDUb.
Definition tPreDUb : VLogic B Backward Dual Under := vgalois_hl tHLb.
Definition tPostDOb : VLogic B Forward Dual Over := vcomplement_FPU tILb.
Definition tPreDOb : VLogic B Backward Dual Over := vcomplement_BPU tSILb.

End TextbookCube.
