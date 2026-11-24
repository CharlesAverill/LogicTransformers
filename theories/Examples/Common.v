(** * Shared infrastructure for the examples

    For a language given as an instance of the core ([act_sem] for its
    atomic actions), this file builds the 16 logics of the cube as verified
    records ([Framework.Verified.VLogic]). One record (HL) is generated
    from the semantics, and every other one is obtained by applying a
    transformer to a record. Each [derive_*] lemma is pulled from a
    record's completeness field: it turns semantic validity into a
    derivation in that logic.

    Why the examples derive triples by completeness. The generated rules
    are semantic, not syntactic:

    - an atom's rule mentions its relation directly (its post is the image
      of the pre under the action);
    - the star rule has one premise per iteration count [n]
      ([X n] to [X (n+1)]), and on the bottom face one premise per state;
    - assertions are arbitrary Rocq predicates.

    So a derivation by hand amounts to supplying, for every loop, the whole
    family of iterate assertions. That is the loop's semantics, which is
    what we characterize anyway. Each example therefore characterizes its
    program's runs and divergence once, proves each node's triple
    semantically valid, and obtains the derivation from the logic's
    completeness theorem. The derivation is a genuine object of the logic:
    completeness builds it from the generated exact rules plus one
    consequence step.

    [hand_cons] and [hand_gen] build HL derivations by hand from the
    generated rules and consequence ([RobotExample.robot_HL_by_hand]
    uses them). The rule-based proofs
    ([ImpProofs], [StackProofs], [ParExample]) use the admissible rules of
    [Core.Rules] and [Core.RulesBot] instead. *)

From Stdlib Require Import Arith Wf_nat.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube CubeLogic Transformer.
From LogicTransformers.Transformers Require Import Flip Complement Galois.
From LogicTransformers.Framework Require Import Verified.
From LogicTransformers.Core Require Import
  Kernel KernelBot Generate GenerateBot CoreCube CoreCousot VCore.

Section Common.

Context {Σ Act : Type} (act_sem : Act -> Σ -> Σ -> Prop).

Notation T := (KLang act_sem).
Notation B := (KLangB act_sem).

(** ** The 16 logics, as records obtained by transformers

    One record is generated from the semantics: HL. Every other node is
    obtained by applying a transformer to a record, and its soundness and
    completeness are read off the resulting record:

    - [vgalois_hl], [vcomplement], [vgalois_dimg_nc]: generic edges (the
      HL class);
    - [vto]: regenerate at another node from the atoms' relation recovered
      from a record's derivations (crossing to the IL and SIL classes);
    - [vto_bot], [vbot_to]: the same across and within the bottom face. *)

Definition HLv : VLogic T Forward Plain Over := start_HL act_sem.
Definition PreDUv : VLogic T Backward Dual Under := vgalois_hl HLv.
Definition PostDUv : VLogic T Forward Dual Under := vcomplement_FPO HLv.
Definition NCv : VLogic T Backward Plain Over := vgalois_dimg_nc PostDUv.
Definition ILv : VLogic T Forward Plain Under := vto act_sem HLv _ _ _.
Definition PostDOv : VLogic T Forward Dual Over := vcomplement_FPU ILv.
Definition SILv : VLogic T Backward Plain Under := vto act_sem ILv _ _ _.
Definition PreDOv : VLogic T Backward Dual Over := vcomplement_BPU SILv.

Definition HLbv : VLogic B Forward Plain Over := vto_bot act_sem HLv _ _ _.
Definition PreDUbv : VLogic B Backward Dual Under := vgalois_hl HLbv.
Definition PostDUbv : VLogic B Forward Dual Under := vcomplement_FPO HLbv.
Definition NCbv : VLogic B Backward Plain Over := vgalois_dimg_nc PostDUbv.
Definition ILbv : VLogic B Forward Plain Under := vbot_to act_sem HLbv _ _ _.
Definition PostDObv : VLogic B Forward Dual Over := vcomplement_FPU ILbv.
Definition SILbv : VLogic B Backward Plain Under := vbot_to act_sem ILbv _ _ _.
Definition PreDObv : VLogic B Backward Dual Over := vcomplement_BPU SILbv.

(** The logics themselves. *)
Definition HL_t := vl_logic HLv.
Definition IL_t := vl_logic ILv.
Definition NC_t := vl_logic NCv.
Definition SIL_t := vl_logic SILv.
Definition PostDO_t := vl_logic PostDOv.
Definition PostDU_t := vl_logic PostDUv.
Definition PreDO_t := vl_logic PreDOv.
Definition PreDU_t := vl_logic PreDUv.
Definition HL_b := vl_logic HLbv.
Definition IL_b := vl_logic ILbv.
Definition NC_b := vl_logic NCbv.
Definition SIL_b := vl_logic SILbv.
Definition PostDO_b := vl_logic PostDObv.
Definition PostDU_b := vl_logic PostDUbv.
Definition PreDO_b := vl_logic PreDObv.
Definition PreDU_b := vl_logic PreDUbv.

(** ** From validity to derivations: pulled from each record *)

Definition derive_HL_t := vl_derive HLv.
Definition derive_IL_t := vl_derive ILv.
Definition derive_NC_t := vl_derive NCv.
Definition derive_SIL_t := vl_derive SILv.
Definition derive_PostDO_t := vl_derive PostDOv.
Definition derive_PostDU_t := vl_derive PostDUv.
Definition derive_PreDO_t := vl_derive PreDOv.
Definition derive_PreDU_t := vl_derive PreDUv.
Definition derive_HL_b := vl_derive HLbv.
Definition derive_IL_b := vl_derive ILbv.
Definition derive_NC_b := vl_derive NCbv.
Definition derive_SIL_b := vl_derive SILbv.
Definition derive_PostDO_b := vl_derive PostDObv.
Definition derive_PostDU_b := vl_derive PostDUbv.
Definition derive_PreDO_b := vl_derive PreDObv.
Definition derive_PreDU_b := vl_derive PreDUbv.

(** ** Building HL derivations by hand *)

(** A generated rule instance is a rule of HL. *)
Lemma hand_gen : forall g ps c,
    @fwd_rule Σ Act act_sem act_sem g ps c ->
    (forall t, ps t -> derivable (rules HL_t) t) ->
    derivable (rules HL_t) c.
Proof.
  intros g ps c HR H. eapply D_Rule; [| exact H].
  left. exists (inl g). split; [exact I | exact HR].
Qed.

(** HL's consequence rule. *)
Lemma hand_cons : forall (P P' Q Q' : assertion T) c,
    derivable (rules HL_t) (mkTriple P' c Q') ->
    aimpl P P' -> aimpl Q' Q ->
    derivable (rules HL_t) (mkTriple P c Q).
Proof.
  intros P P' Q Q' c D H1 H2.
  apply D_Rule with (ps := fun t => t = mkTriple P' c Q').
  - right. exists P, P', Q, Q', c. split; [split; assumption |].
    split; reflexivity.
  - intros t ->. exact D.
Qed.

(** ** Loops: [while B do c] as [(assume B; c)*; assume ¬B] *)

End Common.

