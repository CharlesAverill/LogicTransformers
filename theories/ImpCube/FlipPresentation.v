(** * Flipping depends on how rules are written, not on what they prove

    Two selections of Imp's Hoare rule pool:
    - [HLc], the textbook rules (backward assignment, invariant loop rule,
      and so on), the rules of [Hoare.hoare_proof];
    - [HLs], the exact forward rules ([sym]).

    Both are sound and complete Hoare logics, so they derive exactly the
    same triples ([HLc_HLs_same_theorems]). Flipping them from over- to
    under-approximation gives different results: flipping [HLs] gives a
    sound and complete incorrectness logic, and flipping [HLc] gives an
    unsound one ([flip_depends_on_presentation]). So a logic's flip is not
    determined by its theorems ([flip_theorems_differ]).
    By [Transformers.Flip.flip_works_iff], the difference is exactly that
    every [sym] rule is sound at both approximations, while backward
    assignment is not. *)

From Stdlib Require Import Classical.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube CubeLogic.
From LogicTransformers.Transformers Require Import Flip.
From LogicTransformers.Imp Require Import Syntax BigStep Lang.
From LogicTransformers.Imp Require Import Hoare.
From LogicTransformers.ImpCube Require Import ImpRules HoareLogic IL.

Definition HLc : CubeLogic Imp := restrict HL_C classic.
Definition HLs : CubeLogic Imp := restrict HL_C sym.

Lemma HLc_locally_sound : locally_sound (to_logic HLc).
Proof.
  apply cl_locally_sound, restrict_base_sound, locally_sound_base.
  exact HL_locally_sound.
Qed.

Lemma HLs_locally_sound : locally_sound (to_logic HLs).
Proof.
  apply cl_locally_sound, restrict_base_sound, locally_sound_base.
  exact HL_locally_sound.
Qed.

Ltac by_rule r := left; exists r; split; [split; exact I |].

(** Every [hoare_proof] derivation is a derivation in [HLc]. *)
Lemma hoare_proof_HLc : forall P c Q,
    hoare_proof P c Q -> derivable (rules (to_logic HLc)) (ht P c Q).
Proof.
  intros P c Q H. induction H.
  - apply (D_Rule _ prem0); [by_rule RSkip; constructor | intros t []].
  - apply (D_Rule _ prem0); [by_rule RAsgnBwd; constructor | intros t []].
  - apply (D_Rule _ (prem2 (ht P c1 Q) (ht Q c2 R)));
      [by_rule RSeq; constructor | intros t [-> | ->]; assumption].
  - apply (D_Rule _ (prem2 (ht (with_b P b) c1 Q) (ht (with_nb P b) c2 Q)));
      [by_rule RIf; constructor | intros t [-> | ->]; assumption].
  - apply (D_Rule _ (prem1 (ht (with_b P b) c P)));
      [by_rule RWhileInv; constructor | intros t ->; assumption].
  - apply (D_Rule _ (prem2 (ht P c1 Q) (ht P c2 Q)));
      [by_rule RChoice; constructor | intros t [-> | ->]; assumption].
  - apply (D_Rule _ prem0); [by_rule RHavocBwd; constructor | intros t []].
  - apply (D_Rule _ (fun t => t = ht P' c Q')); [| intros t ->; assumption].
    right. exists P, P', Q, Q', c. split; [split; assumption |].
    split; reflexivity.
Qed.

Lemma HLc_complete : complete (to_logic HLc).
Proof.
  intros [P c Q] V. apply hoare_proof_HLc, hoare_complete.
  exact (proj1 (HL_valid_iff P c Q) V).
Qed.

Lemma HLs_complete : complete (to_logic HLs).
Proof.
  apply (flip_complete HLs). intros P c.
  eapply derivable_mono; [| apply sym_exact].
  intros ps c' [r [Hs HR]]. exists r.
  split; [split; [exact I | exact Hs] | exact HR].
Qed.

(** Two sound and complete Hoare logics prove the same triples. *)
Theorem HLc_HLs_same_theorems : forall t,
    derivable (rules (to_logic HLc)) t <-> derivable (rules (to_logic HLs)) t.
Proof.
  intros t. split; intros D.
  - apply HLs_complete. exact (locally_sound_sound _ HLc_locally_sound t D).
  - apply HLc_complete. exact (locally_sound_sound _ HLs_locally_sound t D).
Qed.

(** Their flips differ: one is sound and complete, the other unsound. *)
Theorem flip_depends_on_presentation :
    (forall t, derivable (rules (to_logic HLc)) t <->
               derivable (rules (to_logic HLs)) t) /\
    locally_sound (to_logic (flip HLs)) /\
    complete (to_logic (flip HLs)) /\
    ~ sound (to_logic (flip HLc)).
Proof.
  split; [exact HLc_HLs_same_theorems |].
  split; [exact IL_locally_sound |].
  split; [exact IL_complete | exact flip_classic_unsound].
Qed.

(** So the flip is not determined by a logic's theorems: the two logics
    prove the same triples, and their flips do not. *)
Theorem flip_theorems_differ :
    exists t, derivable (rules (to_logic (flip HLc))) t /\
              ~ derivable (rules (to_logic (flip HLs))) t.
Proof.
  apply NNPP. intros H. apply flip_classic_unsound. intros t D.
  apply (locally_sound_sound _ IL_locally_sound).
  apply NNPP. intros Hn. apply H. exists t. split; assumption.
Qed.
