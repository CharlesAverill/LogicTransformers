(** * Inversion: forward <-> backward

    Inverting the semantics turns a triple [(P, c, Q)] over [L] into
    [(Q, c, P)] over [inv L], and swaps direction while keeping the
    approximation:

<<
      img_R P ⊆ Q    <->   preimg_{R⁻¹} P ⊆ Q          (HL  <-> NC)
      Q ⊆ img_R P    <->   Q ⊆ preimg_{R⁻¹} P          (IL  <-> SIL)
>>

    Unlike [Complement] and [Flip], this transformer changes the
    language. It needs no axioms. *)

From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube CubeLogic Transformer.
From LogicTransformers.Transformers Require Import Flip.

Section Invert.

Context {L : Language}.

Definition swap (t : triple L) : triple (inv L) :=
  @mkTriple (inv L) (post t) (cmd t) (pre t).

Lemma swap_proper : respects_equiv swap.
Proof.
  intros [P c Q] [P' c' Q'] [HP [Hc HQ]]. unfold swap; simpl in *.
  repeat split; auto; try apply HP; try apply HQ.
Qed.

Theorem swap_valid : forall d a t,
    cube_valid d a t <-> cube_valid (flip_dir d) a (swap t).
Proof.
  intros d a [P c Q].
  destruct d, a; simpl; unfold aimpl, img, preimg; simpl; firstorder.
Qed.

Definition inv_cl (C : CubeLogic L) : CubeLogic (inv L) :=
  mkCubeLogic (flip_dir (cl_dir C)) (cl_approx C) (cl_rule C)
    (fun r => map_rules swap (cl_pool C r)) (cl_keep C).

Theorem inv_cl_base_sound : forall C,
    base_sound C -> base_sound (inv_cl C).
Proof.
  intros C HB ps c [r [Hk [ps0 [c0 [HR [-> Hps]]]]]] Hprem. simpl in *.
  apply swap_valid. apply (HB ps0 c0); [exists r; auto |].
  intros t Ht. apply swap_valid, Hprem, Hps. exists t. auto.
Qed.

(** ** Inversion preserves derivability and completeness

    A swapped consequence instance is a consequence instance at the
    inverted vertex, so every derivation maps to a derivation. Inversion is
    an isomorphism, so this needs no exactness assumption. *)

Lemma cons_side_swap : forall d a (P P' Q Q' : assertion L),
    cons_side d a P P' Q Q' <->
    @cons_side (inv L) (flip_dir d) a Q Q' P P'.
Proof. intros d a P P' Q Q'. destruct d, a; simpl; tauto. Qed.

Lemma inv_cl_derivable : forall C t,
    derivable (cl_rules C) t -> derivable (cl_rules (inv_cl C)) (swap t).
Proof.
  intros C t D.
  induction D as [ps c [Hb | Hc] Hps IH | t t' D IH He].
  - apply D_Rule with (ps := image swap ps).
    + left. destruct Hb as [r [Hk HR]]. exists r. split; [exact Hk |].
      exists ps, c. repeat split; auto.
    + intros t' [t0 [H0 ->]]. auto.
  - destruct Hc as [P [P' [Q [Q' [cm [Hside [-> ->]]]]]]].
    apply D_Rule with (ps := fun t => t = swap (mkTriple P' cm Q')).
    + right. exists Q, Q', P, P', cm.
      split; [exact (proj1 (cons_side_swap _ _ P P' Q Q') Hside)
             | split; reflexivity].
    + intros t ->. apply IH. reflexivity.
  - eapply D_Equiv; [exact IH | apply swap_proper, He].
Qed.

Theorem inv_cl_complete : forall C,
    complete (to_logic C) -> complete (to_logic (inv_cl C)).
Proof.
  intros C HC [P c Q] V.
  pose proof (inv_cl_derivable C (@mkTriple L Q c P)) as H.
  apply H, HC. simpl.
  apply (swap_valid (cl_dir C) (cl_approx C) (@mkTriple L Q c P)). exact V.
Qed.

Theorem inv_cl_locally_sound : forall C,
    base_sound C -> locally_sound (to_logic (inv_cl C)).
Proof. intros C HB. apply cl_locally_sound, inv_cl_base_sound, HB. Qed.

(** Flipping commutes with inversion on the nose. *)
Theorem flip_inv_cl : forall C, flip (inv_cl C) = inv_cl (flip C).
Proof. reflexivity. Qed.

End Invert.
