(** * The top face of the Cousot cube for Imp

    All eight nodes of the partial-correctness face, each a sound and
    complete program logic:

<<
                 Over (τ(·) ⊆ ·)              Under (· ⊆ τ(·))
    post         HL                           IL
    pre          NC                           SIL
    p̃ost         postD_over  = ∼IL            postD_under = ∼HL  (≡ NC)
    p̃re (wlp)    preD_over   = ∼SIL           preD_under  = HL   (≡ HL)
>>

    The four [Plain] nodes were built earlier (HL from the rule pool, IL by
    flipping, NC by complement, SIL by complement and flip). The four
    [Dual] nodes come from edges:

    - complement ([∼]): [postD_over], [postD_under], [preD_over]
      (classical);
    - Galois ([preD_under] from HL): constructive.

    The two Galois connections mean only six of the eight theories are
    distinct ([galois_pairs]). *)

From Stdlib Require Import Classical.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube CubeLogic Transformer.
From LogicTransformers.Transformers Require Import Complement Galois.
From LogicTransformers.Imp Require Import Lang.
From LogicTransformers.Logics Require Import HoareLogic IL NC SIL.

Definition SIL : ProgramLogic Imp := to_logic SIL_A.

(** ** The [Dual] nodes *)

Definition postD_over : ProgramLogic Imp :=
  run_edge (complement_edge Forward Plain Under) IL.

Definition postD_under : ProgramLogic Imp :=
  run_edge (complement_edge Forward Plain Over) HL.

Definition preD_over : ProgramLogic Imp :=
  run_edge (complement_edge Backward Plain Under) SIL.

Definition preD_under : ProgramLogic Imp :=
  run_edge galois_hl_wlp HL.

(** ** Every node is (locally) sound and complete *)

Ltac edge_sound H :=
  apply run_edge_locally_sound; [intros; reflexivity | apply H].
Ltac edge_complete H :=
  apply run_edge_complete; [intros; reflexivity | apply H].

Theorem postD_over_locally_sound : locally_sound postD_over.
Proof. edge_sound IL_locally_sound. Qed.
Theorem postD_over_complete : complete postD_over.
Proof. edge_complete IL_complete. Qed.

Theorem postD_under_locally_sound : locally_sound postD_under.
Proof. edge_sound HL_locally_sound. Qed.
Theorem postD_under_complete : complete postD_under.
Proof. edge_complete HL_complete. Qed.

Theorem preD_over_locally_sound : locally_sound preD_over.
Proof. edge_sound SIL_A_locally_sound. Qed.
Theorem preD_over_complete : complete preD_over.
Proof. edge_complete SIL_A_complete. Qed.

Theorem preD_under_locally_sound : locally_sound preD_under.
Proof. edge_sound HL_locally_sound. Qed.
Theorem preD_under_complete : complete preD_under.
Proof. edge_complete HL_complete. Qed.

(** Each node's validity is the corresponding [cvalid]. *)
Lemma top_face_validity :
  (forall t, valid HL t <-> cvalid Forward Plain Over t) /\
  (forall t, valid IL t <-> cvalid Forward Plain Under t) /\
  (forall t, valid NC t <-> cvalid Backward Plain Over t) /\
  (forall t, valid SIL t <-> cvalid Backward Plain Under t) /\
  (forall t, valid postD_over t <-> cvalid Forward Dual Over t) /\
  (forall t, valid postD_under t <-> cvalid Forward Dual Under t) /\
  (forall t, valid preD_over t <-> cvalid Backward Dual Over t) /\
  (forall t, valid preD_under t <-> cvalid Backward Dual Under t).
Proof. repeat split; intros; assumption. Qed.

(** ** The Galois connections collapse two pairs of nodes

    Two sound and complete logics for equivalent validities derive the
    same triples. *)

Lemma same_theory : forall (L1 L2 : ProgramLogic Imp),
    sound L1 -> complete L1 -> sound L2 -> complete L2 ->
    (forall t, valid L1 t <-> valid L2 t) ->
    forall t, derivable (rules L1) t <-> derivable (rules L2) t.
Proof.
  intros L1 L2 S1 C1 S2 C2 V t. split; intros D.
  - apply C2, V, S1, D.
  - apply C1, V, S2, D.
Qed.

Theorem galois_pairs :
  (forall t, derivable (rules HL) t <-> derivable (rules preD_under) t) /\
  (forall t, derivable (rules NC) t <-> derivable (rules postD_under) t).
Proof.
  split; apply same_theory.
  - apply HL_sound.
  - apply HL_complete.
  - apply locally_sound_sound, preD_under_locally_sound.
  - apply preD_under_complete.
  - apply galois_post_wlp.
  - apply NC_sound.
  - apply NC_complete.
  - apply locally_sound_sound, postD_under_locally_sound.
  - apply postD_under_complete.
  - apply galois_pre_dimg.
Qed.
