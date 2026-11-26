(** * The Cousot cube for Imp

    All 16 nodes of Cousot's cube (POPL'24 Fig. 3): four transformers
    (post, pre, p̃ost, p̃re) × two inclusions (⊆, ⊇) × two faces (partial
    correctness over [Imp], nontermination over [ImpBot]). Each node is a
    program logic that is sound and complete for its [cvalid] validity.
    The Galois connections make four pairs of these coincide
    ([TopFace.galois_pairs] and its bottom-face analogue follow the same
    way), so the cube has 12 distinct theories. *)

From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube.
From LogicTransformers.Imp Require Import Lang LangBot.
From LogicTransformers.ImpCube Require Import
  HoareLogic IL NC SIL TopFace BottomFace.

Definition sound_complete {L : Language} (Lg : ProgramLogic L) : Prop :=
  sound Lg /\ complete Lg.

Ltac sc H1 H2 := split; [apply locally_sound_sound, H1 | apply H2].

Theorem cousot_cube_top :
  sound_complete HL /\ sound_complete IL /\
  sound_complete NC /\ sound_complete SIL /\
  sound_complete postD_over /\ sound_complete postD_under /\
  sound_complete preD_over /\ sound_complete preD_under.
Proof.
  repeat split.
  - apply HL_sound.
  - apply HL_complete.
  - apply IL_sound.
  - apply IL_complete.
  - apply NC_sound.
  - apply NC_complete.
  - apply locally_sound_sound, SIL_A_locally_sound.
  - apply SIL_A_complete.
  - apply locally_sound_sound, postD_over_locally_sound.
  - apply postD_over_complete.
  - apply locally_sound_sound, postD_under_locally_sound.
  - apply postD_under_complete.
  - apply locally_sound_sound, preD_over_locally_sound.
  - apply preD_over_complete.
  - apply locally_sound_sound, preD_under_locally_sound.
  - apply preD_under_complete.
Qed.

Theorem cousot_cube_bottom :
  sound_complete HLB /\ sound_complete ILB /\
  sound_complete NCB /\ sound_complete SILB /\
  sound_complete postDB_over /\ sound_complete postDB_under /\
  sound_complete preDB_over /\ sound_complete preDB_under.
Proof.
  split; [sc HLB_locally_sound HLB_complete |].
  split; [sc ILB_locally_sound ILB_complete |].
  split; [sc NCB_locally_sound NCB_complete |].
  split; [sc SILB_locally_sound SILB_complete |].
  split; [sc postDB_over_locally_sound postDB_over_complete |].
  split; [sc postDB_under_locally_sound postDB_under_complete |].
  split; [sc preDB_over_locally_sound preDB_over_complete |].
  sc preDB_under_locally_sound preDB_under_complete.
Qed.
