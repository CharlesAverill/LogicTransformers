(** * Incorrectness logic for Imp, obtained from Hoare logic

    [IL] is [HL] restricted to the [sym] rules and then flipped from
    over- to under-approximation. Nothing else is added:

    - soundness: each [sym] rule is checked at the new vertex
      ([imp_rule_under_sound]);
    - completeness: inherited, because the [sym] rules are exact
      ([flip_complete]).

    The selection matters. Flipping the [classic] Hoare rules gives an
    unsound logic ([flip_classic_unsound]): backward assignment does not
    survive the flip. *)

From Stdlib Require Import String.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube CubeLogic.
From LogicTransformers.Transformers Require Import Flip.
From LogicTransformers.Imp Require Import Syntax BigStep Lang.
From LogicTransformers.Logics Require Import Hoare ImpRules HoareLogic.

Definition IL_C : CubeLogic Imp := flip (restrict HL_C sym).

Definition IL : ProgramLogic Imp := to_logic IL_C.

(** An IL triple [[P] c [Q]] says: every state in [Q] is reachable by
    running [c] from some state in [P]. *)
Lemma IL_valid_iff : forall P c Q,
    valid IL (ht P c Q) <->
    (forall st', Q st' -> exists st, P st /\ ceval c st st').
Proof. intros P c Q. exact (il_valid_iff (ht P c Q)). Qed.

Theorem IL_locally_sound : locally_sound IL.
Proof.
  apply cl_locally_sound. intros ps c [r [[_ Hs] HR]] Hprem.
  exact (imp_rule_under_sound r ps c Hs HR Hprem).
Qed.

Theorem IL_sound : sound IL.
Proof. apply locally_sound_sound, IL_locally_sound. Qed.

Theorem IL_complete : complete IL.
Proof.
  apply (flip_complete (restrict HL_C sym)). intros P c.
  eapply derivable_mono; [| apply sym_exact].
  intros ps c' [r [Hs HR]]. exists r.
  split; [split; [exact I | exact Hs] | exact HR].
Qed.

(** ** Flipping the textbook rules is unsound *)

Theorem flip_classic_unsound :
  ~ sound (to_logic (flip (restrict HL_C classic))).
Proof.
  intros Hs.
  set (x := "x"%string).
  set (t := ht (assn_sub x (ANum 0) (fun _ => True)) (CAsgn x (ANum 0))
               (fun _ => True)).
  assert (D : derivable (rules (to_logic (flip (restrict HL_C classic)))) t).
  { eapply D_Rule; [left; exists RAsgnBwd; split; [split; exact I |];
                    apply IR_AsgnBwd | intros t' []]. }
  apply Hs in D. apply (il_valid_iff t) in D.
  destruct (D (update empty_state x 5) I) as [st [_ Hc]].
  cbn in Hc.
  remember (update empty_state x 5) as st' eqn:E.
  inversion Hc; subst.
  match goal with
  | H : update _ x _ = update _ x _ |- _ =>
      apply (f_equal (fun s => s x)) in H; rewrite !update_eq in H
  end.
  discriminate.
Qed.
