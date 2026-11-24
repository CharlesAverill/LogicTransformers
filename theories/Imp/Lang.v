(** * Imp as a [Language] *)

From LogicTransformers.Framework Require Import Language.
From LogicTransformers.Imp Require Import Syntax BigStep SmallStep Equiv.

(** Imp with big-step semantics. *)
Definition Imp : Language := mkLanguage com state ceval.

(** Imp with small-step semantics, observed at termination. *)
Definition ImpSS : Language :=
  mkLanguage com state (fun c st st' => cmulti c st CSkip st').

Lemma Imp_ImpSS_sem : forall c st st',
    sem Imp c st st' <-> sem ImpSS c st st'.
Proof. intros. apply big_small_equiv. Qed.
