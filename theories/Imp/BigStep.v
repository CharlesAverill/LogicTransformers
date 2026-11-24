(** * Big-step (natural) semantics of Imp *)

From Stdlib Require Import String.
From LogicTransformers.Imp Require Import Syntax.

(** [ceval c st st'] : running [c] from [st] terminates in [st']. *)
Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      ceval CSkip st st
  | E_Asgn : forall st x a,
      ceval (CAsgn x a) st (update st x (aeval st a))
  | E_Seq : forall c1 c2 st st' st'',
      ceval c1 st st' ->
      ceval c2 st' st'' ->
      ceval (CSeq c1 c2) st st''
  | E_IfTrue : forall b c1 c2 st st',
      beval st b = true ->
      ceval c1 st st' ->
      ceval (CIf b c1 c2) st st'
  | E_IfFalse : forall b c1 c2 st st',
      beval st b = false ->
      ceval c2 st st' ->
      ceval (CIf b c1 c2) st st'
  | E_WhileFalse : forall b c st,
      beval st b = false ->
      ceval (CWhile b c) st st
  | E_WhileTrue : forall b c st st' st'',
      beval st b = true ->
      ceval c st st' ->
      ceval (CWhile b c) st' st'' ->
      ceval (CWhile b c) st st''
  | E_ChoiceL : forall c1 c2 st st',
      ceval c1 st st' ->
      ceval (CChoice c1 c2) st st'
  | E_ChoiceR : forall c1 c2 st st',
      ceval c2 st st' ->
      ceval (CChoice c1 c2) st st'
  | E_Havoc : forall x n st,
      ceval (CHavoc x) st (update st x n).

(** Imp is nondeterministic: [havoc x] has many outcomes. *)
Theorem ceval_not_deterministic :
  ~ (forall c st st1 st2, ceval c st st1 -> ceval c st st2 -> st1 = st2).
Proof.
  intros H.
  specialize (H _ _ _ _ (E_Havoc "x"%string 0 empty_state)
                        (E_Havoc "x"%string 1 empty_state)).
  apply (f_equal (fun st => st "x"%string)) in H.
  rewrite !update_eq in H. discriminate.
Qed.
