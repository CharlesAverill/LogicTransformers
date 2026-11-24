(** * Small-step (structural operational) semantics of Imp *)

From LogicTransformers.Imp Require Import Syntax.

(** [cstep c st c' st'] : configuration [(c, st)] steps to [(c', st')].
    [CSkip] is the terminal configuration. *)
Inductive cstep : com -> state -> com -> state -> Prop :=
  | S_Asgn : forall x a st,
      cstep (CAsgn x a) st CSkip (update st x (aeval st a))
  | S_SeqSkip : forall c2 st,
      cstep (CSeq CSkip c2) st c2 st
  | S_SeqStep : forall c1 c1' c2 st st',
      cstep c1 st c1' st' ->
      cstep (CSeq c1 c2) st (CSeq c1' c2) st'
  | S_IfTrue : forall b c1 c2 st,
      beval st b = true ->
      cstep (CIf b c1 c2) st c1 st
  | S_IfFalse : forall b c1 c2 st,
      beval st b = false ->
      cstep (CIf b c1 c2) st c2 st
  | S_While : forall b c st,
      cstep (CWhile b c) st (CIf b (CSeq c (CWhile b c)) CSkip) st
  | S_ChoiceL : forall c1 c2 st,
      cstep (CChoice c1 c2) st c1 st
  | S_ChoiceR : forall c1 c2 st,
      cstep (CChoice c1 c2) st c2 st
  | S_Havoc : forall x n st,
      cstep (CHavoc x) st CSkip (update st x n).

(** Reflexive-transitive closure of [cstep]. *)
Inductive cmulti : com -> state -> com -> state -> Prop :=
  | MS_Refl : forall c st,
      cmulti c st c st
  | MS_Step : forall c st c' st' c'' st'',
      cstep c st c' st' ->
      cmulti c' st' c'' st'' ->
      cmulti c st c'' st''.

Lemma cmulti_trans : forall c st c' st' c'' st'',
    cmulti c st c' st' -> cmulti c' st' c'' st'' -> cmulti c st c'' st''.
Proof.
  intros c st c' st' c'' st'' H1 H2.
  induction H1; [assumption | eapply MS_Step; eauto].
Qed.

(** Sequencing is a congruence for multi-step reduction. *)
Lemma cmulti_seq : forall c1 st c1' st' c2,
    cmulti c1 st c1' st' -> cmulti (CSeq c1 c2) st (CSeq c1' c2) st'.
Proof.
  intros c1 st c1' st' c2 H.
  induction H.
  - apply MS_Refl.
  - eapply MS_Step; [apply S_SeqStep; eassumption | assumption].
Qed.
