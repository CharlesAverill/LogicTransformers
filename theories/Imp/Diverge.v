(** * Divergence of Imp programs

    [diverges c st]: some execution of [c] from [st] runs forever.
    Coinductive, so a diverging loop is an infinite derivation of
    [Dv_WhileIter]. Together with [ceval] this gives Cousot's natural
    relational semantics with nontermination. *)

From LogicTransformers.Imp Require Import Syntax BigStep.

CoInductive diverges : com -> state -> Prop :=
  | Dv_SeqL : forall c1 c2 st,
      diverges c1 st -> diverges (CSeq c1 c2) st
  | Dv_SeqR : forall c1 c2 st st',
      ceval c1 st st' -> diverges c2 st' -> diverges (CSeq c1 c2) st
  | Dv_IfTrue : forall b c1 c2 st,
      beval st b = true -> diverges c1 st -> diverges (CIf b c1 c2) st
  | Dv_IfFalse : forall b c1 c2 st,
      beval st b = false -> diverges c2 st -> diverges (CIf b c1 c2) st
  | Dv_WhileBody : forall b c st,
      beval st b = true -> diverges c st -> diverges (CWhile b c) st
  | Dv_WhileIter : forall b c st st',
      beval st b = true -> ceval c st st' ->
      diverges (CWhile b c) st' -> diverges (CWhile b c) st
  | Dv_ChoiceL : forall c1 c2 st,
      diverges c1 st -> diverges (CChoice c1 c2) st
  | Dv_ChoiceR : forall c1 c2 st,
      diverges c2 st -> diverges (CChoice c1 c2) st.

Lemma diverges_skip : forall st, ~ diverges CSkip st.
Proof. intros st H. inversion H. Qed.

Lemma diverges_asgn : forall x a st, ~ diverges (CAsgn x a) st.
Proof. intros x a st H. inversion H. Qed.

Lemma diverges_havoc : forall x st, ~ diverges (CHavoc x) st.
Proof. intros x st H. inversion H. Qed.

(** [while true skip] diverges from every state. *)
Lemma loop_forever : forall st, diverges (CWhile BTrue CSkip) st.
Proof.
  cofix CH. intros st.
  eapply Dv_WhileIter; [reflexivity | apply E_Skip | apply CH].
Qed.
