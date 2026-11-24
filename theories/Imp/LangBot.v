(** * Imp with nontermination: the bottom face's language

    States are [option state], with [None] standing for nontermination ⊥.
    A program relates [Some s] to [Some s'] when it can terminate in [s'],
    and to [None] when it can diverge. ⊥ is absorbing ([None] goes only to
    [None]), the strict extension that makes sequencing compose.

    Every cube notion over [ImpBot] is a bottom-face notion. For example
    [cvalid Forward Plain Over] on a triple whose post excludes [None] is
    total correctness. *)

From LogicTransformers.Framework Require Import Language.
From LogicTransformers.Imp Require Import Syntax BigStep Diverge.

Definition ostate := option state.

Definition semB (c : com) (o o' : ostate) : Prop :=
  match o, o' with
  | None, None => True
  | None, Some _ => False
  | Some s, Some s' => ceval c s s'
  | Some s, None => diverges c s
  end.

Definition ImpBot : Language := mkLanguage com ostate semB.

Lemma semB_none : forall c o', semB c None o' <-> o' = None.
Proof.
  intros c [s'|]; simpl; split; intros H;
    solve [contradiction | discriminate | reflexivity | exact I].
Qed.

Lemma semB_seq : forall c1 c2 o o'',
    semB (CSeq c1 c2) o o'' <-> exists o', semB c1 o o' /\ semB c2 o' o''.
Proof.
  intros c1 c2 [s|] [s''|]; simpl; split.
  - intros H. inversion H; subst. exists (Some st'). simpl. auto.
  - intros [[s'|] [H1 H2]]; [eapply E_Seq; eassumption | contradiction].
  - intros H. inversion H; subst.
    + exists None. simpl. auto.
    + exists (Some st'). simpl. auto.
  - intros [[s'|] [H1 H2]].
    + eapply Dv_SeqR; eassumption.
    + apply Dv_SeqL. exact H1.
  - contradiction.
  - intros [[s'|] [H1 H2]]; contradiction.
  - intros _. exists None. simpl. auto.
  - auto.
Qed.

Lemma semB_skip : forall o o', semB CSkip o o' <-> o' = o.
Proof.
  intros [s|] [s'|]; simpl; split; intros H.
  - inversion H; subst. reflexivity.
  - inversion H; subst. apply E_Skip.
  - apply diverges_skip in H. contradiction.
  - discriminate.
  - contradiction.
  - discriminate.
  - reflexivity.
  - exact I.
Qed.

Lemma semB_asgn : forall x a o o',
    semB (CAsgn x a) o o' <->
    match o with
    | None => o' = None
    | Some s => o' = Some (update s x (aeval s a))
    end.
Proof.
  intros x a [s|] [s'|]; simpl; split; intros H.
  - inversion H; subst. reflexivity.
  - inversion H; subst. apply E_Asgn.
  - apply diverges_asgn in H. contradiction.
  - discriminate.
  - contradiction.
  - discriminate.
  - reflexivity.
  - exact I.
Qed.

Lemma semB_havoc : forall x o o',
    semB (CHavoc x) o o' <->
    match o with
    | None => o' = None
    | Some s => exists n, o' = Some (update s x n)
    end.
Proof.
  intros x [s|] [s'|]; simpl; split; intros H.
  - inversion H; subst. exists n. reflexivity.
  - destruct H as [n Hn]. inversion Hn; subst. apply E_Havoc.
  - apply diverges_havoc in H. contradiction.
  - destruct H as [n Hn]. discriminate.
  - contradiction.
  - discriminate.
  - reflexivity.
  - exact I.
Qed.

Lemma semB_if : forall b c1 c2 s o',
    semB (CIf b c1 c2) (Some s) o' <->
    (beval s b = true /\ semB c1 (Some s) o') \/
    (beval s b = false /\ semB c2 (Some s) o').
Proof.
  intros b c1 c2 s [s'|]; simpl; split.
  - intros H. inversion H; subst; auto.
  - intros [[Hb H] | [Hb H]]; [apply E_IfTrue | apply E_IfFalse]; auto.
  - intros H. inversion H; subst; auto.
  - intros [[Hb H] | [Hb H]]; [apply Dv_IfTrue | apply Dv_IfFalse]; auto.
Qed.

Lemma semB_choice : forall c1 c2 o o',
    semB (CChoice c1 c2) o o' <-> semB c1 o o' \/ semB c2 o o'.
Proof.
  intros c1 c2 [s|] [s'|]; simpl; split; intros H.
  - inversion H; subst; auto.
  - destruct H as [H | H]; [apply E_ChoiceL | apply E_ChoiceR]; auto.
  - inversion H; subst; auto.
  - destruct H as [H | H]; [apply Dv_ChoiceL | apply Dv_ChoiceR]; auto.
  - contradiction.
  - destruct H as [H | H]; contradiction.
  - left. exact I.
  - exact I.
Qed.
