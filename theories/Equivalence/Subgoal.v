(** * Subgoal induction (node 14 of Cousot's figure)

    Morris and Wegbreit's subgoal induction (CACM 1977) proves
    input/output properties: an assertion [Q s t] relates a run's initial
    state [s] to its final state [t]. Loops are proved by induction on
    the computation that *remains*: [Q] holds when the loop exits at
    once, and is preserved backwards across one iteration. Cousot places
    it at the [p̃re ⊆] corner, which a Galois connection identifies with
    Hoare logic.

    [sgi c Q] is subgoal induction for Imp, in that style: [SG_While]
    asks for exit and backward-step conditions on a loop relation [I],
    with the body described by its own subgoal [Qb].

    - [sgi_sound], [sgi_complete]: [sgi c Q] holds exactly when every
      run satisfies [Q]; completeness takes the program's own relation
      as the assertion.
    - [sgi_iff_generated]: a Hoare-style triple [(P, c, Q)], as the
      relation [P s → Q t], is proved by subgoal induction exactly when
      the generated logic at the [p̃re ⊆] corner derives it.

    The rules are reconstructed from the method's standard presentation,
    not copied from the paper. Constructive. *)

From LogicTransformers.Imp Require Import Syntax BigStep Lang Hoare.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Verified.
From LogicTransformers.Core Require Import Kernel ImpCore.
From LogicTransformers.Examples Require Import Common.

Definition rel := state -> state -> Prop.

Inductive sgi : com -> rel -> Prop :=
  | SG_Skip : forall (Q : rel), (forall s, Q s s) -> sgi CSkip Q
  | SG_Asgn : forall (Q : rel) x a,
      (forall s, Q s (update s x (aeval s a))) -> sgi (CAsgn x a) Q
  | SG_Havoc : forall (Q : rel) x,
      (forall s n, Q s (update s x n)) -> sgi (CHavoc x) Q
  | SG_Seq : forall (Q Q1 Q2 : rel) c1 c2,
      sgi c1 Q1 -> sgi c2 Q2 ->
      (forall s m t, Q1 s m -> Q2 m t -> Q s t) -> sgi (CSeq c1 c2) Q
  | SG_If : forall (Q Q1 Q2 : rel) b c1 c2,
      sgi c1 Q1 -> sgi c2 Q2 ->
      (forall s t, bassn b s -> Q1 s t -> Q s t) ->
      (forall s t, ~ bassn b s -> Q2 s t -> Q s t) ->
      sgi (CIf b c1 c2) Q
  | SG_While : forall (I Qb : rel) b c,
      sgi c Qb ->
      (forall s, ~ bassn b s -> I s s) ->
      (forall s m t, bassn b s -> Qb s m -> I m t -> I s t) ->
      sgi (CWhile b c) I
  | SG_Choice : forall (Q : rel) c1 c2,
      sgi c1 Q -> sgi c2 Q -> sgi (CChoice c1 c2) Q
  | SG_Cons : forall (Q Q' : rel) c,
      (forall s t, Q' s t -> Q s t) -> sgi c Q' -> sgi c Q.

Theorem sgi_sound : forall c Q, sgi c Q -> forall s t, ceval c s t -> Q s t.
Proof.
  intros c Q H. induction H; intros s t Hc.
  - inversion Hc; subst. apply H.
  - inversion Hc; subst. apply H.
  - inversion Hc; subst. apply H.
  - inversion Hc; subst. eapply H1; [apply IHsgi1 | apply IHsgi2]; eassumption.
  - inversion Hc; subst.
    + apply H1; [assumption | apply IHsgi1; assumption].
    + apply H2; [apply bassn_false'; assumption | apply IHsgi2; assumption].
  - remember (CWhile b c) as w eqn:Ew. induction Hc; inversion Ew; subst.
    + apply H0, bassn_false'. assumption.
    + eapply H1; [assumption | apply IHsgi; eassumption |].
      apply IHHc2; reflexivity.
  - inversion Hc; subst; [apply IHsgi1 | apply IHsgi2]; assumption.
  - apply H, IHsgi, Hc.
Qed.

Lemma sgi_ceval : forall c, sgi c (ceval c).
Proof.
  induction c as [| x a | c1 IH1 c2 IH2 | b c1 IH1 c2 IH2 | b c IH
                  | c1 IH1 c2 IH2 | x].
  - apply SG_Skip. intros. apply E_Skip.
  - apply SG_Asgn. intros. apply E_Asgn.
  - eapply SG_Seq; [exact IH1 | exact IH2 |].
    intros. eapply E_Seq; eassumption.
  - eapply SG_If; [exact IH1 | exact IH2 | |].
    + intros. apply E_IfTrue; assumption.
    + intros. apply E_IfFalse; [apply bassn_false |]; assumption.
  - eapply SG_While; [exact IH | |].
    + intros. apply E_WhileFalse, bassn_false. assumption.
    + intros. eapply E_WhileTrue; eassumption.
  - apply SG_Choice.
    + eapply SG_Cons; [| exact IH1]. intros. apply E_ChoiceL. assumption.
    + eapply SG_Cons; [| exact IH2]. intros. apply E_ChoiceR. assumption.
  - apply SG_Havoc. intros. apply E_Havoc.
Qed.

Theorem sgi_complete : forall c (Q : rel),
    (forall s t, ceval c s t -> Q s t) -> sgi c Q.
Proof. intros c Q H. eapply SG_Cons; [exact H | apply sgi_ceval]. Qed.

(** Against the generated logic at the [p̃re ⊆] corner. *)
Theorem sgi_iff_generated : forall (P Q : state -> Prop) c,
    sgi c (fun s t => P s -> Q t) <->
    derivable (rules (vl_logic (PreDUv iact_sem)))
      (@mkTriple ICore P (enc c) Q).
Proof.
  intros P Q c. rewrite vl_theory, <- enc_cvalid, cvalid_Imp_rel. simpl.
  split.
  - intros H s HP t Hc. exact (sgi_sound c _ H s t Hc HP).
  - intros H. apply sgi_complete. intros s t Hc HP. exact (H s HP t Hc).
Qed.
