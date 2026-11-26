(** * Cook's relative completeness, with syntactic assertions

    The rest of the development takes assertions to be predicates of the
    meta-logic, which makes weakest preconditions expressible for free.
    Here assertions are syntax: any formula language [F] with a
    denotation and a few constructs (substitution, universal
    quantification over a variable, conjunction, conjunction with a
    guard or its negation, implication from a guard or its negation),
    each specified by its denotation ([FoLang]).

    - [hs]: Hoare logic over formulas, with Cook's consequence rule
      (implications decided by an oracle, here entailment between
      denotations); sound ([hs_sound]).
    - [hs_complete]: complete *relative to expressiveness*, and only of
      the loops the program contains ([loops_expressive]): for each loop
      and postcondition, some formula denotes the loop's weakest liberal
      precondition. This is Cook's theorem.
    - [Fo]: a concrete first-order language over Imp states (boolean
      expressions, connectives, quantifiers over program variables,
      explicit substitution). [fo_complete_loop_free]: for loop-free
      programs no assumption is needed. Loops need quantifiers over
      numbers, not just program variables: [Equivalence.Godel] adds
      them, codes loop traces with Gödel's β-function, and proves
      completeness for all of Imp outright ([fa_complete]).
    - [sem_complete]: semantic assertions are the degenerate, trivially
      expressive instance used elsewhere. Constructive. *)

From LogicTransformers.Imp Require Import Syntax BigStep.
From LogicTransformers.Imp Require Import Hoare.

Definition wlpc (c : com) (Q : assertion) : assertion :=
  fun s => forall s', ceval c s s' -> Q s'.

Record FoLang := mkFoLang {
  form : Type;
  den : form -> assertion;
  fsub : var -> aexp -> form -> form;
  fall : var -> form -> form;
  fand : form -> form -> form;
  fwith : bexp -> form -> form;
  fwithout : bexp -> form -> form;
  fif : bexp -> form -> form;       (* b -> f *)
  fifnot : bexp -> form -> form;    (* not b -> f *)
  den_sub : forall x a f s,
    den (fsub x a f) s <-> den f (update s x (aeval s a));
  den_all : forall x f s, den (fall x f) s <-> forall n, den f (update s x n);
  den_and : forall f g s, den (fand f g) s <-> den f s /\ den g s;
  den_with : forall b f s, den (fwith b f) s <-> den f s /\ bassn b s;
  den_without : forall b f s,
    den (fwithout b f) s <-> den f s /\ ~ bassn b s;
  den_if : forall b f s, den (fif b f) s <-> (bassn b s -> den f s);
  den_ifnot : forall b f s, den (fifnot b f) s <-> (~ bassn b s -> den f s)
}.

Section Cook.

Variable FL : FoLang.
Notation F := (form FL).
Notation den := (den FL).

Inductive hs : F -> com -> F -> Prop :=
  | HS_Skip : forall f, hs f CSkip f
  | HS_Asgn : forall f x a, hs (fsub FL x a f) (CAsgn x a) f
  | HS_Havoc : forall f x, hs (fall FL x f) (CHavoc x) f
  | HS_Seq : forall f g h c1 c2, hs f c1 g -> hs g c2 h -> hs f (CSeq c1 c2) h
  | HS_If : forall f g b c1 c2,
      hs (fwith FL b f) c1 g -> hs (fwithout FL b f) c2 g ->
      hs f (CIf b c1 c2) g
  | HS_While : forall i b c,
      hs (fwith FL b i) c i -> hs i (CWhile b c) (fwithout FL b i)
  | HS_Choice : forall f g c1 c2,
      hs f c1 g -> hs f c2 g -> hs f (CChoice c1 c2) g
  | HS_Cons : forall f f' g g' c,
      (forall s, den f s -> den f' s) -> (forall s, den g' s -> den g s) ->
      hs f' c g' -> hs f c g.

(** ** Soundness, through the semantic Hoare logic *)

Theorem hs_sound : forall f c g, hs f c g -> hoare_valid (den f) c (den g).
Proof.
  intros f c g H. apply hoare_sound. induction H.
  - apply H_Skip.
  - eapply H_Consequence_pre; [apply H_Asgn |].
    intros s Hs. apply (den_sub FL), Hs.
  - eapply H_Consequence_pre; [apply H_Havoc |].
    intros s Hs n. apply (den_all FL), Hs.
  - eapply H_Seq; eassumption.
  - apply H_If.
    + eapply H_Consequence_pre; [exact IHhs1 |].
      intros s [Hf Hb]. apply (den_with FL). auto.
    + eapply H_Consequence_pre; [exact IHhs2 |].
      intros s [Hf Hb]. apply (den_without FL). auto.
  - eapply H_Consequence_post;
      [apply H_While; eapply H_Consequence_pre; [exact IHhs |] |].
    + intros s [Hi Hb]. apply (den_with FL). auto.
    + intros s Hs. apply (den_without FL), Hs.
  - apply H_Choice; assumption.
  - eapply H_Consequence; [exact IHhs | |]; assumption.
Qed.

(** ** Completeness relative to expressiveness of loops *)

Definition expresses (c : com) : Prop :=
  forall g, exists f, forall s, den f s <-> wlpc c (den g) s.

Fixpoint loops_expressive (c : com) : Prop :=
  match c with
  | CSeq c1 c2 | CIf _ c1 c2 | CChoice c1 c2 =>
      loops_expressive c1 /\ loops_expressive c2
  | CWhile b c0 => expresses (CWhile b c0) /\ loops_expressive c0
  | _ => True
  end.

Ltac same := intros ? H; exact H.

(** For every postcondition there is a provable precondition that
    contains the weakest liberal precondition. *)
Lemma hs_wlp : forall c, loops_expressive c -> forall g,
    exists f, hs f c g /\ forall s, wlpc c (den g) s -> den f s.
Proof.
  induction c as [| x a | c1 IH1 c2 IH2 | b c1 IH1 c2 IH2 | b c IH
                  | c1 IH1 c2 IH2 | x]; intros Hle g; simpl in Hle.
  - exists g. split; [apply HS_Skip |]. intros s H. apply H, E_Skip.
  - exists (fsub FL x a g). split; [apply HS_Asgn |].
    intros s H. apply (den_sub FL), H, E_Asgn.
  - destruct Hle as [L1 L2].
    destruct (IH2 L2 g) as [f2 [D2 W2]].
    destruct (IH1 L1 f2) as [f1 [D1 W1]].
    exists f1. split; [eapply HS_Seq; eassumption |].
    intros s H. apply W1. intros s1 H1. apply W2. intros s2 H2.
    apply H. eapply E_Seq; eassumption.
  - destruct Hle as [L1 L2].
    destruct (IH1 L1 g) as [f1 [D1 W1]]. destruct (IH2 L2 g) as [f2 [D2 W2]].
    exists (fand FL (fif FL b f1) (fifnot FL b f2)). split.
    + apply HS_If.
      * eapply HS_Cons; [| same | exact D1].
        intros s Hs. apply (den_with FL) in Hs. destruct Hs as [Hs Hb].
        apply (den_and FL) in Hs. destruct Hs as [Hs _].
        apply (den_if FL) in Hs; assumption.
      * eapply HS_Cons; [| same | exact D2].
        intros s Hs. apply (den_without FL) in Hs. destruct Hs as [Hs Hb].
        apply (den_and FL) in Hs. destruct Hs as [_ Hs].
        apply (den_ifnot FL) in Hs; assumption.
    + intros s H. apply (den_and FL). split.
      * apply (den_if FL). intros Hb. apply W1. intros s' Hc.
        apply H, E_IfTrue; assumption.
      * apply (den_ifnot FL). intros Hb. apply W2. intros s' Hc.
        apply H, E_IfFalse; [apply bassn_false, Hb | exact Hc].
  - destruct Hle as [Hex L].
    destruct (Hex g) as [i Hi].
    destruct (IH L i) as [f [D W]].
    exists i. split.
    + eapply HS_Cons; [same | | apply HS_While].
      * intros s Hs. apply (den_without FL) in Hs. destruct Hs as [Hs Hb].
        apply Hi in Hs. apply Hs, E_WhileFalse, bassn_false, Hb.
      * eapply HS_Cons; [| same | exact D].
        intros s Hs. apply (den_with FL) in Hs. destruct Hs as [Hs Hb].
        apply W. intros s' Hc. apply Hi. intros s'' Hw.
        apply Hi in Hs. apply Hs. eapply E_WhileTrue; eassumption.
    + intros s H. apply Hi, H.
  - destruct Hle as [L1 L2].
    destruct (IH1 L1 g) as [f1 [D1 W1]]. destruct (IH2 L2 g) as [f2 [D2 W2]].
    exists (fand FL f1 f2). split.
    + apply HS_Choice.
      * eapply HS_Cons; [| same | exact D1].
        intros s Hs. apply (den_and FL) in Hs. apply (proj1 Hs).
      * eapply HS_Cons; [| same | exact D2].
        intros s Hs. apply (den_and FL) in Hs. apply (proj2 Hs).
    + intros s H. apply (den_and FL). split.
      * apply W1. intros s' Hc. apply H, E_ChoiceL, Hc.
      * apply W2. intros s' Hc. apply H, E_ChoiceR, Hc.
  - exists (fall FL x g). split; [apply HS_Havoc |].
    intros s H. apply (den_all FL). intros n. apply H, E_Havoc.
Qed.

Theorem hs_complete : forall f c g, loops_expressive c ->
    hoare_valid (den f) c (den g) -> hs f c g.
Proof.
  intros f c g Hle V. destruct (hs_wlp c Hle g) as [f' [D W]].
  eapply HS_Cons; [| same | exact D].
  intros s Hf. apply W. intros s' Hc. exact (V s s' Hf Hc).
Qed.

End Cook.

(** ** A first-order assertion language for Imp *)

Inductive fo : Type :=
  | FB (b : bexp)
  | FNot (f : fo)
  | FAnd (f g : fo)
  | FOr (f g : fo)
  | FAll (x : var) (f : fo)
  | FEx (x : var) (f : fo)
  | FSub (x : var) (a : aexp) (f : fo).

Fixpoint fden (f : fo) (s : state) : Prop :=
  match f with
  | FB b => bassn b s
  | FNot f => ~ fden f s
  | FAnd f g => fden f s /\ fden g s
  | FOr f g => fden f s \/ fden g s
  | FAll x f => forall n, fden f (update s x n)
  | FEx x f => exists n, fden f (update s x n)
  | FSub x a f => fden f (update s x (aeval s a))
  end.

Definition fimp (f g : fo) : fo := FOr (FNot f) g.

Lemma fimp_den : forall b f s,
    fden (fimp (FB b) f) s <-> (bassn b s -> fden f s).
Proof.
  intros b f s. simpl. unfold bassn. split.
  - intros [H | H] Hb; [contradiction | exact H].
  - intros H. destruct (beval s b); [right; apply H | left]; congruence.
Qed.

Lemma fimpnot_den : forall b f s,
    fden (fimp (FNot (FB b)) f) s <-> (~ bassn b s -> fden f s).
Proof.
  intros b f s. simpl. unfold bassn. split.
  - intros [H | H] Hb; [contradiction | exact H].
  - intros H. destruct (beval s b) eqn:E; [left | right; apply H];
      congruence.
Qed.

Definition Fo : FoLang.
Proof.
  refine (mkFoLang fo fden FSub FAll FAnd
            (fun b f => FAnd f (FB b)) (fun b f => FAnd f (FNot (FB b)))
            (fun b f => fimp (FB b) f) (fun b f => fimp (FNot (FB b)) f)
            _ _ _ _ _ _ _).
  - intros. reflexivity.
  - intros. reflexivity.
  - intros. reflexivity.
  - intros. reflexivity.
  - intros. reflexivity.
  - intros. apply fimp_den.
  - intros. apply fimpnot_den.
Defined.

Fixpoint loop_free (c : com) : Prop :=
  match c with
  | CSeq c1 c2 | CIf _ c1 c2 | CChoice c1 c2 => loop_free c1 /\ loop_free c2
  | CWhile _ _ => False
  | _ => True
  end.

Lemma loop_free_expressive : forall FL c, loop_free c -> loops_expressive FL c.
Proof.
  intros FL c. induction c; simpl; tauto.
Qed.

(** Syntactic Hoare logic is complete for loop-free Imp programs, with
    first-order formulas, and no expressiveness assumption. *)
Theorem fo_complete_loop_free : forall f c g, loop_free c ->
    hoare_valid (fden f) c (fden g) -> hs Fo f c g.
Proof.
  intros f c g Hlf V. apply hs_complete; [apply loop_free_expressive, Hlf |].
  exact V.
Qed.

(** ** Semantic assertions: the trivially expressive instance *)

Definition Sem : FoLang.
Proof.
  refine (mkFoLang assertion (fun P => P) (fun x a P => assn_sub x a P)
            (fun x P s => forall n, P (update s x n))
            (fun P Q s => P s /\ Q s)
            (fun b P s => P s /\ bassn b s) (fun b P s => P s /\ ~ bassn b s)
            (fun b P s => bassn b s -> P s) (fun b P s => ~ bassn b s -> P s)
            _ _ _ _ _ _ _); intros; reflexivity.
Defined.

Lemma sem_expressive : forall c, loops_expressive Sem c.
Proof.
  induction c; simpl; try tauto.
  split; [| assumption].
  intros g. exists (wlpc (CWhile b c) g). intros s. reflexivity.
Qed.

Theorem sem_complete : forall P c Q, hoare_valid P c Q -> hs Sem P c Q.
Proof. intros P c Q V. apply hs_complete; [apply sem_expressive | exact V]. Qed.
