(** * Verscht and Kaminski's taxonomy, as corners of the cube

    Verscht and Kaminski (POPL 2025, "A Taxonomy of Hoare-Like Logics")
    define eight predicate transformers on a nondeterministic program and
    obtain sixteen logics by over- or under-approximating each. Their
    divergence is informal ("[p] can diverge on [σ]"). Here a program's
    behaviour is a relation [R] (terminating runs) and a predicate [D]
    (initial states from which some run diverges), and the definitions
    follow their Definitions 3.1 to 3.6:

<<
      awp  c σ = ∃τ. R σ τ ∧ c τ          dwlp c σ = ∀τ. R σ τ → c τ
      dwp  c σ = ¬D σ ∧ ∀τ. R σ τ → c τ   awlp c σ = D σ ∨ ∃τ. R σ τ ∧ c τ
      asp  b τ = ∃σ. R σ τ ∧ b σ          dslp b τ = ∀σ. R σ τ → b σ
      dsp  b τ = (∃σ. R σ τ) ∧ dslp b τ   aslp b τ = (¬∃σ. R σ τ) ∨ asp b τ
>>

    [taxonomy_in_cube]: each of their sixteen logics is exactly one
    corner of one of three cubes:
    - 8 on the ordinary face of the program ([R]): the logics built from
      [awp], [dwlp], [asp], [dslp] (Hoare, incorrectness, Lisbon or SIL,
      necessary preconditions, partial incorrectness, and their
      contrapositives);
    - 4 on the nontermination-aware face ([RB]: [None] is divergence):
      the logics built from [dwp] and [awlp] (total correctness, angelic
      partial correctness, and their contrapositives);
    - 4 on the nontermination-aware face of the *inverse* program, with
      [None] read as *unreachability* ([RU]): the logics built from [dsp]
      and [aslp], which they introduce as new and note are absent from
      Cousot's cube.

    The last group answers their conjecture that the cube could be
    extended with "an additional symbol representing unreachability, dual
    to ⊥": no new symbol is needed, only the existing ⊥ of the inverse
    program. Assertions on [option] states are lifted with [lift b x]
    ([b] on proper states, [x] on ⊥).

    Two of the sixteen use [classic] ([dsp] needs "a predecessor exists"
    from "not unreachable"); the rest are constructive. *)

From Stdlib Require Import Classical.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Relational.

Section Taxonomy.

Context {St : Type} (R : St -> St -> Prop) (D : St -> Prop).

Definition sub (P Q : St -> Prop) : Prop := forall s, P s -> Q s.

(** ** Their eight transformers *)

Definition awp (c : St -> Prop) : St -> Prop :=
  fun s => exists t, R s t /\ c t.
Definition dwlp (c : St -> Prop) : St -> Prop :=
  fun s => forall t, R s t -> c t.
Definition dwp (c : St -> Prop) : St -> Prop :=
  fun s => ~ D s /\ forall t, R s t -> c t.
Definition awlp (c : St -> Prop) : St -> Prop :=
  fun s => D s \/ exists t, R s t /\ c t.
Definition asp (b : St -> Prop) : St -> Prop :=
  fun t => exists s, R s t /\ b s.
Definition dslp (b : St -> Prop) : St -> Prop :=
  fun t => forall s, R s t -> b s.
Definition dsp (b : St -> Prop) : St -> Prop :=
  fun t => (exists s, R s t) /\ forall s, R s t -> b s.
Definition aslp (b : St -> Prop) : St -> Prop :=
  fun t => (~ exists s, R s t) \/ exists s, R s t /\ b s.

(** ** The three relations *)

(** Nontermination-aware: [None] is divergence. *)
Definition RB (o o' : option St) : Prop :=
  match o, o' with
  | Some s, Some s' => R s s'
  | Some s, None => D s
  | None, None => True
  | None, Some _ => False
  end.

(** The inverse program, with [None] as unreachability: a final state
    steps back to its initial states, or to [None] when it has none. *)
Definition RU (o o' : option St) : Prop :=
  match o, o' with
  | Some t, Some s => R s t
  | Some t, None => ~ exists s, R s t
  | None, None => True
  | None, Some _ => False
  end.

Definition lift (b : St -> Prop) (x : Prop) : option St -> Prop :=
  fun o => match o with Some s => b s | None => x end.

(** ** The ordinary face: 8 logics *)

Lemma hl_partial : forall b c,
    sub (asp b) c <-> cvr b c Forward Plain Over R.
Proof.
  intros b c. unfold sub, asp. simpl. split.
  - intros H s s' Hb Hr. apply H. eauto.
  - intros H t [s [Hr Hb]]. eauto.
Qed.

Lemma hl_partial_wlp : forall b c,
    sub b (dwlp c) <-> cvr b c Backward Dual Under R.
Proof. intros b c. unfold sub, dwlp. simpl. tauto. Qed.

Lemma il : forall b c, sub c (asp b) <-> cvr b c Forward Plain Under R.
Proof.
  intros b c. unfold sub, asp. simpl. split.
  - intros H t Hc. destruct (H t Hc) as [s [Hr Hb]]. eauto.
  - intros H t Hc. destruct (H t Hc) as [s [Hb Hr]]. eauto.
Qed.

Lemma lisbon : forall b c, sub b (awp c) <-> cvr b c Backward Plain Under R.
Proof. intros b c. unfold sub, awp. simpl. tauto. Qed.

Lemma necessary : forall b c,
    sub (awp c) b <-> cvr b c Backward Plain Over R.
Proof.
  intros b c. unfold sub, awp. simpl. split.
  - intros H s t Hr Hc. apply H. eauto.
  - intros H s [t [Hr Hc]]. eauto.
Qed.

Lemma partial_incorrectness : forall b c,
    sub c (dslp b) <-> cvr b c Forward Dual Under R.
Proof. intros b c. unfold sub, dslp. simpl. tauto. Qed.

Lemma dslp_over : forall b c,
    sub (dslp b) c <-> cvr b c Forward Dual Over R.
Proof. intros b c. unfold sub, dslp. simpl. tauto. Qed.

Lemma dwlp_over : forall b c,
    sub (dwlp c) b <-> cvr b c Backward Dual Over R.
Proof. intros b c. unfold sub, dwlp. simpl. tauto. Qed.

(** ** The nontermination-aware face: 4 logics *)

Lemma total_correctness : forall b c,
    sub b (dwp c) <->
    cvr (lift b False) (lift c False) Forward Plain Over RB.
Proof.
  intros b c. unfold sub, dwp. simpl. split.
  - intros H [s|] [s'|] Hb Hr; simpl in *; try contradiction.
    + exact (proj2 (H s Hb) s' Hr).
    + exact (proj1 (H s Hb) Hr).
  - intros H s Hb. split.
    + intros Hd. exact (H (Some s) None Hb Hd).
    + intros t Hr. exact (H (Some s) (Some t) Hb Hr).
Qed.

Lemma angelic_partial : forall b c,
    sub b (awlp c) <->
    cvr (lift b False) (lift c True) Backward Plain Under RB.
Proof.
  intros b c. unfold sub, awlp. simpl. split.
  - intros H [s|] Hb; simpl in *; [| contradiction].
    destruct (H s Hb) as [Hd | [t [Hr Hc]]].
    + exists None. simpl. auto.
    + exists (Some t). simpl. auto.
  - intros H s Hb. destruct (H (Some s) Hb) as [[t|] [Hr Hc]]; simpl in *.
    + right. eauto.
    + left. exact Hr.
Qed.

Lemma dwp_over : forall b c,
    sub (dwp c) b <->
    cvr (lift b True) (lift c False) Backward Dual Over RB.
Proof.
  intros b c. unfold sub, dwp. simpl. split.
  - intros H [s|] Hall; simpl in *; [| exact I].
    apply H. split.
    + intros Hd. exact (Hall None Hd).
    + intros t Hr. exact (Hall (Some t) Hr).
  - intros H s [Hd Hall]. apply (H (Some s)). intros [t|] Hr; simpl in *.
    + exact (Hall t Hr).
    + exact (Hd Hr).
Qed.

Lemma awlp_over : forall b c,
    sub (awlp c) b <->
    cvr (lift b True) (lift c True) Backward Plain Over RB.
Proof.
  intros b c. unfold sub, awlp. simpl. split.
  - intros H [s|] [s'|] Hr Hc; simpl in *; try contradiction; try exact I.
    + apply H. right. eauto.
    + apply H. left. exact Hr.
  - intros H s [Hd | [t [Hr Hc]]].
    + exact (H (Some s) None Hd I).
    + exact (H (Some s) (Some t) Hr Hc).
Qed.

(** ** The inverse program, with unreachability as ⊥: 4 logics *)

Lemma demonic_incorrectness : forall b c,
    sub c (dsp b) <->
    cvr (lift c False) (lift b False) Forward Plain Over RU.
Proof.
  intros b c. unfold sub, dsp. simpl. split.
  - intros H [t|] [s|] Hc Hr; simpl in *; try contradiction.
    + exact (proj2 (H t Hc) s Hr).
    + exact (Hr (proj1 (H t Hc))).
  - intros H t Hc. split.
    + apply NNPP. intros Hn. exact (H (Some t) None Hc Hn).
    + intros s Hr. exact (H (Some t) (Some s) Hc Hr).
Qed.

Lemma angelic_partial_incorrectness : forall b c,
    sub c (aslp b) <->
    cvr (lift c False) (lift b True) Backward Plain Under RU.
Proof.
  intros b c. unfold sub, aslp. simpl. split.
  - intros H [t|] Hc; simpl in *; [| contradiction].
    destruct (H t Hc) as [Hn | [s [Hr Hb]]].
    + exists None. simpl. auto.
    + exists (Some s). simpl. auto.
  - intros H t Hc. destruct (H (Some t) Hc) as [[s|] [Hr Hb]]; simpl in *.
    + right. eauto.
    + left. exact Hr.
Qed.

Lemma dsp_over : forall b c,
    sub (dsp b) c <->
    cvr (lift c True) (lift b False) Backward Dual Over RU.
Proof.
  intros b c. unfold sub, dsp. simpl. split.
  - intros H [t|] Hall; simpl in *; [| exact I].
    apply H. split.
    + apply NNPP. intros Hn. exact (Hall None Hn).
    + intros s Hr. exact (Hall (Some s) Hr).
  - intros H t [Hex Hall]. apply (H (Some t)). intros [s|] Hr; simpl in *.
    + exact (Hall s Hr).
    + exact (Hr Hex).
Qed.

Lemma aslp_over : forall b c,
    sub (aslp b) c <->
    cvr (lift c True) (lift b True) Backward Plain Over RU.
Proof.
  intros b c. unfold sub, aslp. simpl. split.
  - intros H [t|] [s|] Hr Hb; simpl in *; try contradiction; try exact I.
    + apply H. right. eauto.
    + apply H. left. exact Hr.
  - intros H t [Hn | [s [Hr Hb]]].
    + exact (H (Some t) None Hn I).
    + exact (H (Some t) (Some s) Hr Hb).
Qed.

(** ** All sixteen *)

Theorem taxonomy_in_cube : forall b c,
    (* ordinary face *)
    (sub (asp b) c <-> cvr b c Forward Plain Over R) /\
    (sub b (dwlp c) <-> cvr b c Backward Dual Under R) /\
    (sub c (asp b) <-> cvr b c Forward Plain Under R) /\
    (sub b (awp c) <-> cvr b c Backward Plain Under R) /\
    (sub (awp c) b <-> cvr b c Backward Plain Over R) /\
    (sub c (dslp b) <-> cvr b c Forward Dual Under R) /\
    (sub (dslp b) c <-> cvr b c Forward Dual Over R) /\
    (sub (dwlp c) b <-> cvr b c Backward Dual Over R) /\
    (* nontermination as ⊥ *)
    (sub b (dwp c) <->
       cvr (lift b False) (lift c False) Forward Plain Over RB) /\
    (sub b (awlp c) <->
       cvr (lift b False) (lift c True) Backward Plain Under RB) /\
    (sub (dwp c) b <->
       cvr (lift b True) (lift c False) Backward Dual Over RB) /\
    (sub (awlp c) b <->
       cvr (lift b True) (lift c True) Backward Plain Over RB) /\
    (* the inverse program, unreachability as ⊥ *)
    (sub c (dsp b) <->
       cvr (lift c False) (lift b False) Forward Plain Over RU) /\
    (sub c (aslp b) <->
       cvr (lift c False) (lift b True) Backward Plain Under RU) /\
    (sub (dsp b) c <->
       cvr (lift c True) (lift b False) Backward Dual Over RU) /\
    (sub (aslp b) c <->
       cvr (lift c True) (lift b True) Backward Plain Over RU).
Proof.
  intros b c.
  repeat (split; [solve [first
    [ apply hl_partial | apply hl_partial_wlp | apply il | apply lisbon
    | apply necessary | apply partial_incorrectness | apply dslp_over
    | apply dwlp_over | apply total_correctness | apply angelic_partial
    | apply dwp_over | apply awlp_over | apply demonic_incorrectness
    | apply angelic_partial_incorrectness | apply dsp_over ]] |]).
  apply aslp_over.
Qed.

End Taxonomy.

(** For a language with a nontermination-aware semantics, [RB] is that
    semantics. For example, for the core language, [RB (kev c) (kdiv c)]
    is [semKB c], so their total correctness is HL on the core's bottom
    face. *)
Lemma RB_language : forall (St : Type) (semB : option St -> option St -> Prop),
    (forall o', semB None o' <-> o' = None) ->
    forall o o',
    semB o o' <->
    RB (fun s s' => semB (Some s) (Some s')) (fun s => semB (Some s) None) o o'.
Proof.
  intros St semB Hn [s|] [s'|]; simpl; try tauto.
  - rewrite Hn. split; [discriminate | intros []].
  - rewrite Hn. tauto.
Qed.
