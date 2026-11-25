(** * One rule per logic for small-step languages

    Every program translated by [Core.SmallStepCore] has the same shape:
    load the program, then step while not finished. So every proof about
    one starts the same way: split off the load, apply the loop rule,
    handle the single-step body, weaken at the exit. The lemmas here do
    that once, leaving only the obligations that carry the proof's idea:

    - [hl_senc]: an invariant [I] on configurations, established by the
      load, preserved by each step, and implying the post at the end;
    - [il_senc]: a family [X n] of configurations after [n] steps, each
      reached from the previous one, with every target in some [X n];
    - [nc_senc]: a backward invariant, closed under predecessors;
    - [sil_senc]: a family [X m] of configurations [m] steps from the
      end, each with a step to the next.

    [Tutorial.ImpTutorial], [Examples.ParExample] and [Examples.RaceExample]
    show the long form; [countdown_HL_short] (in the tutorial) shows the
    short one. *)

From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Verified.
From LogicTransformers.Core Require Import Kernel SmallStepCore Rules.

Section SmallStepRules.

Context {Prog St : Type}.
Context (step : Prog * St -> Prog * St -> Prop) (done : Prog).

Notation cfg := (Prog * St)%type.
Notation asem := (sact_sem step).
Notation run := (running done).

Theorem hl_senc : forall (V : VLogic (KLang asem) Forward Plain Over)
    (P Q I : cfg -> Prop) p,
    (forall k, P k -> I (p, snd k)) ->
    (forall k k', I k -> run k -> step k k' -> I k') ->
    (forall k, I k -> ~ run k -> Q k) ->
    prov asem V P (senc done p) Q.
Proof.
  intros V P Q I p Hload Hstep Hexit. unfold senc, sloop.
  apply (hl_seq _ _ _ I).
  - apply (hl_cons _ _ _ (fun k => forall k', asem (SLoad p) k k' -> I k')
             _ I); [| apply hl_act | intros k H; exact H].
    intros k HP k' E. simpl in E. subst k'. apply Hload, HP.
  - apply (hl_cons _ _ _ I _ (fun k => I k /\ ~ run k));
      [intros k H; exact H | apply hl_while | intros k [H1 H2]; auto].
    apply (hl_cons _ _ _ (fun k => forall k', asem SStep k k' -> I k') _ I);
      [| apply hl_act | intros k H; exact H].
    intros k [HI Hr] k' Hs. exact (Hstep k k' HI Hr Hs).
Qed.

Theorem il_senc : forall (V : VLogic (KLang asem) Forward Plain Under)
    (P Q : cfg -> Prop) (X : nat -> cfg -> Prop) p,
    (forall k', X 0 k' -> exists k, P k /\ k' = (p, snd k)) ->
    (forall n k', X (S n) k' -> exists k, X n k /\ run k /\ step k k') ->
    (forall k, Q k -> exists n, X n k /\ ~ run k) ->
    prov asem V P (senc done p) Q.
Proof.
  intros V P Q X p Hload Hstep Hexit. unfold senc, sloop.
  apply (il_seq _ _ _ (X 0)).
  - apply (il_cons _ _ _ P _
             (fun k' => exists k, P k /\ asem (SLoad p) k k'));
      [intros k H; exact H | apply il_act |].
    intros k' Hx. destruct (Hload k' Hx) as [k [HP E]].
    exists k. split; [exact HP | exact E].
  - apply (il_cons _ _ _ (X 0) _ (fun k => exists n, X n k /\ ~ run k));
      [intros k H; exact H | apply il_while | exact Hexit].
    intros n.
    apply (il_cons _ _ _ (fun k => X n k /\ run k) _
             (fun k' => exists k, (X n k /\ run k) /\ asem SStep k k'));
      [intros k H; exact H | apply il_act |].
    intros k' Hx. destruct (Hstep n k' Hx) as [k [Hk [Hr Hs]]].
    exists k. auto.
Qed.

Theorem nc_senc : forall (V : VLogic (KLang asem) Backward Plain Over)
    (P Q I : cfg -> Prop) p,
    (forall k, I (p, snd k) -> P k) ->
    (forall k k', run k -> step k k' -> I k' -> I k) ->
    (forall k, Q k -> I k /\ ~ run k) ->
    prov asem V P (senc done p) Q.
Proof.
  intros V P Q I p Hload Hstep Hexit. unfold senc, sloop.
  apply (nc_seq _ _ _ I).
  - apply (nc_cons _ _ _ (fun k => exists k', asem (SLoad p) k k' /\ I k')
             _ I); [| apply nc_act | intros k H; exact H].
    intros k [k' [E HI]]. simpl in E. subst k'. apply Hload, HI.
  - apply (nc_cons _ _ _ I _ (fun k => I k /\ ~ run k));
      [intros k H; exact H | apply nc_while | exact Hexit].
    apply (nc_cons _ _ _ (fun k => exists k', asem SStep k k' /\ I k') _ I);
      [| apply nc_act | intros k H; exact H].
    intros k [k' [Hs HI]] Hr. exact (Hstep k k' Hr Hs HI).
Qed.

Theorem sil_senc : forall (V : VLogic (KLang asem) Backward Plain Under)
    (P Q : cfg -> Prop) (X : nat -> cfg -> Prop) p,
    (forall k, P k -> exists m, X m (p, snd k)) ->
    (forall m k, X (S m) k -> run k /\ exists k', step k k' /\ X m k') ->
    (forall k, X 0 k -> ~ run k /\ Q k) ->
    prov asem V P (senc done p) Q.
Proof.
  intros V P Q X p Hload Hstep Hexit. unfold senc, sloop.
  apply (sil_seq _ _ _ (fun k => exists m, X m k)).
  - apply (sil_cons _ _ _
             (fun k => exists k', asem (SLoad p) k k' /\ exists m, X m k')
             _ (fun k => exists m, X m k));
      [| apply sil_act | intros k H; exact H].
    intros k HP. exists (p, snd k). split; [reflexivity | exact (Hload k HP)].
  - apply (sil_cons _ _ _ (fun k => exists m, X m k) _ (X 0));
      [intros k H; exact H | apply sil_while | intros k H; apply Hexit, H].
    + intros m.
      apply (sil_cons _ _ _ (fun k => exists k', asem SStep k k' /\ X m k')
               _ (X m)); [| apply sil_act | intros k H; exact H].
      intros k Hx. exact (proj2 (Hstep m k Hx)).
    + intros m k Hx. exact (proj1 (Hstep m k Hx)).
    + intros k Hx. exact (proj1 (Hexit k Hx)).
Qed.

End SmallStepRules.
