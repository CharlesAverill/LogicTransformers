(** * A lost update, found with incorrectness logic

<<
      race  =  a := x ; x := a + 1   ∥   b := x ; x := b + 1
>>

    Two threads each increment [x] through a local copy. Starting from
    [x = 0], the intended result is [x = 2], but if both threads read
    [x] before either writes, one increment is lost and the program ends
    with [x = 1].

    - [race_IL]: incorrectness logic, proved with rules in the IL record
      computed by the transformers: every final state with [x = 1],
      [a = 0] and [b = 0] is reachable from a state with [x = 0]. The
      variant is the interleaving that loses the update ([d n s]: the
      configuration after [n] steps).
    - [race_lost_update]: the result read back for the concurrent program
      itself ([penc_cvalid]).
    - [race_not_correct]: the bug refutes the correctness claim: the
      Hoare triple [{x = 0} race {x = 2}] is *not* valid.

    Showing that the run lands on exactly the target state needs
    [functional_extensionality], because Imp states are functions. *)

From Stdlib Require Import String Arith Lia FunctionalExtensionality.
From LogicTransformers.Imp Require Import Syntax.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Relational Verified.
From LogicTransformers.Core Require Import
  Kernel KernelBot SmallStepCore Rules SmallStepRules.
From LogicTransformers.ParImp Require Import ParImp.
From LogicTransformers.Examples Require Import Common.
From LogicTransformers.Core Require Import TripleNotations.

Local Open Scope string_scope.
Local Open Scope triple_scope.

Local Notation X := "x".
Local Notation A := "a".
Local Notation B := "b".

Definition A1 : pcom := PAsgn A (AVar X).
Definition B1 : pcom := PAsgn X (APlus (AVar A) (ANum 1)).
Definition A2 : pcom := PAsgn B (AVar X).
Definition B2 : pcom := PAsgn X (APlus (AVar B) (ANum 1)).

Definition race : pcom := PPar (PSeq A1 B1) (PSeq A2 B2).

(** ** The interleaving that loses the update *)

Definition st1 (s : state) : state := update s A (s X).
Definition st2 (s : state) : state := update (st1 s) B (st1 s X).
Definition st5 (s : state) : state := update (st2 s) X (st2 s A + 1).
Definition st6 (s : state) : state := update (st5 s) X (st5 s B + 1).

Definition d (n : nat) (s : state) : pcfg :=
  match n with
  | 0 => (race, s)
  | 1 => (PPar (PSeq PSkip B1) (PSeq A2 B2), st1 s)
  | 2 => (PPar (PSeq PSkip B1) (PSeq PSkip B2), st2 s)
  | 3 => (PPar B1 (PSeq PSkip B2), st2 s)
  | 4 => (PPar B1 B2, st2 s)
  | 5 => (PPar PSkip B2, st5 s)
  | 6 => (PPar PSkip PSkip, st6 s)
  | _ => (PSkip, st6 s)
  end.

Lemma d_step : forall n s, n < 7 -> pstep (d n s) (d (S n) s).
Proof.
  intros n s Hn. destruct n as [|[|[|[|[|[|[|n]]]]]]]; try lia;
    simpl; repeat constructor.
Qed.

Lemma d_running : forall n s, n < 7 -> prunning (d n s).
Proof.
  intros n s Hn. destruct n as [|[|[|[|[|[|[|n]]]]]]]; try lia;
    unfold running; simpl; discriminate.
Qed.

(** Every lost-update outcome is the end of that interleaving. *)
Lemma st6_lost : forall s', s' X = 1 -> s' A = 0 -> s' B = 0 ->
    st6 (update s' X 0) = s'.
Proof.
  intros s' Hx Ha Hb. apply functional_extensionality. intros z.
  unfold st6, st5, st2, st1, update.
  destruct (String.eqb_spec X z) as [<- | Hz]; [simpl; lia |].
  destruct (String.eqb_spec B z) as [<- | Hz2]; [simpl; lia |].
  destruct (String.eqb_spec A z) as [<- | Hz3]; [simpl; lia |].
  reflexivity.
Qed.

Definition Lost (s : state) : Prop := s X = 1 /\ s A = 0 /\ s B = 0.

(** ** Incorrectness logic, with rules *)

Theorem race_IL :
  ILv pact_sem ⊢ ⟦ fun k => snd k X = 0 ⟧ penc race
                 ⟦ fun k => fst k = PSkip /\ Lost (snd k) ⟧.
Proof.
  set (Xn := fun n k => n <= 7 /\ exists s, s X = 0 /\ k = d n s).
  apply (il_seq _ _ _ (Xn 0)).
  - apply (il_cons _ _ _ (fun k => snd k X = 0) _
             (fun k' => exists k, snd k X = 0 /\
                                  pact_sem (SLoad race) k k'));
      [intros k H; exact H | apply il_act |].
    intros k' [_ [s [Hs ->]]]. exists (PSkip, s).
    split; [exact Hs | reflexivity].
  - apply (il_cons _ _ _ (Xn 0) _
             (fun k => exists n, Xn n k /\ ~ prunning k));
      [intros k H; exact H | apply il_while |].
    + intros n.
      apply (il_cons _ _ _ (fun k => Xn n k /\ prunning k) _
               (fun k' => exists k, (Xn n k /\ prunning k) /\
                                    pact_sem SStep k k'));
        [intros k H; exact H | apply il_act |].
      intros k' [Hn [s [Hs ->]]]. exists (d n s).
      split; [split; [split; [lia | eauto] | apply d_running; lia] |].
      apply d_step. lia.
    + intros [p s'] [Ep [Hx [Ha Hb]]]. simpl in Ep, Hx, Ha, Hb. subst p.
      exists 7. split; [split; [lia |] |].
      * exists (update s' X 0). split; [apply update_eq |].
        simpl. rewrite (st6_lost s' Hx Ha Hb). reflexivity.
      * intros Hr. apply Hr. reflexivity.
Qed.

(** The same proof with [Core.SmallStepRules.il_senc]: only the family
    of configurations and its three obligations remain. *)
Theorem race_IL_short :
  ILv pact_sem ⊢ ⟦ fun k => snd k X = 0 ⟧ penc race
                 ⟦ fun k => fst k = PSkip /\ Lost (snd k) ⟧.
Proof.
  apply (il_senc pstep PSkip _ _ _
           (fun n k => n <= 7 /\ exists s, s X = 0 /\ k = d n s)).
  - intros k' [_ [s [Hs ->]]]. exists (PSkip, s).
    split; [exact Hs | reflexivity].
  - intros n k' [Hn [s [Hs ->]]]. exists (d n s).
    split; [split; [lia | eauto] |].
    split; [apply d_running; lia | apply d_step; lia].
  - intros [p s'] [Ep [Hx [Ha Hb]]]. simpl in Ep, Hx, Ha, Hb. subst p.
    exists 7. split; [split; [lia |] |].
    + exists (update s' X 0). split; [apply update_eq |].
      simpl. rewrite (st6_lost s' Hx Ha Hb). reflexivity.
    + intros Hr. apply Hr. reflexivity.
Qed.

(** ** Back to the concurrent program *)

Corollary race_lost_update :
  cvalid Forward Plain Under
    (@mkTriple ParImp (fun s => s X = 0) race Lost).
Proof.
  apply (penc_cvalid Forward Plain Under), (vl_valid_of _ _ race_IL).
Qed.

(** The lost update refutes the intended specification. *)
Corollary race_not_correct :
  ~ cvalid Forward Plain Over
      (@mkTriple ParImp (fun s => s X = 0) race (fun s => s X = 2)).
Proof.
  intros Hhl.
  set (s' := update empty_state X 1).
  assert (Hl : Lost s').
  { unfold Lost, s'. repeat split; reflexivity. }
  pose proof (proj1 (cvalid_cvr ParImp _ _ race Forward Plain Under)
                    race_lost_update) as Hil.
  pose proof (proj1 (cvalid_cvr ParImp _ _ race Forward Plain Over) Hhl)
    as Hc.
  simpl in Hil, Hc. destruct (Hil s' Hl) as [s [Hs Hr]].
  pose proof (Hc s s' Hs Hr) as H2. unfold s' in H2.
  rewrite update_eq in H2. discriminate.
Qed.
