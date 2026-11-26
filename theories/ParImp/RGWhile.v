(** * The rely/guarantee while rule is incomplete under interference

    The while rule of [ParImp.RelyGuarantee] (and of [ParImp.RGGhost])
    concludes [{I} while b do c {I ∧ ¬b}] and requires [I ∧ ¬b] to be
    stable under the rely. An environment that may change the loop test
    after the loop has exited breaks this, so the rules are incomplete
    even for sequential programs, and auxiliary variables do not help:

    - [spin]: [while x = 0 do skip];
    - [spin_valid]: under a rely that may change anything, the triple
      [{true} spin {true}] is valid, for any guarantee;
    - [spin_not_rgx]: no derivation proves it, even with auxiliary
      variables ([RGGhost.rgx]): its precondition forces the loop
      invariant to hold everywhere, and then [I ∧ ¬b] is not stable.

    So completeness of the compositional rules needs, besides auxiliary
    variables for parallel composition ([RGIncomplete]), a while rule
    whose exit condition is not required to be stable (for example one
    that weakens [I ∧ ¬b] to its closure under the rely). Axiom-free. *)

From Stdlib Require Import String Arith Lia.
From LogicTransformers.Imp Require Import Syntax.
From LogicTransformers.ParImp Require Import
  ParImp RelyGuarantee RGGhost.

Local Open Scope string_scope.
Local Notation X := "x".

Definition spin : pcom := PWhile (BEq (AVar X) (ANum 0)) PSkip.

(** Programs without assignments never change the state. *)
Fixpoint noasgn (c : pcom) : Prop :=
  match c with
  | PSkip => True
  | PAsgn _ _ | PMulti _ => False
  | PSeq c1 c2 | PPar c1 c2 => noasgn c1 /\ noasgn c2
  | PIf _ c1 c2 => noasgn c1 /\ noasgn c2
  | PWhile _ c => noasgn c
  end.

Lemma noasgn_step : forall c s c' s', noasgn c -> pstep (c, s) (c', s') ->
    noasgn c' /\ s' = s.
Proof.
  intros c s c' s' Hn H.
  remember (c, s) as k eqn:Ek. remember (c', s') as k' eqn:Ek'.
  revert c s c' s' Ek Ek' Hn.
  induction H; intros c0 s0 c0' s0' Ek Ek' Hn;
    injection Ek; injection Ek'; intros; subst; simpl in *;
    try contradiction; try tauto.
  - destruct Hn as [H1 H2].
    destruct (IHpstep _ _ _ _ eq_refl eq_refl H1). tauto.
  - destruct Hn as [H1 H2].
    destruct (IHpstep _ _ _ _ eq_refl eq_refl H1). tauto.
  - destruct Hn as [H1 H2].
    destruct (IHpstep _ _ _ _ eq_refl eq_refl H2). tauto.
Qed.

Lemma noasgn_reach : forall R c0 s0 k, noasgn c0 -> reach R (c0, s0) k ->
    noasgn (fst k).
Proof.
  intros R c0 s0 k Hn H. induction H; [exact Hn | |].
  - destruct k as [c s], k' as [c' s'].
    exact (proj1 (noasgn_step c s c' s' IHreach H0)).
  - exact IHreach.
Qed.

(** Valid: no step changes the state, and the post is [True]. *)
Theorem spin_valid : forall G, (forall s, G s s) ->
    rg_valid (fun _ _ => True) G (fun _ => True) spin (fun _ => True).
Proof.
  intros G HG s0 [c s] _ Hr. split; [| intros _; exact I].
  intros [c' s'] Hs. simpl.
  pose proof (noasgn_reach _ spin s0 (c, s) I Hr) as Hn.
  destruct (noasgn_step c s c' s' Hn Hs) as [_ ->]. apply HG.
Qed.

(** ** No derivation *)

Lemma rgx_while_inv : forall R G P b c Q, rgx R G P (PWhile b c) Q ->
    exists (R' : srel) (I : state -> Prop),
      (forall s s', R s s' -> R' s s') /\ (forall s, P s -> I s) /\
      stable R' (fun s => I s /\ beval s b = false).
Proof.
  intros R G P b c Q H. remember (PWhile b c) as w eqn:Ew.
  induction H; inversion Ew; subst.
  - exists R, I. split; [auto | split; [auto | assumption]].
  - destruct (IHrgx eq_refl) as [R'' [I [HR [HP HS]]]].
    exists R'', I. split; [auto | split; [auto | exact HS]].
Qed.

Theorem spin_not_rgx : forall G,
    ~ rgx (fun _ _ => True) G (fun _ => True) spin (fun _ => True).
Proof.
  intros G H. apply rgx_while_inv in H.
  destruct H as [R' [Inv [HR [HP HS]]]].
  set (s1 := update empty_state X 1).
  set (s0 := update empty_state X 0).
  assert (E : Inv s0 /\ beval s0 (BEq (AVar X) (ANum 0)) = false).
  { apply (HS s1 s0); [| apply HR; exact I].
    split; [apply HP; exact I | reflexivity]. }
  destruct E as [_ E]. discriminate.
Qed.

(** A valid triple that no derivation proves, with or without auxiliary
    variables. *)
Theorem rg_while_incomplete : forall G, (forall s, G s s) ->
    rg_valid (fun _ _ => True) G (fun _ => True) spin (fun _ => True) /\
    ~ rgx (fun _ _ => True) G (fun _ => True) spin (fun _ => True).
Proof.
  intros G HG. split; [apply spin_valid, HG | apply spin_not_rgx].
Qed.
