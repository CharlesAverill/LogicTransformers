(** * Rely/guarantee without auxiliary variables is incomplete

    The textbook counterexample, mechanized:

<<
      inc2  =  x := x + 1  ∥  x := x + 1
>>

    From [x = 0], every run ends with [x = 2] ([inc2_correct]: a valid
    Hoare triple for concurrent Imp). But no rely/guarantee derivation
    proves [{x = 0} inc2 {x = 2}], whatever the rely and guarantee
    ([inc2_not_rg]).

    The reason is in the parallel rule: its post is the conjunction of
    the two threads' posts, and each thread's post must already hold
    when that thread runs alone from [x = 0], where it ends with
    [x = 1]. Nothing a thread can state about the shared state alone
    records whether the *other* thread has incremented yet. That is what
    auxiliary (ghost) variables add in the classical completeness
    results (Owicki and Gries; Stirling; Xu, de Roever and He), and why
    [ParImp.RelyGuarantee] is a sound route into the cube rather than a
    complete one.

    [rg_incomplete] packages the result. Axiom-free. *)

From Stdlib Require Import String Arith Lia.
From LogicTransformers.Imp Require Import Syntax.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Relational.
From LogicTransformers.Core Require Import Kernel SmallStepCore.
From LogicTransformers.ParImp Require Import
  ParImp RelyGuarantee ConcurrentIL.

Local Open Scope string_scope.
Local Notation X := "x".

Definition incx : pcom := PAsgn X (APlus (AVar X) (ANum 1)).
Definition inc2 : pcom := PPar incx incx.

(** ** The triple is valid *)

Definition cnt (c : pcom) : nat := match c with PSkip => 0 | _ => 1 end.

Lemma inc_parrun : forall a b s a' b' s',
    parrun a b s a' b' s' ->
    (a = incx \/ a = PSkip) -> (b = incx \/ b = PSkip) ->
    s' X + cnt a' + cnt b' = s X + cnt a + cnt b.
Proof.
  intros a b s a' b' s' H. induction H; intros Ha Hb; [reflexivity | |].
  - destruct Ha as [-> | ->]; [| inversion H].
    inversion H; subst. rewrite (IHparrun (or_intror eq_refl) Hb).
    simpl. rewrite update_eq. lia.
  - destruct Hb as [-> | ->]; [| inversion H].
    inversion H; subst. rewrite (IHparrun Ha (or_intror eq_refl)).
    simpl. rewrite update_eq. lia.
Qed.

Theorem inc2_correct :
  cvalid Forward Plain Over
    (@mkTriple ParImp (fun s => s X = 0) inc2 (fun s => s X = 2)).
Proof.
  apply cvalid_cvr. simpl. intros s s' Hs Hr.
  apply par_done in Hr.
  pose proof (inc_parrun _ _ _ _ _ _ Hr (or_introl eq_refl)
                (or_introl eq_refl)) as E.
  simpl in E. lia.
Qed.

(** ** No rely/guarantee derivation proves it *)

Lemma rg_asgn_inv : forall R G P x a Q, rg R G P (PAsgn x a) Q ->
    exists P' Q' : state -> Prop,
      (forall s, P s -> P' s) /\ (forall s, Q' s -> Q s) /\
      (forall s, P' s -> Q' (update s x (aeval s a))).
Proof.
  intros R G P x a Q H. remember (PAsgn x a) as c eqn:Ec.
  induction H; inversion Ec; subst.
  - exists P, Q. split; [auto | split; [auto |]]. intros s Hs.
    exact (proj1 (H1 s Hs)).
  - destruct (IHrg eq_refl) as [P1 [Q1 [HP [HQ Hs]]]].
    exists P1, Q1. split; [auto | split; [auto | exact Hs]].
Qed.

Lemma rg_par_inv : forall R G P c1 c2 Q, rg R G P (PPar c1 c2) Q ->
    exists R1 G1 R2 G2 (P1 P2 Q1 Q2 : state -> Prop),
      (forall s, P s -> P1 s /\ P2 s) /\ (forall s, Q1 s /\ Q2 s -> Q s) /\
      rg R1 G1 P1 c1 Q1 /\ rg R2 G2 P2 c2 Q2.
Proof.
  intros R G P c1 c2 Q H. remember (PPar c1 c2) as c eqn:Ec.
  induction H; inversion Ec; subst.
  - exists R1, G1, R2, G2, P1, P2, Q1, Q2. auto.
  - destruct (IHrg eq_refl)
      as [R1 [G1 [R2 [G2 [P1 [P2 [Q1 [Q2 [HP [HQ [K1 K2]]]]]]]]]]].
    exists R1, G1, R2, G2, P1, P2, Q1, Q2.
    split; [intros s Hs; apply HP, H, Hs |].
    split; [intros s Hs; apply H2, HQ, Hs | auto].
Qed.

Theorem inc2_not_rg : forall R G,
    ~ rg R G (fun s => s X = 0) inc2 (fun s => s X = 2).
Proof.
  intros R G H. apply rg_par_inv in H.
  destruct H as [R1 [G1 [R2 [G2 [P1 [P2 [Q1 [Q2 [HP [HQ [H1 H2]]]]]]]]]]].
  apply rg_asgn_inv in H1. apply rg_asgn_inv in H2.
  destruct H1 as [P1' [Q1' [HP1 [HQ1 Hs1]]]].
  destruct H2 as [P2' [Q2' [HP2 [HQ2 Hs2]]]].
  set (s0 := empty_state).
  destruct (HP s0 eq_refl) as [Hp1 Hp2].
  pose proof (HQ1 _ (Hs1 s0 (HP1 s0 Hp1))) as Hq1.
  pose proof (HQ2 _ (Hs2 s0 (HP2 s0 Hp2))) as Hq2.
  pose proof (HQ _ (conj Hq1 Hq2)) as Hq.
  rewrite update_eq in Hq. simpl in Hq. discriminate.
Qed.

(** A valid Hoare triple for a closed concurrent program that no
    rely/guarantee derivation proves. *)
Theorem rg_incomplete :
  exists P c Q,
    cvalid Forward Plain Over (@mkTriple ParImp P c Q) /\
    forall G, ~ rg (fun _ _ => False) G P c Q.
Proof.
  exists (fun s => s X = 0), inc2, (fun s => s X = 2).
  split; [exact inc2_correct | intros G; apply inc2_not_rg].
Qed.
