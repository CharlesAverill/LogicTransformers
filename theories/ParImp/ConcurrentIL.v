(** * Compositional incorrectness logic for concurrent Imp

    Under-approximate reasoning about concurrency cannot use relies and
    guarantees the way [ParImp.RelyGuarantee] does. Each thread's proof
    would say that *some* run reaches its post, and two such claims
    cannot in general be merged into one interleaving. Concurrent
    incorrectness logics compose *schedules* instead.

    [cil P c Q] means: every state in [Q] is the end of a run of [c] from
    a state in [P] ([cil_valid], which is IL validity for [ParImp]). The
    rules are O'Hearn's for the sequential constructs, plus three for
    parallel composition:
    - [CI_ParSeqL], [CI_ParSeqR]: run one thread to the end, then the
      other;
    - [CI_ParSplit]: run both threads' first parts in parallel, then both
      second parts. Phases are how races are exposed: the lost update of
      [Examples.RaceExample] is two phases, both reads and then both
      writes ([Examples.RaceCIL]).

    Two more rules make the logic complete: a one-step rule
    ([CI_Step], symbolic execution of one interleaving step) and
    infinitary disjunction ([CI_DisjAll]).

    [cil_sound], [cil_complete]: sound and complete for the interleaving
    semantics, so [cil] proves exactly the valid IL triples of concurrent
    Imp ([cil_iff]). [cil_derive_IL]: a [cil] proof gives a derivation in
    any IL record for the encoded program, from which the other corners
    are computed.

    All of it is axiom-free. *)

From LogicTransformers.Imp Require Import Syntax.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Relational Verified.
From LogicTransformers.Core Require Import Kernel SmallStepCore.
From LogicTransformers.ParImp Require Import ParImp.

Notation run := (smulti pstep).

Definition cil_valid (P : state -> Prop) (c : pcom) (Q : state -> Prop) :=
  forall s', Q s' -> exists s, P s /\ run (c, s) (PSkip, s').

(** ** Runs in context *)

Lemma run_trans : forall k1 k2 k3, run k1 k2 -> run k2 k3 -> run k1 k3.
Proof.
  intros k1 k2 k3 H1 H2. induction H1; [exact H2 |].
  eapply SM_Step; [eassumption | apply IHsmulti, H2].
Qed.

Lemma run_step : forall k1 k2, pstep k1 k2 -> run k1 k2.
Proof. intros k1 k2 H. eapply SM_Step; [exact H | apply SM_Refl]. Qed.

Lemma run_ctx : forall (f : pcom -> pcom),
    (forall c s c' s', pstep (c, s) (c', s') -> pstep (f c, s) (f c', s')) ->
    forall k k', run k k' -> run (f (fst k), snd k) (f (fst k'), snd k').
Proof.
  intros f Hf k k' H. induction H as [k | k k1 k2 Hs _ IH]; [apply SM_Refl |].
  destruct k as [c s], k1 as [c1 s1].
  eapply SM_Step; [apply Hf, Hs | exact IH].
Qed.

Lemma run_seq : forall c1 c1' c2 s s',
    run (c1, s) (c1', s') -> run (PSeq c1 c2, s) (PSeq c1' c2, s').
Proof.
  intros c1 c1' c2 s s' H.
  exact (run_ctx (fun c => PSeq c c2) (fun c s c' s' H => PS_Seq c c' c2 s s' H)
           _ _ H).
Qed.

Lemma run_parL : forall c1 c1' c2 s s',
    run (c1, s) (c1', s') -> run (PPar c1 c2, s) (PPar c1' c2, s').
Proof.
  intros c1 c1' c2 s s' H.
  exact (run_ctx (fun c => PPar c c2)
           (fun c s c' s' H => PS_ParL c c' c2 s s' H) _ _ H).
Qed.

Lemma run_parR : forall c1 c2 c2' s s',
    run (c2, s) (c2', s') -> run (PPar c1 c2, s) (PPar c1 c2', s').
Proof.
  intros c1 c2 c2' s s' H.
  exact (run_ctx (fun c => PPar c1 c)
           (fun c s c' s' H => PS_ParR c1 c c' s s' H) _ _ H).
Qed.

(** A run of a parallel composition to the end: interleaved steps of the
    two threads until both are [skip], then the final step. *)
Inductive parrun : pcom -> pcom -> state -> pcom -> pcom -> state -> Prop :=
  | PR_Refl : forall a b s, parrun a b s a b s
  | PR_L : forall a a1 b s s1 a' b' s',
      pstep (a, s) (a1, s1) -> parrun a1 b s1 a' b' s' -> parrun a b s a' b' s'
  | PR_R : forall a b b1 s s1 a' b' s',
      pstep (b, s) (b1, s1) -> parrun a b1 s1 a' b' s' -> parrun a b s a' b' s'.

Lemma run_skip : forall s k, run (PSkip, s) k -> k = (PSkip, s).
Proof.
  intros s k H. inversion H; subst; [reflexivity |].
  match goal with Hs : pstep (PSkip, s) _ |- _ => inversion Hs end.
Qed.

Lemma par_done_gen : forall k k', run k k' ->
    forall a b s s', k = (PPar a b, s) -> k' = (PSkip, s') ->
    parrun a b s PSkip PSkip s'.
Proof.
  intros k k' H. induction H as [k | k k1 k2 Hs Hr IH];
    intros a b s s' E E'; subst.
  - discriminate.
  - inversion Hs; subst.
    + eapply PR_L; [eassumption | eapply IH; reflexivity].
    + eapply PR_R; [eassumption | eapply IH; reflexivity].
    + apply run_skip in Hr. injection Hr; intros; subst. apply PR_Refl.
Qed.

Lemma par_done : forall a b s s',
    run (PPar a b, s) (PSkip, s') -> parrun a b s PSkip PSkip s'.
Proof.
  intros a b s s' H. exact (par_done_gen _ _ H a b s s' eq_refl eq_refl).
Qed.

Lemma parrun_seq : forall a b s a' b' s' c d,
    parrun a b s a' b' s' ->
    run (PPar (PSeq a c) (PSeq b d), s) (PPar (PSeq a' c) (PSeq b' d), s').
Proof.
  intros a b s a' b' s' c d H. induction H; [apply SM_Refl | |].
  - eapply SM_Step; [apply PS_ParL, PS_Seq; eassumption | exact IHparrun].
  - eapply SM_Step; [apply PS_ParR, PS_Seq; eassumption | exact IHparrun].
Qed.

(** ** The logic *)

Inductive cil : (state -> Prop) -> pcom -> (state -> Prop) -> Prop :=
  | CI_Skip : forall P, cil P PSkip P
  | CI_Asgn : forall P x a,
      cil P (PAsgn x a) (fun s' => exists s, P s /\ s' = update s x (aeval s a))
  | CI_Seq : forall P R Q c1 c2,
      cil P c1 R -> cil R c2 Q -> cil P (PSeq c1 c2) Q
  | CI_IfT : forall P Q b c1 c2,
      cil (fun s => P s /\ beval s b = true) c1 Q -> cil P (PIf b c1 c2) Q
  | CI_IfF : forall P Q b c1 c2,
      cil (fun s => P s /\ beval s b = false) c2 Q -> cil P (PIf b c1 c2) Q
  | CI_While : forall (X : nat -> state -> Prop) b c,
      (forall n, cil (fun s => X n s /\ beval s b = true) c (X (S n))) ->
      cil (X 0) (PWhile b c) (fun s => exists n, X n s /\ beval s b = false)
  | CI_Disj : forall P Q1 Q2 c,
      cil P c Q1 -> cil P c Q2 -> cil P c (fun s => Q1 s \/ Q2 s)
  | CI_Cons : forall P P' Q Q' c,
      (forall s, P' s -> P s) -> (forall s, Q s -> Q' s) ->
      cil P' c Q' -> cil P c Q
  | CI_ParSeqL : forall P M Q c1 c2,
      cil P c1 M -> cil M c2 Q -> cil P (PPar c1 c2) Q
  | CI_ParSeqR : forall P M Q c1 c2,
      cil P c2 M -> cil M c1 Q -> cil P (PPar c1 c2) Q
  | CI_ParSplit : forall P M Q c1a c1b c2a c2b,
      cil P (PPar c1a c2a) M -> cil M (PPar c1b c2b) Q ->
      cil P (PPar (PSeq c1a c1b) (PSeq c2a c2b)) Q
  | CI_Step : forall P Q c c',
      cil (fun s' => exists s, P s /\ pstep (c, s) (c', s')) c' Q ->
      cil P c Q
  | CI_DisjAll : forall (I : Type) P (Qi : I -> state -> Prop) c,
      (forall i, cil P c (Qi i)) -> cil P c (fun s => exists i, Qi i s).

(** ** Soundness *)

Theorem cil_sound : forall P c Q, cil P c Q -> cil_valid P c Q.
Proof.
  intros P c Q H. induction H; intros s' HQ.
  - exists s'. split; [exact HQ | apply SM_Refl].
  - destruct HQ as [s [HP ->]]. exists s. split; [exact HP |].
    apply run_step, PS_Asgn.
  - destruct (IHcil2 s' HQ) as [s1 [HR H2]].
    destruct (IHcil1 s1 HR) as [s [HP H1]].
    exists s. split; [exact HP |].
    eapply run_trans; [apply run_seq, H1 |].
    eapply SM_Step; [apply PS_SeqSkip | exact H2].
  - destruct (IHcil s' HQ) as [s [[HP Hb] Hr]]. exists s.
    split; [exact HP | eapply SM_Step; [apply PS_IfT, Hb | exact Hr]].
  - destruct (IHcil s' HQ) as [s [[HP Hb] Hr]]. exists s.
    split; [exact HP | eapply SM_Step; [apply PS_IfF, Hb | exact Hr]].
  - assert (Hn : forall n s', X n s' ->
                 exists s, X 0 s /\ run (PWhile b c, s) (PWhile b c, s')).
    { induction n as [|n IHn]; intros s1 Hx.
      - exists s1. split; [exact Hx | apply SM_Refl].
      - destruct (H0 n s1 Hx) as [s2 [[Hx2 Hb] Hr]].
        destruct (IHn s2 Hx2) as [s [Hx0 Hw]].
        exists s. split; [exact Hx0 |].
        eapply run_trans; [exact Hw |].
        eapply SM_Step; [apply PS_While |].
        eapply SM_Step; [apply PS_IfT, Hb |].
        eapply run_trans; [apply run_seq, Hr |].
        apply run_step, PS_SeqSkip. }
    destruct HQ as [n [Hx Hb]]. destruct (Hn n s' Hx) as [s [Hx0 Hw]].
    exists s. split; [exact Hx0 |].
    eapply run_trans; [exact Hw |].
    eapply SM_Step; [apply PS_While |].
    apply run_step, PS_IfF, Hb.
  - destruct HQ as [HQ | HQ]; [apply IHcil1 | apply IHcil2]; exact HQ.
  - destruct (IHcil s' (H0 s' HQ)) as [s [HP Hr]].
    exists s. split; [apply H, HP | exact Hr].
  - destruct (IHcil2 s' HQ) as [s1 [HM H2]].
    destruct (IHcil1 s1 HM) as [s [HP H1]].
    exists s. split; [exact HP |].
    eapply run_trans; [apply run_parL, H1 |].
    eapply run_trans; [apply run_parR, H2 |].
    apply run_step, PS_ParDone.
  - destruct (IHcil2 s' HQ) as [s1 [HM H1]].
    destruct (IHcil1 s1 HM) as [s [HP H2]].
    exists s. split; [exact HP |].
    eapply run_trans; [apply run_parR, H2 |].
    eapply run_trans; [apply run_parL, H1 |].
    apply run_step, PS_ParDone.
  - destruct (IHcil2 s' HQ) as [s1 [HM H2]].
    destruct (IHcil1 s1 HM) as [s [HP H1]].
    exists s. split; [exact HP |].
    apply par_done in H1.
    eapply run_trans; [apply parrun_seq, H1 |].
    eapply SM_Step; [apply PS_ParL, PS_SeqSkip |].
    eapply SM_Step; [apply PS_ParR, PS_SeqSkip | exact H2].
  - destruct (IHcil s' HQ) as [s1 [[s [HP Hs]] Hr]].
    exists s. split; [exact HP | eapply SM_Step; eassumption].
  - destruct HQ as [i HQ]. exact (H0 i s' HQ).
Qed.

(** ** Completeness

    With the one-step rule and infinitary disjunction, the logic is
    complete: each target state's run is followed step by step
    ([cil_run]), and the targets are combined by disjunction. The
    compositional rules ([CI_ParSeqL], [CI_ParSplit], ...) remain
    available as shortcuts. *)

Lemma cil_run_gen : forall k k', run k k' ->
    forall c s s', k = (c, s) -> k' = (PSkip, s') ->
    cil (fun x => x = s) c (fun x => x = s').
Proof.
  intros k k' H. induction H as [k | k k1 k2 Hs _ IH];
    intros c s s' E E'; subst.
  - injection E'; intros; subst. apply CI_Skip.
  - destruct k1 as [c1 s1]. apply (CI_Step _ _ c c1).
    apply (CI_Cons _ (fun x => x = s1) _ (fun x => x = s'));
      [intros x ->; exists s; auto | auto | eapply IH; reflexivity].
Qed.

Lemma cil_run : forall c s s',
    run (c, s) (PSkip, s') -> cil (fun x => x = s) c (fun x => x = s').
Proof. intros c s s' H. exact (cil_run_gen _ _ H c s s' eq_refl eq_refl). Qed.

Theorem cil_complete : forall P c Q, cil_valid P c Q -> cil P c Q.
Proof.
  intros P c Q V.
  apply (CI_Cons _ P _ (fun t => exists i : {s' | Q s'}, t = proj1_sig i));
    [auto | intros s' HQ; exists (exist _ s' HQ); reflexivity |].
  apply (CI_DisjAll {s' | Q s'} P (fun i t => t = proj1_sig i)).
  intros [s' HQ]. simpl. destruct (V s' HQ) as [s [HP Hr]].
  apply (CI_Cons _ (fun x => x = s) _ (fun x => x = s'));
    [intros x ->; exact HP | auto | apply cil_run, Hr].
Qed.

(** IL validity for concurrent Imp and derivability coincide. *)
Corollary cil_iff : forall P c Q,
    cil P c Q <-> cvalid Forward Plain Under (@mkTriple ParImp P c Q).
Proof.
  intros P c Q. rewrite cvalid_cvr. simpl.
  split; [apply cil_sound | apply cil_complete].
Qed.

(** ** Into the cube *)

Theorem cil_il : forall P c Q, cil P c Q ->
    cvalid Forward Plain Under (@mkTriple ParImp P c Q).
Proof.
  intros P c Q H. apply cvalid_cvr. simpl. exact (cil_sound P c Q H).
Qed.

Corollary cil_derive_IL :
    forall (V : VLogic (KLang pact_sem) Forward Plain Under) P c Q,
    cil P c Q ->
    derivable (rules (vl_logic V))
      (@mkTriple (KLang pact_sem) (fun k => P (snd k)) (penc c)
         (liftG snd pfin Forward Plain Under Q)).
Proof.
  intros V P c Q H. apply vl_derive.
  apply (penc_cvalid Forward Plain Under). exact (cil_il P c Q H).
Qed.
