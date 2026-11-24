(** * The core language with nontermination

    [kdiv c s]: some run of [c] from [s] diverges (coinductive). Atoms and
    tests never diverge. A star diverges when, after finitely many
    iterations, the body diverges ([KD_StarBody]) or it iterates forever
    ([KD_StarIter] infinitely often).

    [KLangB]: states [option Σ] with [None = ⊥] absorbing, the bottom face
    of the cube for the core language. *)

From LogicTransformers.Framework Require Import Language.
From Stdlib Require Import Arith Wf_nat.
From LogicTransformers.Core Require Import Kernel.

Section KernelBot.

Context {Σ Act : Type} (act_sem : Act -> Σ -> Σ -> Prop).

Notation kev := (kev act_sem).

CoInductive kdiv : kcom Σ Act -> Σ -> Prop :=
  | KD_SeqL : forall c1 c2 s, kdiv c1 s -> kdiv (KSeq c1 c2) s
  | KD_SeqR : forall c1 c2 s s1,
      kev c1 s s1 -> kdiv c2 s1 -> kdiv (KSeq c1 c2) s
  | KD_ChoiceL : forall c1 c2 s, kdiv c1 s -> kdiv (KChoice c1 c2) s
  | KD_ChoiceR : forall c1 c2 s, kdiv c2 s -> kdiv (KChoice c1 c2) s
  | KD_StarBody : forall c s, kdiv c s -> kdiv (KStar c) s
  | KD_StarIter : forall c s s1,
      kev c s s1 -> kdiv (KStar c) s1 -> kdiv (KStar c) s.

Definition semKB (c : kcom Σ Act) (o o' : option Σ) : Prop :=
  match o, o' with
  | None, None => True
  | None, Some _ => False
  | Some s, Some s' => kev c s s'
  | Some s, None => kdiv c s
  end.

Definition KLangB : Language := mkLanguage (kcom Σ Act) (option Σ) semKB.

Lemma semKB_none : forall c o', semKB c None o' <-> o' = None.
Proof.
  intros c [s'|]; simpl; split; intros H;
    solve [contradiction | discriminate | reflexivity | exact I].
Qed.

Lemma semKB_skip : forall o o', semKB KSkip o o' <-> o' = o.
Proof.
  intros [s|] [s'|]; simpl; split; intros H.
  - inversion H; subst. reflexivity.
  - inversion H; subst. apply KE_Skip.
  - inversion H.
  - discriminate.
  - contradiction.
  - discriminate.
  - reflexivity.
  - exact I.
Qed.

Lemma semKB_act : forall a o o',
    semKB (KAct a) o o' <->
    match o, o' with
    | Some s, Some s' => act_sem a s s'
    | None, None => True
    | _, _ => False
    end.
Proof.
  intros a [s|] [s'|]; simpl; split; intros H;
    solve [ inversion H; subst; assumption | apply KE_Act, H | inversion H
          | contradiction | exact H | exact I ].
Qed.

Lemma semKB_assume : forall B o o',
    semKB (KAssume B) o o' <->
    match o, o' with
    | Some s, Some s' => s' = s /\ B s
    | None, None => True
    | _, _ => False
    end.
Proof.
  intros B [s|] [s'|]; simpl; split; intros H;
    solve [ inversion H; subst; auto
          | destruct H as [-> HB]; apply KE_Assume, HB
          | contradiction | exact H | exact I ].
Qed.

Lemma semKB_seq : forall c1 c2 o o'',
    semKB (KSeq c1 c2) o o'' <-> exists o', semKB c1 o o' /\ semKB c2 o' o''.
Proof.
  intros c1 c2 [s|] [s''|]; simpl; split.
  - intros H. inversion H; subst. exists (Some s1). simpl. auto.
  - intros [[s'|] [H1 H2]]; [eapply KE_Seq; eassumption | contradiction].
  - intros H. inversion H; subst.
    + exists None. simpl. auto.
    + exists (Some s1). simpl. auto.
  - intros [[s'|] [H1 H2]].
    + eapply KD_SeqR; eassumption.
    + apply KD_SeqL. exact H1.
  - contradiction.
  - intros [[s'|] [H1 H2]]; contradiction.
  - intros _. exists None. simpl. auto.
  - auto.
Qed.

Lemma semKB_choice : forall c1 c2 o o',
    semKB (KChoice c1 c2) o o' <-> semKB c1 o o' \/ semKB c2 o o'.
Proof.
  intros c1 c2 [s|] [s'|]; simpl; split; intros H.
  - inversion H; subst; auto.
  - destruct H as [H | H]; [apply KE_ChoiceL | apply KE_ChoiceR]; auto.
  - inversion H; subst; auto.
  - destruct H as [H | H]; [apply KD_ChoiceL | apply KD_ChoiceR]; auto.
  - contradiction.
  - destruct H as [H | H]; contradiction.
  - left. exact I.
  - exact I.
Qed.

Lemma kwhile_div_guard : forall B c s, kdiv (kwhile B c) s -> B s.
Proof.
  intros B c s H. inversion H; subst.
  - match goal with H' : kdiv (KStar _) _ |- _ => inversion H'; subst end.
    + match goal with H' : kdiv (KSeq _ _) _ |- _ => inversion H'; subst end.
      * match goal with H' : kdiv (KAssume _) _ |- _ => inversion H' end.
      * match goal with H' : kev (KAssume _) _ _ |- _ =>
          inversion H'; subst end. assumption.
    + match goal with H' : kev (KSeq _ _) _ _ |- _ => inversion H'; subst end.
      match goal with H' : kev (KAssume _) _ _ |- _ =>
        inversion H'; subst end. assumption.
  - match goal with H' : kdiv (KAssume _) _ |- _ => inversion H' end.
Qed.

(** Divergence from a coinvariant: every state of [I] satisfies the guard
    and has a body step back into [I]. *)
Lemma kwhile_div_intro : forall (I : Σ -> Prop) B c,
    (forall s, I s -> B s /\ exists s', kev c s s' /\ I s') ->
    forall s, I s -> kdiv (kwhile B c) s.
Proof.
  intros I B c H s HI. apply KD_SeqL. revert s HI. cofix CH. intros s HI.
  destruct (H s HI) as [HB [s' [Hc HI']]].
  eapply KD_StarIter; [eapply KE_Seq; [apply KE_Assume, HB | exact Hc] |].
  apply CH, HI'.
Qed.

(** No divergence: the body never diverges and decreases a measure. *)
Lemma kwhile_no_div : forall (mu : Σ -> nat) B c,
    (forall s, ~ kdiv c s) ->
    (forall s s', B s -> kev c s s' -> mu s' < mu s) ->
    forall s, ~ kdiv (kwhile B c) s.
Proof.
  intros mu B c Hnd Hdec s H. inversion H; subst;
    [| match goal with H' : kdiv (KAssume _) _ |- _ => inversion H' end].
  match goal with H' : kdiv (KStar _) _ |- _ => clear H; rename H' into H end.
  remember (mu s) as n eqn:En. revert s H En.
  induction n as [n IH] using (well_founded_induction lt_wf).
  intros s H En. inversion H; subst.
  - match goal with H' : kdiv (KSeq _ _) _ |- _ => inversion H'; subst end.
    + match goal with H' : kdiv (KAssume _) _ |- _ => inversion H' end.
    + match goal with H' : kev (KAssume _) _ _ |- _ =>
        inversion H'; subst end.
      eapply Hnd; eassumption.
  - match goal with H' : kev (KSeq _ _) _ _ |- _ => inversion H'; subst end.
    match goal with H' : kev (KAssume _) _ _ |- _ =>
      inversion H'; subst end.
    eapply (IH (mu s1)); [| eassumption | reflexivity].
    eapply Hdec; eassumption.
Qed.


(** Termination of a loop from a well-founded variant and an invariant. *)
Lemma kwhile_no_div_wf : forall (W : Type) (R : W -> W -> Prop)
    (I : Σ -> Prop) (mu : Σ -> W) B c,
    well_founded R ->
    (forall s, I s -> B s -> ~ kdiv c s) ->
    (forall s s', I s -> B s -> kev c s s' -> I s' /\ R (mu s') (mu s)) ->
    forall s, I s -> ~ kdiv (kwhile B c) s.
Proof.
  intros W R I mu B c Hwf Hnd Hdec s HI H. inversion H; subst;
    [| match goal with H' : kdiv (KAssume _) _ |- _ => inversion H' end].
  match goal with H' : kdiv (KStar _) _ |- _ => clear H; rename H' into H end.
  remember (mu s) as w eqn:Ew. revert s HI H Ew.
  induction w as [w IH] using (well_founded_induction Hwf).
  intros s HI H Ew. inversion H; subst.
  - match goal with H' : kdiv (KSeq _ _) _ |- _ => inversion H'; subst end.
    + match goal with H' : kdiv (KAssume _) _ |- _ => inversion H' end.
    + match goal with H' : kev (KAssume _) _ _ |- _ =>
        inversion H'; subst end.
      eapply Hnd; eassumption.
  - match goal with H' : kev (KSeq _ _) _ _ |- _ => inversion H'; subst end.
    match goal with H' : kev (KAssume _) _ _ |- _ =>
      inversion H'; subst end.
    match goal with
    | Hk : kev c ?x ?y, Hb : B ?x, Hx : I ?x |- _ =>
        destruct (Hdec x y Hx Hb Hk) as [HI' HR];
        eapply (IH (mu y)); [exact HR | exact HI' | eassumption | reflexivity]
    end.
Qed.

End KernelBot.
