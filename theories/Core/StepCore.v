(** * Any step relation, as segments in the core

    [Core.SmallStepCore] needs a final program that cannot step. Some
    semantics don't have one: in adversarial logic, channel transfers
    can still happen after both programs have finished. This file needs
    no such assumption.

    A *segment* [(p, q)] is a program: run from residual program [p] to
    residual program [q], by any number of steps. Its semantics is
    [steps (p, s) (q, s')]. In the core it becomes

<<
      segenc (p, q)  =  TLoad p ; TStep* ; assume (residual = q)
>>

    [segenc_run]: the encoding has exactly the segment's runs.
    [segenc_cvalid]: every validity at all eight corners of the ordinary
    face transfers between a segment and its encoding. Preconditions are
    read on the state, postconditions on configurations whose residual is
    [q].

    ** Rules for segments, for any step relation

    In any IL record for the encoding, [sprov P p q Q] says: every state
    in [Q] is reached, from some state in [P], by a run from residual
    [p] to residual [q] ([sprov_iff]). Its rules hold for every step
    relation:
    - [sprov_trans]: runs compose;
    - [sprov_step]: one step, from a single state;
    - [sprov_from]: start from one state satisfying the precondition;
    - [sprov_embed]: an IL triple of *any* other core language transfers
      to a segment, given an inclusion of its relation in the segment's
      runs. This is the monotonicity of IL in the relation
      ([Framework.Uniform.cvr_mono]).

    Axiom-free. *)

From Stdlib Require Import Setoid.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Relational Verified.
From LogicTransformers.Core Require Import Kernel Rules.

Inductive tact (Prog : Type) : Type :=
  | TLoad (p : Prog)
  | TStep.

Arguments TLoad {Prog}.
Arguments TStep {Prog}.

Section StepCore.

Context {Prog St : Type} (step : Prog * St -> Prog * St -> Prop).

Notation cfg := (Prog * St)%type.

Inductive steps : cfg -> cfg -> Prop :=
  | ST_Refl : forall k, steps k k
  | ST_Step : forall k k1 k2, step k k1 -> steps k1 k2 -> steps k k2.

Lemma steps_trans : forall k1 k2 k3, steps k1 k2 -> steps k2 k3 -> steps k1 k3.
Proof.
  intros k1 k2 k3 H1 H2. induction H1; [exact H2 |].
  eapply ST_Step; [eassumption | apply IHsteps, H2].
Qed.

Definition Seg : Language :=
  mkLanguage (Prog * Prog) St (fun pq s s' => steps (fst pq, s) (snd pq, s')).

Definition tact_sem (a : tact Prog) (k k' : cfg) : Prop :=
  match a with
  | TLoad p => k' = (p, snd k)
  | TStep => step k k'
  end.

Definition segenc (pq : Prog * Prog) : kcom cfg (tact Prog) :=
  KSeq (KAct (TLoad (fst pq)))
       (KSeq (KStar (KAct TStep)) (KAssume (fun k => fst k = snd pq))).

Notation kev := (kev tact_sem).

Lemma star_steps : forall k k', kev (KStar (KAct TStep)) k k' <-> steps k k'.
Proof.
  intros k k'. split.
  - intros H. remember (KStar (KAct TStep)) as c eqn:Ec.
    induction H; inversion Ec; subst; [apply ST_Refl |].
    match goal with H' : kev (KAct _) _ _ |- _ => inversion H'; subst end.
    eapply ST_Step; [eassumption | apply IHkev2; reflexivity].
  - intros H. induction H; [apply KE_StarRefl |].
    eapply KE_StarStep; [apply KE_Act; exact H | exact IHsteps].
Qed.

Theorem segenc_run : forall pq k k',
    kev (segenc pq) k k' <->
    fst k' = snd pq /\ steps (fst pq, snd k) (snd pq, snd k').
Proof.
  intros [p q] k [c' s']. unfold segenc. simpl. split.
  - intros H. inversion H; subst.
    match goal with H1 : kev (KAct _) _ _ |- _ => inversion H1; subst end.
    match goal with H1 : tact_sem (TLoad _) _ _ |- _ => simpl in H1; subst end.
    match goal with H2 : kev (KSeq _ _) _ _ |- _ => inversion H2; subst end.
    match goal with H3 : kev (KAssume _) _ _ |- _ => inversion H3; subst end.
    match goal with H4 : kev (KStar _) _ _ |- _ =>
      apply star_steps in H4 end.
    simpl. split; [reflexivity | assumption].
  - intros [E Hs]. subst c'.
    eapply KE_Seq; [apply KE_Act; reflexivity |].
    eapply KE_Seq; [apply star_steps; exact Hs | apply KE_Assume; reflexivity].
Qed.

Theorem segenc_cvalid : forall d p a (P Q : St -> Prop) pq,
    cvalid d p a (@mkTriple Seg P pq Q) <->
    cvalid d p a (@mkTriple (KLang tact_sem) (fun k => P (snd k)) (segenc pq)
                    (liftG snd (fun k => fst k = snd pq) d p a Q)).
Proof.
  intros d p a P Q pq. rewrite !cvalid_cvr. simpl.
  apply (cvr_proj snd (fun k => fst k = snd pq)).
  - intros s. exists (snd pq, s). split; reflexivity.
  - intros k k'. apply segenc_run.
Qed.

Section Segments.

Variable V : VLogic (KLang tact_sem) Forward Plain Under.

Definition sprov (P : St -> Prop) (p q : Prog) (Q : St -> Prop) : Prop :=
  prov tact_sem V (fun k => P (snd k)) (segenc (p, q))
    (liftG snd (fun k => fst k = q) Forward Plain Under Q).

Theorem sprov_iff : forall P p q Q,
    sprov P p q Q <->
    (forall s', Q s' -> exists s, P s /\ steps (p, s) (q, s')).
Proof.
  intros P p q Q. unfold sprov, prov. rewrite vl_theory.
  rewrite <- (segenc_cvalid Forward Plain Under P Q (p, q)).
  rewrite cvalid_cvr. reflexivity.
Qed.

Lemma sprov_trans : forall P R Q p q r,
    sprov P p q R -> sprov R q r Q -> sprov P p r Q.
Proof.
  intros P R Q p q r H1 H2. rewrite sprov_iff in *. intros s2 HQ.
  destruct (H2 s2 HQ) as [s1 [HR K2]]. destruct (H1 s1 HR) as [s [HP K1]].
  exists s. split; [exact HP | eapply steps_trans; eassumption].
Qed.

Lemma sprov_step : forall p q s s', step (p, s) (q, s') ->
    sprov (only s) p q (only s').
Proof.
  intros p q s s' H. apply sprov_iff. intros x E. unfold only in E.
  subst x. exists s. split; [reflexivity |].
  eapply ST_Step; [exact H | apply ST_Refl].
Qed.

Lemma sprov_from : forall (P Q : St -> Prop) s p q,
    P s -> sprov (only s) p q Q -> sprov P p q Q.
Proof.
  intros P Q s p q HP H. rewrite sprov_iff in *. intros s' HQ.
  destruct (H s' HQ) as [x [E Hs]]. unfold only in E. subst x. eauto.
Qed.

Lemma sprov_embed : forall {Act1 : Type} (act1 : Act1 -> St -> St -> Prop)
    (V1 : VLogic (KLang act1) Forward Plain Under) P c Q p q,
    (forall s s', Kernel.kev act1 c s s' -> steps (p, s) (q, s')) ->
    prov act1 V1 P c Q -> sprov P p q Q.
Proof.
  intros Act1 act1 V1 P c Q p q Hinc H.
  apply sprov_iff. intros s' HQ.
  destruct (proj1 (il_iff act1 V1 _ _ _) H s' HQ) as [s [HP Hk]].
  exists s. split; [exact HP | apply Hinc, Hk].
Qed.

End Segments.

End StepCore.
