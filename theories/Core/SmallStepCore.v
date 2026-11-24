(** * Any small-step language is an instance of the core

    Given a step relation on configurations [(program, state)] and a final
    program [done] (stuck), the language's semantics is
    - terminating runs: [smulti (p, s) (done, s')];
    - divergence: [sdiv (p, s)], an infinite sequence of steps.

    Encoding: the core's states are configurations, and it has two atoms,
    [SLoad p] (install program [p]) and [SStep] (take one step). A program
    becomes "load it, then step while not done":

<<
      senc p  =  SLoad p ; while (fst k <> done) do SStep end
>>

    - [senc_run], [senc_div]: the encoding has exactly the language's
      terminating runs and divergences.
    - [senc_cvalid], [senc_cvalid_bot]: every cube validity, on both faces,
      transfers between a source triple and its encoding. Preconditions
      are read on the state part of a configuration, postconditions on
      final configurations ([liftG], see [Framework.Relational]).

    This is how concurrency enters the core: an interleaving semantics is a
    step relation, so the 16 logics apply to concurrent programs. Their
    rules are about the global step relation (one loop over configurations,
    so invariants are Owicki-Gries style global invariants), not
    thread-modular. *)

From Stdlib Require Import Setoid.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Relational.
From LogicTransformers.Core Require Import Kernel KernelBot.

Inductive sact (Prog : Type) : Type :=
  | SLoad (p : Prog)
  | SStep.

Arguments SLoad {Prog}.
Arguments SStep {Prog}.

Section SmallStepCore.

Context {Prog St : Type}.
Context (step : Prog * St -> Prog * St -> Prop) (done : Prog).
Hypothesis done_stuck : forall s k', ~ step (done, s) k'.
Hypothesis done_dec : forall p : Prog, p = done \/ p <> done.

Notation cfg := (Prog * St)%type.

(** ** The source language *)

Inductive smulti : cfg -> cfg -> Prop :=
  | SM_Refl : forall k, smulti k k
  | SM_Step : forall k k1 k2, step k k1 -> smulti k1 k2 -> smulti k k2.

CoInductive sdiv : cfg -> Prop :=
  | SD_Step : forall k k', step k k' -> sdiv k' -> sdiv k.

Definition SLang : Language :=
  mkLanguage Prog St (fun p s s' => smulti (p, s) (done, s')).

Definition ssemB (p : Prog) (o o' : option St) : Prop :=
  match o, o' with
  | None, None => True
  | None, Some _ => False
  | Some s, Some s' => smulti (p, s) (done, s')
  | Some s, None => sdiv (p, s)
  end.

Definition SLangB : Language := mkLanguage Prog (option St) ssemB.

(** ** The encoding *)

Definition sact_sem (a : sact Prog) (k k' : cfg) : Prop :=
  match a with
  | SLoad p => k' = (p, snd k)
  | SStep => step k k'
  end.

Definition running (k : cfg) : Prop := fst k <> done.
Definition fin (k : cfg) : Prop := fst k = done.
Definition finB (o : option cfg) : Prop :=
  match o with Some k => fin k | None => True end.

Definition sloop : kcom cfg (sact Prog) := kwhile running (KAct SStep).
Definition senc (p : Prog) : kcom cfg (sact Prog) :=
  KSeq (KAct (SLoad p)) sloop.

Notation kev := (kev sact_sem).
Notation kdiv := (kdiv sact_sem).
Notation body := (KSeq (KAssume running) (KAct (@SStep Prog))).

Lemma step_running : forall k k', step k k' -> running k.
Proof.
  intros [p s] k' H E. simpl in E. subst p. exact (done_stuck s k' H).
Qed.

Lemma not_running : forall k, ~ running k -> fin k.
Proof.
  intros k H. destruct (done_dec (fst k)) as [E | E]; [exact E | contradiction].
Qed.

Lemma star_smulti : forall k k', kev (KStar body) k k' -> smulti k k'.
Proof.
  intros k k' H. remember (KStar body) as c eqn:Ec.
  induction H; inversion Ec; subst; [apply SM_Refl |].
  match goal with H' : kev (KSeq _ _) _ _ |- _ => inversion H'; subst end.
  match goal with H' : kev (KAssume _) _ _ |- _ => inversion H'; subst end.
  match goal with H' : kev (KAct _) _ _ |- _ => inversion H'; subst end.
  eapply SM_Step; [eassumption | apply IHkev2; reflexivity].
Qed.

Lemma smulti_star : forall k k', smulti k k' -> kev (KStar body) k k'.
Proof.
  intros k k' H. induction H; [apply KE_StarRefl |].
  eapply KE_StarStep; [| exact IHsmulti].
  eapply KE_Seq;
    [apply KE_Assume; eapply step_running; eassumption | apply KE_Act, H].
Qed.

Lemma sloop_run : forall k k', kev sloop k k' <-> smulti k k' /\ fin k'.
Proof.
  intros k k'. unfold sloop. rewrite (kwhile_run_iff sact_sem). split.
  - intros [H Hn]. split; [apply star_smulti, H | apply not_running, Hn].
  - intros [H Hf]. split; [apply smulti_star, H |]. intros Hr. apply Hr, Hf.
Qed.

Theorem senc_run : forall p k k',
    kev (senc p) k k' <-> fin k' /\ smulti (p, snd k) (done, snd k').
Proof.
  intros p k [q s']. unfold senc. split.
  - intros H. inversion H; subst.
    match goal with H' : kev (KAct _) _ _ |- _ => inversion H'; subst end.
    match goal with H' : sact_sem (SLoad _) _ _ |- _ =>
      simpl in H'; subst end.
    match goal with H' : kev sloop _ _ |- _ =>
      apply sloop_run in H' as [Hm Hf] end.
    unfold fin in Hf. simpl in Hf. subst q. split; [reflexivity | exact Hm].
  - intros [Hf Hm]. unfold fin in Hf. simpl in Hf. subst q.
    eapply KE_Seq; [apply KE_Act; reflexivity |].
    apply sloop_run. split; [exact Hm | reflexivity].
Qed.

Lemma sloop_div : forall k, kdiv sloop k <-> sdiv k.
Proof.
  intros k. split.
  - intros H. unfold sloop, kwhile in H. inversion H; subst;
      [| match goal with H' : kdiv (KAssume _) _ |- _ => inversion H' end].
    match goal with
    | H' : kdiv (KStar _) _ |- _ => clear H; rename H' into H
    end.
    revert k H. cofix CH. intros k H. inversion H; subst.
    + exfalso.
      match goal with H' : kdiv (KSeq _ _) _ |- _ => inversion H'; subst end;
        match goal with
        | H' : kdiv (KAssume _) _ |- _ => inversion H'
        | H' : kdiv (KAct _) _ |- _ => inversion H'
        end.
    + match goal with H' : kev (KSeq _ _) _ _ |- _ => inversion H'; subst end.
      match goal with H' : kev (KAssume _) _ _ |- _ => inversion H'; subst end.
      match goal with H' : kev (KAct _) _ _ |- _ => inversion H'; subst end.
      eapply SD_Step; [eassumption | apply CH; assumption].
  - intros H. unfold sloop.
    apply (kwhile_div_intro sact_sem sdiv); [| exact H].
    intros k0 Hd. inversion Hd; subst.
    split; [eapply step_running; eassumption |].
    eexists. split; [apply KE_Act; eassumption | assumption].
Qed.

Theorem senc_div : forall p k, kdiv (senc p) k <-> sdiv (p, snd k).
Proof.
  intros p k. unfold senc. split.
  - intros H. inversion H; subst.
    + match goal with H' : kdiv (KAct _) _ |- _ => inversion H' end.
    + match goal with H' : kev (KAct _) _ _ |- _ => inversion H'; subst end.
      match goal with H' : sact_sem (SLoad _) _ _ |- _ =>
        simpl in H'; subst end.
      apply sloop_div. assumption.
  - intros H. eapply KD_SeqR; [apply KE_Act; reflexivity |].
    apply sloop_div, H.
Qed.

(** ** Validity transfers, on both faces *)

Theorem senc_cvalid : forall d p a (P Q : St -> Prop) c,
    cvalid d p a (@mkTriple SLang P c Q) <->
    cvalid d p a (@mkTriple (KLang sact_sem) (fun k => P (snd k)) (senc c)
                    (liftG snd fin d p a Q)).
Proof.
  intros d p a P Q c. rewrite !cvalid_cvr. simpl.
  apply (cvr_proj snd fin).
  - intros s. exists (done, s). split; reflexivity.
  - intros k k'. apply senc_run.
Qed.

Theorem senc_cvalid_bot : forall d p a (P Q : option St -> Prop) c,
    cvalid d p a (@mkTriple SLangB P c Q) <->
    cvalid d p a (@mkTriple (KLangB sact_sem)
                    (fun o => P (option_map snd o)) (senc c)
                    (liftG (option_map snd) finB d p a Q)).
Proof.
  intros d p a P Q c. rewrite !cvalid_cvr. simpl.
  apply (cvr_proj (option_map snd) finB).
  - intros [s|]; [exists (Some (done, s)) | exists None]; split; reflexivity.
  - intros [k|] [k'|]; simpl.
    + apply senc_run.
    + rewrite senc_div. tauto.
    + tauto.
    + tauto.
Qed.

End SmallStepCore.
