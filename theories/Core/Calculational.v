(** * Cousot's calculational equations for the core language

    The semantics of each core construct, abstracted by [post] or [pre]
    ([Framework.Abstraction]), satisfies one equation per construct.
    Cousot's calculational design reads proof rules off such equations
    (via Aczel's correspondence between equations and rules), and
    [Core.Generate]'s generated rules are these equations read that way:

<<
      post skip P          = P
      post a P             = post (act_sem a) P
      post (assume B) P    = P ∧ B
      post (c1 ; c2) P     = post c2 (post c1 P)
      post (c1 ⊕ c2) P     = post c1 P ∨ post c2 P
      post (c* ) P         = ∃ n. (post c)ⁿ P
>>

    and symmetrically for [pre]. Each is proved here from the core
    semantics, axiom-free. The last section derives Hoare logic's rules
    from these equations by calculation, without looking at runs. *)

From LogicTransformers.Framework Require Import Language Cube Abstraction.
From LogicTransformers.Core Require Import Kernel.

Section Calculational.

Context {Σ Act : Type} (act_sem : Act -> Σ -> Σ -> Prop).

Notation kev := (kev act_sem).

Lemma apost_ext : forall (R1 R2 : @rel Σ) P,
    (forall s s', R1 s s' <-> R2 s s') -> peq (apost R1 P) (apost R2 P).
Proof.
  intros R1 R2 P H s'. unfold apost. split; intros [s [HP Hr]];
    exists s; split; try exact HP; apply H, Hr.
Qed.

Lemma apre_ext : forall (R1 R2 : @rel Σ) Q,
    (forall s s', R1 s s' <-> R2 s s') -> peq (apre R1 Q) (apre R2 Q).
Proof.
  intros R1 R2 Q H s. unfold apre. split; intros [s' [Hr HQ]];
    exists s'; split; try exact HQ; apply H, Hr.
Qed.

Lemma kev_seq_comp : forall c1 c2 s s',
    kev (KSeq c1 c2) s s' <-> rcomp (kev c1) (kev c2) s s'.
Proof.
  intros c1 c2 s s'. unfold rcomp. split.
  - intros H. inversion H; subst. eauto.
  - intros [s1 [H1 H2]]. eapply KE_Seq; eassumption.
Qed.

Lemma kev_choice_union : forall c1 c2 s s',
    kev (KChoice c1 c2) s s' <-> runion (kev c1) (kev c2) s s'.
Proof.
  intros c1 c2 s s'. unfold runion. split.
  - intros H. inversion H; subst; auto.
  - intros [H | H]; [apply KE_ChoiceL | apply KE_ChoiceR]; exact H.
Qed.

Lemma kev_star_rtc : forall c s s', kev (KStar c) s s' <-> rtc (kev c) s s'.
Proof.
  intros c s s'. split.
  - intros H. remember (KStar c) as k eqn:Ek.
    induction H; inversion Ek; subst; [apply rtc_refl |].
    eapply rtc_step; [eassumption | apply IHkev2; reflexivity].
  - intros H. induction H as [s | s s1 s2 H1 _ IH];
      [apply KE_StarRefl | eapply KE_StarStep; eassumption].
Qed.

(** ** Forward: [post] *)

Theorem post_skip : forall P, peq (apost (kev KSkip) P) P.
Proof.
  intros P s'. unfold apost. split.
  - intros [s [HP H]]. inversion H; subst. exact HP.
  - intros HP. exists s'. split; [exact HP | apply KE_Skip].
Qed.

Theorem post_act : forall a P,
    peq (apost (kev (KAct a)) P) (apost (act_sem a) P).
Proof.
  intros a P. apply apost_ext. intros s s'. split.
  - intros H. inversion H; subst. assumption.
  - apply KE_Act.
Qed.

Theorem post_assume : forall B P,
    peq (apost (kev (KAssume B)) P) (fun s => P s /\ B s).
Proof.
  intros B P s'. unfold apost. split.
  - intros [s [HP H]]. inversion H; subst. auto.
  - intros [HP HB]. exists s'. split; [exact HP | apply KE_Assume, HB].
Qed.

Theorem post_seq : forall c1 c2 P,
    peq (apost (kev (KSeq c1 c2)) P) (apost (kev c2) (apost (kev c1) P)).
Proof.
  intros c1 c2 P s.
  rewrite (apost_ext _ _ P (kev_seq_comp c1 c2) s). apply apost_comp.
Qed.

Theorem post_choice : forall c1 c2 P,
    peq (apost (kev (KChoice c1 c2)) P)
        (fun s => apost (kev c1) P s \/ apost (kev c2) P s).
Proof.
  intros c1 c2 P s.
  rewrite (apost_ext _ _ P (kev_choice_union c1 c2) s). apply apost_union.
Qed.

Theorem post_star : forall c P,
    peq (apost (kev (KStar c)) P)
        (fun s => exists n, iter (apost (kev c)) n P s).
Proof.
  intros c P s. rewrite (apost_ext _ _ P (kev_star_rtc c) s). apply apost_rtc.
Qed.

(** ** Backward: [pre] *)

Theorem pre_skip : forall Q, peq (apre (kev KSkip) Q) Q.
Proof.
  intros Q s. unfold apre. split.
  - intros [s' [H HQ]]. inversion H; subst. exact HQ.
  - intros HQ. exists s. split; [apply KE_Skip | exact HQ].
Qed.

Theorem pre_act : forall a Q,
    peq (apre (kev (KAct a)) Q) (apre (act_sem a) Q).
Proof.
  intros a Q. apply apre_ext. intros s s'. split.
  - intros H. inversion H; subst. assumption.
  - apply KE_Act.
Qed.

Theorem pre_assume : forall B Q,
    peq (apre (kev (KAssume B)) Q) (fun s => B s /\ Q s).
Proof.
  intros B Q s. unfold apre. split.
  - intros [s' [H HQ]]. inversion H; subst. auto.
  - intros [HB HQ]. exists s. split; [apply KE_Assume, HB | exact HQ].
Qed.

Theorem pre_seq : forall c1 c2 Q,
    peq (apre (kev (KSeq c1 c2)) Q) (apre (kev c1) (apre (kev c2) Q)).
Proof.
  intros c1 c2 Q s.
  rewrite (apre_ext _ _ Q (kev_seq_comp c1 c2) s). apply apre_comp.
Qed.

Theorem pre_choice : forall c1 c2 Q,
    peq (apre (kev (KChoice c1 c2)) Q)
        (fun s => apre (kev c1) Q s \/ apre (kev c2) Q s).
Proof.
  intros c1 c2 Q s.
  rewrite (apre_ext _ _ Q (kev_choice_union c1 c2) s). apply apre_union.
Qed.

Theorem pre_star : forall c Q,
    peq (apre (kev (KStar c)) Q)
        (fun s => exists n, iter (apre (kev c)) n Q s).
Proof.
  intros c Q s. rewrite (apre_ext _ _ Q (kev_star_rtc c) s). apply apre_rtc.
Qed.

(** ** Rules by calculation

    Cousot derives each logic's rules by calculating with its theory. For
    Hoare logic the theory is [theory Forward Plain Over], that is
    [post c P ⊆ Q]. The rules below are derived from the equations above
    and the monotonicity of [post] alone: no proof here looks at a run.
    Each is the calculation in its comment.

    - [calc_seq]: [post (c1; c2) P = post c2 (post c1 P) ⊆ post c2 Q ⊆ R];
    - [calc_choice]: [post (c1 ⊕ c2) P = post c1 P ∪ post c2 P ⊆ Q];
    - [calc_star_park]: if [post c I ⊆ I] then every iterate stays in
      [I], so [post c* I = ⋃ₙ (post c)ⁿ I ⊆ I] (Park's induction: the
      invariant rule);
    - [calc_star_exact]: if [post c (X n) ⊆ X (n+1)] for every [n], then
      [post c* (X 0) = ⋃ₙ (post c)ⁿ (X 0) ⊆ ⋃ₙ X n] (the iteration rule
      the generator uses, read from the same equation as an Aczel rule
      with one premise per [n]). *)

Notation HLth c P Q := (theory Forward Plain Over (kev c) P Q).

Lemma post_mono : forall c (P P' : Σ -> Prop),
    sub P P' -> sub (apost (kev c) P) (apost (kev c) P').
Proof. intros c. apply apost_mono. Qed.

Theorem calc_skip : forall P, HLth KSkip P P.
Proof. intros P s H. apply (post_skip P s), H. Qed.

Theorem calc_act : forall a P, HLth (KAct a) P (apost (act_sem a) P).
Proof. intros a P s H. apply (post_act a P s), H. Qed.

Theorem calc_assume : forall B P, HLth (KAssume B) P (fun s => P s /\ B s).
Proof. intros B P s H. apply (post_assume B P s), H. Qed.

Theorem calc_seq : forall c1 c2 P Q R,
    HLth c1 P Q -> HLth c2 Q R -> HLth (KSeq c1 c2) P R.
Proof.
  intros c1 c2 P Q R H1 H2 s Hs. simpl in *.
  apply (post_seq c1 c2 P s) in Hs.
  exact (H2 s (post_mono c2 _ _ H1 s Hs)).
Qed.

Theorem calc_choice : forall c1 c2 P Q,
    HLth c1 P Q -> HLth c2 P Q -> HLth (KChoice c1 c2) P Q.
Proof.
  intros c1 c2 P Q H1 H2 s Hs. simpl in *.
  apply (post_choice c1 c2 P s) in Hs. destruct Hs as [H | H]; auto.
Qed.

Theorem calc_star_park : forall c I, HLth c I I -> HLth (KStar c) I I.
Proof.
  intros c I H s Hs. simpl in *. apply (post_star c I s) in Hs.
  destruct Hs as [n Hn]. revert s Hn. induction n as [|n IH]; intros s Hn.
  - exact Hn.
  - apply H. exact (post_mono c _ _ IH s Hn).
Qed.

Theorem calc_star_exact : forall c (X : nat -> Σ -> Prop),
    (forall n, HLth c (X n) (X (S n))) ->
    HLth (KStar c) (X 0) (fun s => exists n, X n s).
Proof.
  intros c X H s Hs. simpl in *. apply (post_star c (X 0) s) in Hs.
  destruct Hs as [n Hn]. exists n. revert s Hn.
  induction n as [|n IH]; intros s Hn; [exact Hn |].
  apply H. exact (post_mono c _ _ IH s Hn).
Qed.

End Calculational.
