(** * A structural core language

    A Kleene-algebra-with-tests style language, generic in the state type
    [Σ] and the atomic actions (any relation [act_sem a]):

<<
      c ::= skip | act a | assume B | c₁ ; c₂ | c₁ ⊕ c₂ | c*
>>

    Its semantics is defined structurally, so proof rules can be generated
    once per operator ([Core.Generate]). Imp is encoded into it
    ([Core.ImpCore]). Tests are semantic predicates. *)

From LogicTransformers.Framework Require Import Language.

Section Kernel.

Context {Σ Act : Type} (act_sem : Act -> Σ -> Σ -> Prop).

Inductive kcom : Type :=
  | KSkip
  | KAct (a : Act)
  | KAssume (B : Σ -> Prop)
  | KSeq (c1 c2 : kcom)
  | KChoice (c1 c2 : kcom)
  | KStar (c : kcom).

Inductive kev : kcom -> Σ -> Σ -> Prop :=
  | KE_Skip : forall s, kev KSkip s s
  | KE_Act : forall a s s', act_sem a s s' -> kev (KAct a) s s'
  | KE_Assume : forall (B : Σ -> Prop) s, B s -> kev (KAssume B) s s
  | KE_Seq : forall c1 c2 s s1 s2,
      kev c1 s s1 -> kev c2 s1 s2 -> kev (KSeq c1 c2) s s2
  | KE_ChoiceL : forall c1 c2 s s', kev c1 s s' -> kev (KChoice c1 c2) s s'
  | KE_ChoiceR : forall c1 c2 s s', kev c2 s s' -> kev (KChoice c1 c2) s s'
  | KE_StarRefl : forall c s, kev (KStar c) s s
  | KE_StarStep : forall c s s1 s2,
      kev c s s1 -> kev (KStar c) s1 s2 -> kev (KStar c) s s2.

Lemma kev_star_snoc : forall c s s1 s2,
    kev (KStar c) s s1 -> kev c s1 s2 -> kev (KStar c) s s2.
Proof.
  intros c s s1 s2 H. remember (KStar c) as k eqn:Ek.
  revert s2. induction H; inversion Ek; subst; intros s3 H3.
  - eapply KE_StarStep; [exact H3 | apply KE_StarRefl].
  - eapply KE_StarStep; [exact H | apply IHkev2; auto].
Qed.

Definition KLang : Language := mkLanguage kcom Σ kev.

(** ** Loops: [while B do c] as [(assume B; c)*; assume ¬B] *)

Definition kwhile (B : Σ -> Prop) (c : kcom) : kcom :=
  KSeq (KStar (KSeq (KAssume B) c)) (KAssume (fun s => ~ B s)).

Lemma kev_star_trans : forall c s s1 s2,
    kev (KStar c) s s1 -> kev (KStar c) s1 s2 ->
    kev (KStar c) s s2.
Proof.
  intros c s s1 s2 H. remember (KStar c) as k eqn:Ek.
  revert s2. induction H; inversion Ek; subst; intros s3 H3; [exact H3 |].
  eapply KE_StarStep; [eassumption | apply IHkev2; auto].
Qed.

Lemma kwhile_run_iff : forall B c s s',
    kev (kwhile B c) s s' <->
    kev (KStar (KSeq (KAssume B) c)) s s' /\ ~ B s'.
Proof.
  intros B c s s'. split.
  - intros H. inversion H; subst.
    match goal with H' : kev (KAssume _) _ _ |- _ => inversion H'; subst end.
    auto.
  - intros [H1 H2]. eapply KE_Seq; [exact H1 | apply KE_Assume, H2].
Qed.


End Kernel.

Arguments kcom : clear implicits.
Arguments KSkip {Σ Act}.
Arguments KAct {Σ Act}.
Arguments KAssume {Σ Act}.
Arguments KSeq {Σ Act}.
Arguments KChoice {Σ Act}.
Arguments KStar {Σ Act}.
Arguments kwhile {Σ Act}.
