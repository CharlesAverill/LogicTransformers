(** * Imp's hand-written rules are instances of the generator

    Each rule in Imp's [sym] and [bwd] selections ([ImpCube.ImpRules]) is a
    derived rule of the generated system on encoded programs: from
    generated derivations of the encoded premises, the generated rules
    (without consequence) derive the encoded conclusion, up to assertion
    equivalence ([sym_instance], [bwd_instance]). So whole Imp derivations
    translate into generated ones ([sym_derivations], [bwd_derivations]).

    The derivations follow the encodings: [if] is a choice of two
    [assume; c] sequences, and [while] is a star of [assume b; c] followed by
    [assume ¬b]. The loop's index family is reused as the star's index
    family. For the wlp rule the families differ only by [Q ∨ b] vs
    [¬b → Q], which agree because Imp's tests are decidable. *)

From LogicTransformers.Imp Require Import Syntax BigStep Lang.
From LogicTransformers.Imp Require Import Hoare.
From LogicTransformers.ImpCube Require Import ImpRules.
From LogicTransformers.Framework Require Import Language ProgramLogic Cube.
From LogicTransformers.Core Require Import Kernel ImpCore Generate.

Definition encT (t : triple Imp) : triple ICore :=
  @mkTriple ICore (pre t) (enc (cmd t)) (post t).

Notation ct := (@mkTriple ICore).
Notation GF := (@fwd_base state iact iact_sem iact_sem).
Notation GB := (@bwd_base state iact iact_sem iact_sem).

Lemma encT_proper : forall t t', triple_equiv t t' ->
    triple_equiv (encT t) (encT t').
Proof.
  intros [P c Q] [P' c' Q'] [HP [Hc HQ]]. simpl in *. subst.
  split; [exact HP | split; [reflexivity | exact HQ]].
Qed.

Lemma gF : forall g ps c,
    fwd_rule iact_sem g ps c -> (forall t, ps t -> derivable GF t) ->
    derivable GF c.
Proof. intros g ps c HR H. eapply D_Rule; [exists g; exact HR | exact H]. Qed.

Lemma gB : forall g ps c,
    bwd_rule iact_sem g ps c -> (forall t, ps t -> derivable GB t) ->
    derivable GB c.
Proof. intros g ps c HR H. eapply D_Rule; [exists g; exact HR | exact H]. Qed.

Lemma bassn_dec : forall b s, bassn b s \/ ~ bassn b s.
Proof.
  intros b s. unfold bassn. destruct (beval s b); [left | right]; auto.
Qed.

Lemma equiv_post : forall P c (Q Q' : assertion ICore),
    aequiv Q Q' -> triple_equiv (ct P c Q) (ct P c Q').
Proof. intros. repeat split; auto; apply H. Qed.

Lemma equiv_pre : forall (P P' : assertion ICore) c Q,
    aequiv P P' -> triple_equiv (ct P c Q) (ct P' c Q).
Proof. intros. repeat split; auto; apply H. Qed.

Ltac no_prem := intros t [].

(** ** Forward rules *)

Theorem sym_instance : forall r ps c,
    sym r -> imp_rule r ps c ->
    (forall t, ps t -> derivable GF (encT t)) -> derivable GF (encT c).
Proof.
  intros r ps c Hs HR H.
  destruct HR; simpl in Hs; try contradiction; simpl.
  - (* Skip *) apply (gF _ _ _ (F_Skip _ _ P)). no_prem.
  - (* AsgnFwd *) apply (gF _ _ _ (F_Act _ _ P (IAsgn x a))). no_prem.
  - (* Seq *)
    apply (gF _ _ _ (F_Seq _ _ P Q R (enc c1) (enc c2))).
    intros t [-> | ->]; [apply (H _ (or_introl eq_refl))
                        | apply (H _ (or_intror eq_refl))].
  - (* IfDisj *)
    apply (gF _ _ _ (F_Choice _ _ P Q1 Q2 _ _)).
    intros t [-> | ->].
    + apply (gF _ _ _ (F_Seq _ _ P (with_b P b) Q1 _ _)).
      intros t [-> | ->];
        [apply (gF _ _ _ (F_Assume _ _ P (bassn b))); no_prem
        | apply (H _ (or_introl eq_refl))].
    + apply (gF _ _ _ (F_Seq _ _ P (with_nb P b) Q2 _ _)).
      intros t [-> | ->];
        [apply (gF _ _ _ (F_Assume _ _ P (fun s => ~ bassn b s))); no_prem
        | apply (H _ (or_intror eq_refl))].
  - (* WhileIdx *)
    eapply D_Equiv;
      [apply (gF _ _ _ (F_Seq _ _ (P 0) (fun s => exists n, P n s)
                          (fun s => (exists n, P n s) /\ ~ bassn b s)
                          (KStar (KSeq (KAssume (bassn b)) (enc c)))
                          (KAssume (fun s => ~ bassn b s)))) |].
    + intros t [-> | ->].
      * apply (gF _ _ _ (F_Star _ _ P _)).
        intros t [n ->].
        apply (gF _ _ _ (F_Seq _ _ (P n) (with_b (P n) b) (P (S n)) _ _)).
        intros t [-> | ->];
          [apply (gF _ _ _ (F_Assume _ _ (P n) (bassn b))); no_prem
          | apply (H _ (ex_intro _ n eq_refl))].
      * apply (gF _ _ _ (F_Assume _ _ _ (fun s => ~ bassn b s))). no_prem.
    + apply equiv_post. intros s. split.
      * intros [[n Hn] Hb]. exists n. split; assumption.
      * intros [n [Hn Hb]]. split; [exists n |]; assumption.
  - (* ChoiceDisj *)
    apply (gF _ _ _ (F_Choice _ _ P Q1 Q2 _ _)).
    intros t [-> | ->]; [apply (H _ (or_introl eq_refl))
                        | apply (H _ (or_intror eq_refl))].
  - (* HavocFwd *)
    eapply D_Equiv; [apply (gF _ _ _ (F_Act _ _ P (IHavoc x))); no_prem |].
    apply equiv_post. intros s'. unfold sp_rel, havoc_post. simpl. split.
    + intros [s [HP [n ->]]]. exists s, n. auto.
    + intros [s [n [HP ->]]]. exists s. split; [exact HP | exists n; auto].
Qed.

(** ** Backward rules *)

Theorem bwd_instance : forall r ps c,
    bwd r -> imp_rule r ps c ->
    (forall t, ps t -> derivable GB (encT t)) -> derivable GB (encT c).
Proof.
  intros r ps c Hs HR H.
  destruct HR; simpl in Hs; try contradiction; simpl.
  - (* Skip *) apply (gB _ _ _ (B_Skip _ _ P)). no_prem.
  - (* AsgnBwd *)
    eapply D_Equiv; [apply (gB _ _ _ (B_Act _ _ Q (IAsgn x a))); no_prem |].
    apply equiv_pre. intros s. unfold wlp_rel, assn_sub. simpl. split.
    + intros Hw. apply Hw. reflexivity.
    + intros HQ s' ->. exact HQ.
  - (* Seq *)
    apply (gB _ _ _ (B_Seq _ _ P Q R (enc c1) (enc c2))).
    intros t [-> | ->]; [apply (H _ (or_introl eq_refl))
                        | apply (H _ (or_intror eq_refl))].
  - (* HavocBwd *)
    eapply D_Equiv; [apply (gB _ _ _ (B_Act _ _ Q (IHavoc x))); no_prem |].
    apply equiv_pre. intros s. unfold wlp_rel. simpl. split.
    + intros Hw n. apply Hw. exists n. reflexivity.
    + intros HQ s' [n ->]. apply HQ.
  - (* IfBwd *)
    apply (gB _ _ _ (B_Choice _ _ (fun s => bassn b s -> P1 s)
                       (fun s => ~ bassn b s -> P2 s) Q _ _)).
    intros t [-> | ->].
    + apply (gB _ _ _ (B_Seq _ _ _ P1 Q _ _)).
      intros t [-> | ->];
        [apply (gB _ _ _ (B_Assume _ _ P1 (bassn b))); no_prem
        | apply (H _ (or_introl eq_refl))].
    + apply (gB _ _ _ (B_Seq _ _ _ P2 Q _ _)).
      intros t [-> | ->];
        [apply (gB _ _ _ (B_Assume _ _ P2 (fun s => ~ bassn b s))); no_prem
        | apply (H _ (or_intror eq_refl))].
  - (* ChoiceBwd *)
    apply (gB _ _ _ (B_Choice _ _ P1 P2 Q _ _)).
    intros t [-> | ->]; [apply (H _ (or_introl eq_refl))
                        | apply (H _ (or_intror eq_refl))].
  - (* WhileWlp *)
    set (M := fun s => ~ bassn b s -> Q s).
    set (U := fun n => match n with
                       | 0 => M
                       | S k => fun s => bassn b s -> W k s
                       end).
    assert (HU : forall n, aequiv (wlp_family Q b W n) (U n)).
    { intros [|k] s; simpl; unfold M; destruct (bassn_dec b s) as [Hb | Hb];
        split; intros H1; try tauto. }
    eapply D_Equiv;
      [apply (gB _ _ _ (B_Seq _ _ (fun s => forall n, U n s) M Q
                          (KStar (KSeq (KAssume (bassn b)) (enc c)))
                          (KAssume (fun s => ~ bassn b s)))) |].
    + intros t [-> | ->].
      * apply (gB _ _ _ (B_Star _ _ U _)).
        intros t [n ->].
        apply (gB _ _ _ (B_Seq _ _ (U (S n)) (W n) (U n) _ _)).
        intros t [-> | ->];
          [apply (gB _ _ _ (B_Assume _ _ (W n) (bassn b))); no_prem |].
        eapply D_Equiv; [apply (H _ (ex_intro _ n eq_refl)) |].
        apply equiv_post, HU.
      * apply (gB _ _ _ (B_Assume _ _ Q (fun s => ~ bassn b s))). no_prem.
    + apply equiv_pre. intros s. split; intros H1 n; apply HU, H1.
Qed.

(** ** Whole derivations translate *)

Theorem sym_derivations : forall t,
    derivable sym_base t -> derivable GF (encT t).
Proof.
  intros t D. induction D as [ps c [r [Hs HR]] _ IH | t t' _ IH He].
  - exact (sym_instance r ps c Hs HR IH).
  - eapply D_Equiv; [exact IH | apply encT_proper, He].
Qed.

Definition bwd_base_imp : ruleset Imp :=
  fun ps c => exists r, bwd r /\ imp_rule r ps c.

Theorem bwd_derivations : forall t,
    derivable bwd_base_imp t -> derivable GB (encT t).
Proof.
  intros t D. induction D as [ps c [r [Hs HR]] _ IH | t t' _ IH He].
  - exact (bwd_instance r ps c Hs HR IH).
  - eapply D_Equiv; [exact IH | apply encT_proper, He].
Qed.
