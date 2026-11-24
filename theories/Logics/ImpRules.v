(** * The Imp rule pool

    Every proof rule for Imp, in one named family, without the
    consequence rule (that one is generic, see [CubeLogic]). Every rule is
    sound for Hoare logic. Logics pick the rules they need:

    - [classic]: the textbook Hoare rules (backward assignment and havoc,
      shared-post if and choice, invariant loop rule);
    - [sym]: forward assignment and havoc, disjunctive if and choice, and
      the iteration-indexed loop rule. These are sound under both
      approximations and derive exact strongest postconditions;
    - [bwd]: backward assignment and havoc, backward if and choice, and
      an iteration-indexed wlp loop rule. These derive exact weakest
      liberal preconditions; under complement they become the SIL
      rules. *)

From Stdlib Require Import String.
From LogicTransformers.Imp Require Import Syntax BigStep Lang.
From LogicTransformers.Logics Require Import Hoare.
From LogicTransformers.Framework Require Import Language ProgramLogic Cube.

Notation ht := (@mkTriple Imp).
Notation sp := (@img Imp).

Definition with_b (P : assertion Imp) (b : bexp) : assertion Imp :=
  fun st => P st /\ bassn b st.

Definition with_nb (P : assertion Imp) (b : bexp) : assertion Imp :=
  fun st => P st /\ ~ bassn b st.

(** Forward (Floyd-style) posts for assignment and havoc. *)
Definition asgn_post (x : var) (a : aexp) (P : assertion Imp)
  : assertion Imp :=
  fun st' => exists st, P st /\ st' = update st x (aeval st a).

Definition havoc_post (x : var) (P : assertion Imp) : assertion Imp :=
  fun st' => exists st n, P st /\ st' = update st x n.

Definition prem0 : triple Imp -> Prop := fun _ => False.
Definition prem1 (a : triple Imp) : triple Imp -> Prop := fun t => t = a.
Definition prem2 (a b : triple Imp) : triple Imp -> Prop :=
  fun t => t = a \/ t = b.

Inductive rule_name :=
  | RSkip
  | RAsgnBwd | RAsgnFwd
  | RSeq
  | RIf | RIfDisj
  | RWhileInv | RWhileIdx
  | RChoice | RChoiceDisj
  | RHavocBwd | RHavocFwd
  | RIfBwd | RChoiceBwd | RWhileWlp.

(** The posts of the wlp loop rule: [Q ∨ b] after zero iterations, and
    [W n ∨ ¬b] after [n + 1], where [W n] is the [n]-th premise's pre. *)
Definition wlp_family (Q : assertion Imp) (b : bexp)
    (W : nat -> assertion Imp) (n : nat) : assertion Imp :=
  match n with
  | 0 => fun st => Q st \/ bassn b st
  | S k => fun st => W k st \/ ~ bassn b st
  end.

Inductive imp_rule : rule_name -> ruleset Imp :=
  | IR_Skip : forall P,
      imp_rule RSkip prem0 (ht P CSkip P)
  | IR_AsgnBwd : forall Q x a,
      imp_rule RAsgnBwd prem0 (ht (assn_sub x a Q) (CAsgn x a) Q)
  | IR_AsgnFwd : forall P x a,
      imp_rule RAsgnFwd prem0 (ht P (CAsgn x a) (asgn_post x a P))
  | IR_Seq : forall P Q R c1 c2,
      imp_rule RSeq (prem2 (ht P c1 Q) (ht Q c2 R)) (ht P (CSeq c1 c2) R)
  | IR_If : forall P Q b c1 c2,
      imp_rule RIf
        (prem2 (ht (with_b P b) c1 Q) (ht (with_nb P b) c2 Q))
        (ht P (CIf b c1 c2) Q)
  | IR_IfDisj : forall P Q1 Q2 b c1 c2,
      imp_rule RIfDisj
        (prem2 (ht (with_b P b) c1 Q1) (ht (with_nb P b) c2 Q2))
        (ht P (CIf b c1 c2) (fun st => Q1 st \/ Q2 st))
  | IR_WhileInv : forall P b c,
      imp_rule RWhileInv
        (prem1 (ht (with_b P b) c P))
        (ht P (CWhile b c) (with_nb P b))
  | IR_WhileIdx : forall (P : nat -> assertion Imp) b c,
      imp_rule RWhileIdx
        (fun t => exists n, t = ht (with_b (P n) b) c (P (S n)))
        (ht (P 0) (CWhile b c) (fun st => exists n, with_nb (P n) b st))
  | IR_Choice : forall P Q c1 c2,
      imp_rule RChoice (prem2 (ht P c1 Q) (ht P c2 Q))
        (ht P (CChoice c1 c2) Q)
  | IR_ChoiceDisj : forall P Q1 Q2 c1 c2,
      imp_rule RChoiceDisj (prem2 (ht P c1 Q1) (ht P c2 Q2))
        (ht P (CChoice c1 c2) (fun st => Q1 st \/ Q2 st))
  | IR_HavocBwd : forall Q x,
      imp_rule RHavocBwd prem0
        (ht (fun st => forall n, Q (update st x n)) (CHavoc x) Q)
  | IR_HavocFwd : forall P x,
      imp_rule RHavocFwd prem0 (ht P (CHavoc x) (havoc_post x P))
  | IR_IfBwd : forall P1 P2 Q b c1 c2,
      imp_rule RIfBwd (prem2 (ht P1 c1 Q) (ht P2 c2 Q))
        (ht (fun st => (bassn b st -> P1 st) /\ (~ bassn b st -> P2 st))
            (CIf b c1 c2) Q)
  | IR_ChoiceBwd : forall P1 P2 Q c1 c2,
      imp_rule RChoiceBwd (prem2 (ht P1 c1 Q) (ht P2 c2 Q))
        (ht (fun st => P1 st /\ P2 st) (CChoice c1 c2) Q)
  | IR_WhileWlp : forall Q (W : nat -> assertion Imp) b c,
      imp_rule RWhileWlp
        (fun t => exists n, t = ht (W n) c (wlp_family Q b W n))
        (ht (fun st => forall n, wlp_family Q b W n st) (CWhile b c) Q).

(** ** Selections *)

Definition classic (r : rule_name) : Prop :=
  match r with
  | RSkip | RAsgnBwd | RSeq | RIf | RWhileInv | RChoice | RHavocBwd => True
  | _ => False
  end.

Definition sym (r : rule_name) : Prop :=
  match r with
  | RSkip | RAsgnFwd | RSeq | RIfDisj | RWhileIdx | RChoiceDisj
  | RHavocFwd => True
  | _ => False
  end.

Definition bwd (r : rule_name) : Prop :=
  match r with
  | RSkip | RAsgnBwd | RSeq | RIfBwd | RWhileWlp | RChoiceBwd
  | RHavocBwd => True
  | _ => False
  end.

(** ** Loop lemmas for the indexed rule *)

(** Over-approximation: if each iteration moves [P n] into [P (S n)],
    every exit state lies in some [P m] with the guard false. *)
Lemma while_idx_over : forall (P : nat -> assertion Imp) b c,
    (forall n s s', P n s -> bassn b s -> ceval c s s' -> P (S n) s') ->
    forall s s', ceval (CWhile b c) s s' ->
    forall n, P n s -> exists m, P m s' /\ ~ bassn b s'.
Proof.
  intros P b c Hbody s s' Hc.
  remember (CWhile b c) as w eqn:Ew.
  induction Hc; inversion Ew; subst; intros n HP.
  - exists n. split; [assumption | apply bassn_false'; assumption].
  - eapply IHHc2; [reflexivity | eapply Hbody; eassumption].
Qed.

(** Under-approximation: if every state of [P (S n)] is reached by one
    iteration from [P n], every state of [P n] is reached from [P 0] by a
    prefix of the loop. *)
Lemma while_idx_under : forall (P : nat -> assertion Imp) b c,
    (forall n s', P (S n) s' ->
       exists s, P n s /\ bassn b s /\ ceval c s s') ->
    forall n s', P n s' ->
    exists s, P 0 s /\
      (forall s'', ceval (CWhile b c) s' s'' ->
                   ceval (CWhile b c) s s'').
Proof.
  intros P b c Hbody n.
  induction n as [| n IH]; intros s' HP.
  - exists s'. auto.
  - destruct (Hbody n s' HP) as [s1 [HP1 [Hb Hc]]].
    destruct (IH s1 HP1) as [s0 [H0 Hpre]].
    exists s0. split; [exact H0 |].
    intros s'' Hw. apply Hpre. eapply E_WhileTrue; eassumption.
Qed.

(** ** Every rule is sound for Hoare logic *)

Lemma over_prem : forall (ps : triple Imp -> Prop),
    (forall t, ps t -> cube_valid Forward Over t) ->
    forall t, ps t ->
    forall s s', pre t s -> ceval (cmd t) s s' -> post t s'.
Proof. intros ps H t Ht. apply (hl_valid_iff t), H, Ht. Qed.

Theorem imp_rule_over_sound : forall r ps c,
    imp_rule r ps c ->
    (forall t, ps t -> cube_valid Forward Over t) ->
    cube_valid Forward Over c.
Proof.
  intros r ps c HR H. pose proof (over_prem _ H) as H'. clear H.
  apply hl_valid_iff.
  destruct HR; cbn; intros s s' HP Hc.
  - (* Skip *) inversion Hc; subst. exact HP.
  - (* AsgnBwd *) inversion Hc; subst. exact HP.
  - (* AsgnFwd *) inversion Hc; subst. exists s. auto.
  - (* Seq *)
    inversion Hc; subst.
    apply (H' (ht Q c2 R) (or_intror eq_refl) st'); [| assumption].
    apply (H' (ht P c1 Q) (or_introl eq_refl) s); assumption.
  - (* If *)
    inversion Hc; subst.
    + apply (H' _ (or_introl eq_refl) s); [split |]; assumption.
    + apply (H' _ (or_intror eq_refl) s);
        [split; [| apply bassn_false'] |]; assumption.
  - (* IfDisj *)
    inversion Hc; subst.
    + left. apply (H' _ (or_introl eq_refl) s); [split |]; assumption.
    + right. apply (H' _ (or_intror eq_refl) s);
        [split; [| apply bassn_false'] |]; assumption.
  - (* WhileInv *)
    remember (CWhile b c) as w eqn:Ew.
    revert HP. induction Hc; intros HP; inversion Ew; subst.
    + split; [assumption | apply bassn_false'; assumption].
    + apply IHHc2; [reflexivity |].
      apply (H' _ eq_refl st); [split |]; assumption.
  - (* WhileIdx *)
    apply (while_idx_over P b c) with (n := 0) in Hc; [| | exact HP].
    + destruct Hc as [m Hm]. exists m. exact Hm.
    + intros n s1 s2 H1 Hb Hc1.
      apply (H' _ (ex_intro _ n eq_refl) s1); [split |]; assumption.
  - (* Choice *)
    inversion Hc; subst.
    + apply (H' _ (or_introl eq_refl) s); assumption.
    + apply (H' _ (or_intror eq_refl) s); assumption.
  - (* ChoiceDisj *)
    inversion Hc; subst.
    + left. apply (H' _ (or_introl eq_refl) s); assumption.
    + right. apply (H' _ (or_intror eq_refl) s); assumption.
  - (* HavocBwd *) inversion Hc; subst. apply HP.
  - (* HavocFwd *) inversion Hc; subst. exists s, n. auto.
  - (* IfBwd *)
    inversion Hc; subst.
    + apply (H' _ (or_introl eq_refl) s); [apply (proj1 HP) |]; assumption.
    + apply (H' _ (or_intror eq_refl) s);
        [apply (proj2 HP), bassn_false' |]; assumption.
  - (* ChoiceBwd *)
    inversion Hc; subst.
    + apply (H' _ (or_introl eq_refl) s); [apply HP | assumption].
    + apply (H' _ (or_intror eq_refl) s); [apply HP | assumption].
  - (* WhileWlp *)
    remember (CWhile b c) as w eqn:Ew.
    revert HP. induction Hc; intros HP; inversion Ew; subst.
    + destruct (HP 0) as [Hq | Hb]; [exact Hq |].
      exfalso. unfold bassn in Hb. congruence.
    + apply IHHc2; [reflexivity |]. intros n.
      apply (H' _ (ex_intro _ n eq_refl) st); [| assumption].
      destruct (HP (S n)) as [Hw | Hnb]; [exact Hw |].
      exfalso. apply Hnb. assumption.
Qed.

(** ** The [sym] rules are sound for incorrectness logic *)

Lemma under_prem : forall (ps : triple Imp -> Prop),
    (forall t, ps t -> cube_valid Forward Under t) ->
    forall t, ps t ->
    forall s', post t s' -> exists s, pre t s /\ ceval (cmd t) s s'.
Proof. intros ps H t Ht. apply (il_valid_iff t), H, Ht. Qed.

Theorem imp_rule_under_sound : forall r ps c,
    sym r ->
    imp_rule r ps c ->
    (forall t, ps t -> cube_valid Forward Under t) ->
    cube_valid Forward Under c.
Proof.
  intros r ps c Hsym HR H. pose proof (under_prem _ H) as H'. clear H.
  apply il_valid_iff.
  destruct HR; simpl in Hsym; try contradiction; cbn; intros s' Hs'.
  - (* Skip *) exists s'. split; [exact Hs' | apply E_Skip].
  - (* AsgnFwd *)
    destruct Hs' as [s [HP ->]]. exists s. split; [exact HP | apply E_Asgn].
  - (* Seq *)
    destruct (H' (ht Q c2 R) (or_intror eq_refl) s' Hs') as [m [HQ Hc2]].
    destruct (H' (ht P c1 Q) (or_introl eq_refl) m HQ) as [s [HP Hc1]].
    exists s. split; [exact HP | eapply E_Seq; eassumption].
  - (* IfDisj *)
    destruct Hs' as [Hq | Hq].
    + destruct (H' _ (or_introl eq_refl) s' Hq) as [s [[HP Hb] Hc]].
      exists s. split; [exact HP | apply E_IfTrue; assumption].
    + destruct (H' _ (or_intror eq_refl) s' Hq) as [s [[HP Hb] Hc]].
      exists s. split; [exact HP |].
      apply E_IfFalse; [apply bassn_false |]; assumption.
  - (* WhileIdx *)
    destruct Hs' as [n [Hn Hnb]].
    assert (Hbody : forall n s', P (S n) s' ->
                      exists s, P n s /\ bassn b s /\ ceval c s s').
    { intros k s1 H1.
      destruct (H' _ (ex_intro _ k eq_refl) s1 H1) as [s0 [[H0 Hb] Hc]].
      exists s0. auto. }
    destruct (while_idx_under P b c Hbody n s' Hn) as [s [H0 Hpre]].
    exists s. split; [exact H0 |].
    apply Hpre, E_WhileFalse, bassn_false, Hnb.
  - (* ChoiceDisj *)
    destruct Hs' as [Hq | Hq].
    + destruct (H' _ (or_introl eq_refl) s' Hq) as [s [HP Hc]].
      exists s. split; [exact HP | apply E_ChoiceL; assumption].
    + destruct (H' _ (or_intror eq_refl) s' Hq) as [s [HP Hc]].
      exists s. split; [exact HP | apply E_ChoiceR; assumption].
  - (* HavocFwd *)
    destruct Hs' as [s [n [HP ->]]].
    exists s. split; [exact HP | apply E_Havoc].
Qed.

(** ** The [sym] rules derive exact strongest postconditions *)

Definition sym_base : ruleset Imp :=
  fun ps c => exists r, sym r /\ imp_rule r ps c.

Lemma sym_rule : forall r ps c,
    sym r -> imp_rule r ps c ->
    (forall t, ps t -> derivable sym_base t) ->
    derivable sym_base c.
Proof. intros r ps c Hs HR H. eapply D_Rule; [exists r; eauto | exact H]. Qed.

Lemma post_equiv : forall P c Q Q',
    aequiv Q Q' -> triple_equiv (ht P c Q) (ht P c Q').
Proof. intros P c Q Q' H. repeat split; auto; apply H. Qed.

Fixpoint iterates (b : bexp) (c : com) (P : assertion Imp) (n : nat)
  : assertion Imp :=
  match n with
  | 0 => P
  | S n => sp c (with_b (iterates b c P n) b)
  end.

Lemma sp_skip : forall P, aequiv P (sp CSkip P).
Proof.
  unfold aequiv, img. cbn. intros P s. split.
  - intros HP. exists s. split; [exact HP | apply E_Skip].
  - intros [s0 [HP Hc]]. inversion Hc; subst. exact HP.
Qed.

Lemma sp_asgn : forall x a P,
    aequiv (asgn_post x a P) (sp (CAsgn x a) P).
Proof.
  unfold aequiv, img, asgn_post. cbn. intros x a P s'. split.
  - intros [s [HP ->]]. exists s. split; [exact HP | apply E_Asgn].
  - intros [s [HP Hc]]. inversion Hc; subst. exists s. auto.
Qed.

Lemma sp_seq : forall c1 c2 P,
    aequiv (sp c2 (sp c1 P)) (sp (CSeq c1 c2) P).
Proof.
  unfold aequiv, img. cbn. intros c1 c2 P s''. split.
  - intros [s' [[s [HP H1]] H2]]. exists s.
    split; [exact HP | eapply E_Seq; eassumption].
  - intros [s [HP Hc]]. inversion Hc; subst.
    eexists. split; [exists s; split; eassumption | eassumption].
Qed.

Lemma sp_if : forall b c1 c2 P,
    aequiv (fun st => sp c1 (with_b P b) st \/ sp c2 (with_nb P b) st)
           (sp (CIf b c1 c2) P).
Proof.
  unfold aequiv, img, with_b, with_nb. cbn. intros b c1 c2 P s'. split.
  - intros [[s [[HP Hb] Hc]] | [s [[HP Hb] Hc]]]; exists s;
      (split; [exact HP |]).
    + apply E_IfTrue; assumption.
    + apply E_IfFalse; [apply bassn_false |]; assumption.
  - intros [s [HP Hc]]. inversion Hc; subst.
    + left. exists s. auto.
    + right. exists s. split; [split; [| apply bassn_false'] |]; assumption.
Qed.

Lemma sp_while : forall b c P,
    aequiv (fun st => exists n, with_nb (iterates b c P n) b st)
           (sp (CWhile b c) P).
Proof.
  intros b c P s'. split.
  - intros [n [Hn Hnb]].
    assert (Hbody : forall n s', iterates b c P (S n) s' ->
                      exists s, iterates b c P n s /\ bassn b s /\
                                ceval c s s').
    { intros k s1 [s0 [[H0 Hb] Hc]]. exists s0. auto. }
    destruct (while_idx_under (iterates b c P) b c Hbody n s' Hn)
      as [s [H0 Hpre]].
    exists s. split; [exact H0 |].
    apply Hpre, E_WhileFalse, bassn_false, Hnb.
  - intros [s [HP Hc]].
    apply (while_idx_over (iterates b c P) b c) with (n := 0) in Hc;
      [exact Hc | | exact HP].
    intros n s1 s2 H1 Hb Hc1. exists s1. split; [split |]; assumption.
Qed.

Lemma sp_choice : forall c1 c2 P,
    aequiv (fun st => sp c1 P st \/ sp c2 P st) (sp (CChoice c1 c2) P).
Proof.
  unfold aequiv, img. cbn. intros c1 c2 P s'. split.
  - intros [[s [HP Hc]] | [s [HP Hc]]]; exists s; split; auto.
    + apply E_ChoiceL; assumption.
    + apply E_ChoiceR; assumption.
  - intros [s [HP Hc]]. inversion Hc; subst; [left | right]; exists s; auto.
Qed.

Lemma sp_havoc : forall x P, aequiv (havoc_post x P) (sp (CHavoc x) P).
Proof.
  unfold aequiv, img, havoc_post. cbn. intros x P s'. split.
  - intros [s [n [HP ->]]]. exists s. split; [exact HP | apply E_Havoc].
  - intros [s [HP Hc]]. inversion Hc; subst. exists s, n. auto.
Qed.

Theorem sym_exact : forall c P, derivable sym_base (ht P c (sp c P)).
Proof.
  induction c; intros P.
  - eapply D_Equiv; [| apply post_equiv, sp_skip].
    eapply (sym_rule RSkip); [exact I | apply IR_Skip | intros t []].
  - eapply D_Equiv; [| apply post_equiv, sp_asgn].
    eapply (sym_rule RAsgnFwd); [exact I | apply IR_AsgnFwd | intros t []].
  - eapply D_Equiv; [| apply post_equiv, sp_seq].
    eapply (sym_rule RSeq); [exact I | apply IR_Seq |].
    intros t [-> | ->]; auto.
  - eapply D_Equiv; [| apply post_equiv, sp_if].
    eapply (sym_rule RIfDisj); [exact I | apply IR_IfDisj |].
    intros t [-> | ->]; auto.
  - eapply D_Equiv; [| apply (post_equiv (iterates b c P 0)), sp_while].
    eapply (sym_rule RWhileIdx); [exact I | apply IR_WhileIdx |].
    intros t [n ->]. apply IHc.
  - eapply D_Equiv; [| apply post_equiv, sp_choice].
    eapply (sym_rule RChoiceDisj); [exact I | apply IR_ChoiceDisj |].
    intros t [-> | ->]; auto.
  - eapply D_Equiv; [| apply post_equiv, sp_havoc].
    eapply (sym_rule RHavocFwd); [exact I | apply IR_HavocFwd | intros t []].
Qed.

(** ** The [bwd] rules derive exact weakest liberal preconditions *)

Notation wl := (@wlp Imp).

Lemma dual_prem : forall (ps : triple Imp -> Prop),
    (forall t, ps t -> dual_valid t) ->
    forall t, ps t ->
    forall s, (forall s', ceval (cmd t) s s' -> post t s') -> pre t s.
Proof. intros ps H t Ht. apply H, Ht. Qed.

(** The [bwd] rules are sound for the wlp-dual. *)
Theorem imp_rule_dual_sound : forall r ps c,
    bwd r ->
    imp_rule r ps c ->
    (forall t, ps t -> dual_valid t) ->
    dual_valid c.
Proof.
  intros r ps c Hbwd HR H. pose proof (dual_prem _ H) as H'. clear H.
  destruct HR; simpl in Hbwd; try contradiction;
    unfold dual_valid, aimpl, wlp; cbn; intros s Hw.
  - (* Skip *) apply Hw, E_Skip.
  - (* AsgnBwd *) apply Hw, E_Asgn.
  - (* Seq *)
    apply (H' _ (or_introl eq_refl)). intros s1 H1.
    apply (H' _ (or_intror eq_refl)). intros s2 H2.
    apply Hw. eapply E_Seq; eassumption.
  - (* HavocBwd *) intros n. apply Hw, E_Havoc.
  - (* IfBwd *)
    split; intros Hb.
    + apply (H' _ (or_introl eq_refl)). intros s' Hc.
      apply Hw, E_IfTrue; assumption.
    + apply (H' _ (or_intror eq_refl)). intros s' Hc.
      apply Hw, E_IfFalse; [apply bassn_false |]; assumption.
  - (* ChoiceBwd *)
    split.
    + apply (H' _ (or_introl eq_refl)). intros s' Hc.
      apply Hw, E_ChoiceL. assumption.
    + apply (H' _ (or_intror eq_refl)). intros s' Hc.
      apply Hw, E_ChoiceR. assumption.
  - (* WhileWlp *)
    intros n. revert s Hw.
    induction n as [| n IH]; intros s Hw; cbn.
    + destruct (beval s b) eqn:E; [right; exact E |].
      left. apply Hw, E_WhileFalse, E.
    + destruct (beval s b) eqn:E.
      * left. apply (H' _ (ex_intro _ n eq_refl)). intros s1 H1.
        apply IH. intros s'' H2. apply Hw. eapply E_WhileTrue; eassumption.
      * right. apply bassn_false'. exact E.
Qed.

(** A triple is wlp-exact when its pre is the weakest liberal
    precondition, i.e. it is both HL-valid and wlp-dual-valid. *)
Definition wexact (t : triple Imp) : Prop :=
  aequiv (pre t) (wl (cmd t) (post t)).

Lemma wexact_iff : forall t,
    wexact t <-> cube_valid Forward Over t /\ dual_valid t.
Proof.
  intros t. rewrite hl_valid_iff.
  unfold wexact, dual_valid, aequiv, aimpl, wlp. split.
  - intros H. split.
    + intros s s' Hp Hc. exact (proj1 (H s) Hp s' Hc).
    + intros s Hw. apply H, Hw.
  - intros [H1 H2] s. split.
    + intros Hp s' Hc. eapply H1; eauto.
    + apply H2.
Qed.

(** A [bwd] rule with wlp-exact premises has a wlp-exact conclusion. *)
Lemma bwd_step : forall r ps c,
    imp_rule r ps c -> bwd r ->
    (forall t, ps t -> wexact t) -> wexact c.
Proof.
  intros r ps c HR Hb H. apply wexact_iff. split.
  - apply (imp_rule_over_sound r ps c HR).
    intros t Ht. apply wexact_iff, H, Ht.
  - apply (imp_rule_dual_sound r ps c Hb HR).
    intros t Ht. apply wexact_iff, H, Ht.
Qed.

Definition bwd_base : ruleset Imp :=
  fun ps c => exists r, bwd r /\ imp_rule r ps c.

Lemma bwd_rule : forall r ps c,
    imp_rule r ps c -> bwd r ->
    (forall t, ps t -> derivable bwd_base t) ->
    derivable bwd_base c.
Proof. intros r ps c HR Hs H. eapply D_Rule; [exists r; eauto | exact H]. Qed.

Lemma wexact_wlp : forall c Q, wexact (ht (wl c Q) c Q).
Proof. intros c Q s. reflexivity. Qed.

Lemma wexact_equiv : forall P c Q,
    wexact (ht P c Q) -> triple_equiv (ht P c Q) (ht (wl c Q) c Q).
Proof. intros P c Q H. repeat split; auto; apply H. Qed.

(** The posts used by the wlp loop rule in an exact derivation. *)
Fixpoint wlp_iter (Q : assertion Imp) (b : bexp) (c : com) (n : nat)
  : assertion Imp :=
  match n with
  | 0 => fun st => Q st \/ bassn b st
  | S n => fun st => wl c (wlp_iter Q b c n) st \/ ~ bassn b st
  end.

Ltac bwd_case HR prems_der prems_ex :=
  eapply D_Equiv;
  [ eapply (bwd_rule _ _ _ HR I); prems_der
  | apply wexact_equiv; eapply (bwd_step _ _ _ HR I); prems_ex ].

Theorem bwd_exact : forall c Q, derivable bwd_base (ht (wl c Q) c Q).
Proof.
  induction c; intros Q.
  - bwd_case (IR_Skip Q) ltac:(intros t []) ltac:(intros t []).
  - bwd_case (IR_AsgnBwd Q x a) ltac:(intros t []) ltac:(intros t []).
  - bwd_case (IR_Seq (wl c1 (wl c2 Q)) (wl c2 Q) Q c1 c2)
      ltac:(intros t [-> | ->]; auto)
      ltac:(intros t [-> | ->]; apply wexact_wlp).
  - bwd_case (IR_IfBwd (wl c1 Q) (wl c2 Q) Q b c1 c2)
      ltac:(intros t [-> | ->]; auto)
      ltac:(intros t [-> | ->]; apply wexact_wlp).
  - bwd_case (IR_WhileWlp Q (fun n => wl c (wlp_iter Q b c n)) b c)
      ltac:(intros t [n ->]; destruct n; apply IHc)
      ltac:(intros t [n ->]; destruct n; apply wexact_wlp).
  - bwd_case (IR_ChoiceBwd (wl c1 Q) (wl c2 Q) Q c1 c2)
      ltac:(intros t [-> | ->]; auto)
      ltac:(intros t [-> | ->]; apply wexact_wlp).
  - bwd_case (IR_HavocBwd Q x) ltac:(intros t []) ltac:(intros t []).
Qed.
