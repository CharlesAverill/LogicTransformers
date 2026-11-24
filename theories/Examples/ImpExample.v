(** * Example: Imp, through its encoding into the core

    The program moves [x] into [y] one unit at a time, but may also idle:

<<
      count := while 0 < x do ((x := x - 1; y := y + 1) ⊕ skip)
>>

    It is written in Imp's own syntax, run through the encoding [enc]
    ([Core.ImpCore], with [enc_correct]), and reasoned about with the
    generated logics for Imp's atoms (assignment and havoc). Its behaviour,
    characterized once:

    - [count_run]: it ends in [s'] from [s] iff [x' = 0], [y' = y + x], and
      all other variables are unchanged;
    - [count_div]: it can diverge from [s] iff [0 < x] (by idling forever).

    Imp states are total functions [string -> nat], so showing that a run
    ends in a *given* state needs [functional_extensionality]
    ([count_complete]). The concrete stack and robot states of the other
    examples need no such axiom. Every node of the cube then gets a triple,
    proved valid from the two facts and derived in that node's generated
    logic by completeness. *)

From Stdlib Require Import String Arith Lia FunctionalExtensionality.
From LogicTransformers.Imp Require Import Syntax BigStep Lang.
From LogicTransformers.Logics Require Import Hoare.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube CubeLogic.
From LogicTransformers.Core Require Import
  Kernel KernelBot Generate GenerateBot CoreCousot ImpCore.
From LogicTransformers.Examples Require Import Common.

Local Open Scope string_scope.
Local Notation X := "x".
Local Notation Y := "y".

Local Open Scope com_scope.

Definition guard : bexp := <{ X > 0 }>.
Definition inc : com := <{ X := X - 1 ; Y := Y + 1 }>.
Definition count : com :=
  <{ while X > 0 do
       (X := X - 1 ; Y := Y + 1) ⊕ skip
     end }>.

Example count_shape : count = CWhile guard (CChoice inc CSkip).
Proof. reflexivity. Qed.

Example count_terms :
  count = CWhile (BNot (BLe (AVar X) (ANum 0)))
            (CChoice (CSeq (CAsgn X (AMinus (AVar X) (ANum 1)))
                           (CAsgn Y (APlus (AVar Y) (ANum 1))))
                     CSkip).
Proof. reflexivity. Qed.

Definition cprog : kcom state iact := enc count.

(** ** Characterizing the program *)

Lemma guard_true : forall s, beval s guard = true <-> 0 < s X.
Proof.
  intros s. unfold guard. simpl. destruct (s X); simpl; split; intros H;
    try discriminate; try lia; reflexivity.
Qed.

Lemma inc_effect : forall s s', ceval inc s s' ->
    s' X = s X - 1 /\ s' Y = s Y + 1 /\
    forall z, z <> X -> z <> Y -> s' z = s z.
Proof.
  intros s s' H. inversion H; subst.
  repeat match goal with H' : ceval (CAsgn _ _) _ _ |- _ =>
    inversion H'; subst; clear H' end.
  repeat split. intros z H1 H2. rewrite !update_neq by congruence.
  reflexivity.
Qed.

Definition Ri (s s' : state) : Prop :=
  s' X = 0 /\ s' Y = s Y + s X /\ forall z, z <> X -> z <> Y -> s' z = s z.

Lemma count_sound : forall s s', ceval count s s' -> Ri s s'.
Proof.
  intros s s' H. remember count as w eqn:Ew.
  induction H; inversion Ew; subst.
  - assert (Hx : st X = 0).
    { destruct (st X) eqn:E; [reflexivity |].
      exfalso. change (beval st guard = false) in H.
      assert (0 < st X) by lia. apply guard_true in H0. congruence. }
    unfold Ri. repeat split; auto; lia.
  - destruct (IHceval2 eq_refl) as [Hx [Hy Ho]].
    assert (Hp : 0 < st X) by (apply guard_true; assumption).
    match goal with
    | H' : ceval (CChoice _ _) _ _ |- _ => inversion H'; subst
    end.
    + match goal with H' : ceval (CSeq _ _) _ _ |- _ =>
        destruct (inc_effect _ _ H') as [Ex [Ey Eo]] end.
      unfold Ri. repeat split; [exact Hx | lia |].
      intros z Hz1 Hz2. rewrite Ho, Eo; auto.
    + match goal with H' : ceval CSkip _ _ |- _ => inversion H'; subst end.
      unfold Ri. auto.
Qed.

Lemma count_complete : forall n s s', s X = n -> Ri s s' -> ceval count s s'.
Proof.
  induction n as [| n IH]; intros s s' Hn [Hx [Hy Ho]].
  - assert (E : s' = s).
    { apply functional_extensionality. intros z.
      destruct (string_dec z X) as [-> | HX]; [lia |].
      destruct (string_dec z Y) as [-> | HY]; [lia | auto]. }
    rewrite E. apply E_WhileFalse. unfold guard. simpl. rewrite Hn. reflexivity.
  - set (s1 := update (update s X (aeval s (AMinus (AVar X) (ANum 1)))) Y
                 (aeval (update s X (aeval s (AMinus (AVar X) (ANum 1))))
                        (APlus (AVar Y) (ANum 1)))).
    assert (Hinc : ceval inc s s1) by (eapply E_Seq; apply E_Asgn).
    destruct (inc_effect _ _ Hinc) as [Ex [Ey Eo]].
    eapply E_WhileTrue; [apply guard_true; lia | apply E_ChoiceL, Hinc |].
    apply IH; [lia |]. unfold Ri. repeat split; [exact Hx | lia |].
    intros z H1 H2. rewrite Ho, Eo; auto.
Qed.

Theorem count_run : forall s s', kev iact_sem cprog s s' <-> Ri s s'.
Proof.
  intros s s'. unfold cprog. rewrite <- enc_correct. split.
  - apply count_sound.
  - apply (count_complete (s X)). reflexivity.
Qed.

(** The final state of a run, given pointwise. *)
Definition final (s : state) : state :=
  update (update s X 0) Y (s Y + s X).

Lemma Ri_final : forall s, Ri s (final s).
Proof.
  intros s. unfold Ri, final. repeat split. intros z H1 H2.
  rewrite !update_neq by congruence. reflexivity.
Qed.

Lemma Ri_refl : forall s, s X = 0 -> Ri s s.
Proof. intros s H. unfold Ri. repeat split; auto. lia. Qed.

Theorem count_div : forall s, kdiv iact_sem cprog s <-> 0 < s X.
Proof.
  intros s. split.
  - intros H. apply guard_true.
    exact (kwhile_div_guard iact_sem (bassn guard) (enc (CChoice inc CSkip))
             s H).
  - apply (kwhile_div_intro iact_sem (fun s => 0 < s X)).
    intros s0 H. split; [apply guard_true, H |].
    exists s0. split; [apply KE_ChoiceR, KE_Skip | exact H].
Qed.

(** ** Top face *)

Notation T := ICore.
Notation B := (KLangB iact_sem).

Definition tri {L : Language} (P : assertion L) c (Q : assertion L) :=
  mkTriple P c Q.

Definition Sum10 (s : state) : Prop := s X + s Y = 10.
Definition Done10 (s : state) : Prop := s X = 0 /\ s Y = 10.

(** HL: if [x + y = 10], every terminating run ends with [x = 0, y = 10]. *)
Definition t_HL : triple T := @tri T Sum10 cprog Done10.
Lemma v_HL : cvalid Forward Plain Over t_HL.
Proof.
  apply hl_valid_iff. intros s s' HP Hc. apply count_run in Hc.
  destruct Hc as [Hx [Hy _]]. simpl in *. unfold Sum10, Done10 in *. lia.
Qed.
Theorem imp_HL : derivable (rules (HL_t iact_sem)) t_HL.
Proof. apply derive_HL_t, v_HL. Qed.

(** IL: every [x = 0, y = 10] state is reachable from [x = 3, y = 7]. *)
Definition t_IL : triple T :=
  @tri T (fun s => s X = 3 /\ s Y = 7) cprog Done10.
Lemma v_IL : cvalid Forward Plain Under t_IL.
Proof.
  apply il_valid_iff. intros s' [Hx Hy]. simpl in *.
  exists (update (update s' X 3) Y 7). split.
  - split; [rewrite update_neq by discriminate |]; apply update_eq.
  - apply count_run. unfold Ri. repeat split; [exact Hx | |].
    + rewrite update_eq, update_neq, update_eq by discriminate. lia.
    + intros z H1 H2. rewrite !update_neq by congruence. reflexivity.
Qed.
Theorem imp_IL : derivable (rules (IL_t iact_sem)) t_IL.
Proof. apply derive_IL_t, v_IL. Qed.

(** NC: reaching [x = 0, y = 10] requires [x + y = 10]. *)
Lemma v_NC : cvalid Backward Plain Over t_HL.
Proof.
  apply nc_valid_iff. intros s s' Hc [Hx Hy]. apply count_run in Hc.
  destruct Hc as [_ [Hy' _]]. simpl in *. unfold Sum10. lia.
Qed.
Theorem imp_NC : derivable (rules (NC_t iact_sem)) t_HL.
Proof. apply derive_NC_t, v_NC. Qed.

(** SIL: from [x + y = 10] some run reaches [y = 10]. *)
Definition t_SIL : triple T := @tri T Sum10 cprog (fun s => s Y = 10).
Lemma v_SIL : cvalid Backward Plain Under t_SIL.
Proof.
  apply sil_valid_iff. intros s HP. exists (final s).
  split; [apply count_run, Ri_final |].
  simpl in *. unfold final, Sum10 in *. rewrite update_eq. lia.
Qed.
Theorem imp_SIL : derivable (rules (SIL_t iact_sem)) t_SIL.
Proof. apply derive_SIL_t, v_SIL. Qed.

(** p̃ost ⊆: an end state all of whose possible starts had [x + y = 10]
    has [x ≠ 0] (no start at all) or [y = 10]. *)
Definition t_PostDO : triple T :=
  @tri T Sum10 cprog (fun s => s X <> 0 \/ s Y = 10).
Lemma v_PostDO : cvalid Forward Dual Over t_PostDO.
Proof.
  unfold t_PostDO, tri. simpl. unfold aimpl, dimg. simpl. intros s' H.
  destruct (Nat.eq_dec (s' X) 0) as [Hx | Hx]; [right | left; exact Hx].
  assert (HP := H s' (proj2 (count_run s' s') (Ri_refl s' Hx))).
  unfold Sum10 in HP. lia.
Qed.
Theorem imp_PostDO : derivable (rules (PostDO_t iact_sem)) t_PostDO.
Proof. apply derive_PostDO_t, v_PostDO. Qed.

(** p̃ost ⊇: Galois-equivalent to NC. *)
Lemma v_PostDU : cvalid Forward Dual Under t_HL.
Proof. apply galois_pre_dimg, v_NC. Qed.
Theorem imp_PostDU : derivable (rules (PostDU_t iact_sem)) t_HL.
Proof. apply derive_PostDU_t, v_PostDU. Qed.

(** p̃re ⊆: if every run is sure to end with [y = 10], then [x + y = 10]. *)
Lemma v_PreDO : cvalid Backward Dual Over t_SIL.
Proof.
  unfold t_SIL, tri. simpl. unfold aimpl, wlp. simpl. intros s H.
  assert (Hy := H (final s) (proj2 (count_run _ _) (Ri_final s))).
  unfold final, Sum10 in *. rewrite update_eq in Hy. lia.
Qed.
Theorem imp_PreDO : derivable (rules (PreDO_t iact_sem)) t_SIL.
Proof. apply derive_PreDO_t, v_PreDO. Qed.

(** p̃re ⊇: Galois-equivalent to HL. *)
Lemma v_PreDU : cvalid Backward Dual Under t_HL.
Proof. apply galois_post_wlp, v_HL. Qed.
Theorem imp_PreDU : derivable (rules (PreDU_t iact_sem)) t_HL.
Proof. apply derive_PreDU_t, v_PreDU. Qed.

(** ** Bottom face (⊥ = [None] is nontermination) *)

Definition SomeP (P : state -> Prop) (bot : Prop) : assertion B :=
  fun o => match o with Some s => P s | None => bot end.

(** HL⊥: from [x + y = 10], the program diverges or ends with
    [x = 0, y = 10]. *)
Definition b_HL : triple B :=
  @tri B (SomeP Sum10 False) cprog (SomeP Done10 True).
Lemma vb_HL : cvalid Forward Plain Over b_HL.
Proof.
  apply hl_valid_iff. intros [s|] [s'|] HP Hc; simpl in *; try contradiction;
    auto.
  apply count_run in Hc. destruct Hc as [Hx [Hy _]].
  unfold Sum10, Done10 in *. lia.
Qed.
Theorem imp_HL_bot : derivable (rules (HL_b iact_sem)) b_HL.
Proof. apply derive_HL_b, vb_HL. Qed.

(** IL⊥: divergence is reachable from [x = 1]. *)
Definition b_IL : triple B :=
  @tri B (SomeP (fun s => s X = 1) False) cprog (fun o => o = None).
Lemma vb_IL : cvalid Forward Plain Under b_IL.
Proof.
  apply il_valid_iff. intros o' Ho'. simpl in Ho'. subst.
  exists (Some (update empty_state X 1)). split.
  - simpl. apply update_eq.
  - simpl. apply count_div. rewrite update_eq. lia.
Qed.
Theorem imp_IL_bot : derivable (rules (IL_b iact_sem)) b_IL.
Proof. apply derive_IL_b, vb_IL. Qed.

(** NC⊥: only starts with [0 < x] (or ⊥ itself) can lead to ⊥. *)
Definition P_div : assertion B := SomeP (fun s => 0 < s X) True.
Definition b_NC : triple B := @tri B P_div cprog (fun o => o = None).
Lemma vb_NC : cvalid Backward Plain Over b_NC.
Proof.
  apply nc_valid_iff. intros [s|] o' Hc Ho'; simpl in *; subst; [| exact I].
  apply count_div, Hc.
Qed.
Theorem imp_NC_bot : derivable (rules (NC_b iact_sem)) b_NC.
Proof. apply derive_NC_b, vb_NC. Qed.

(** SIL⊥: every start with [0 < x] can diverge. *)
Definition b_SIL : triple B :=
  @tri B (SomeP (fun s => 0 < s X) False) cprog (fun o => o = None).
Lemma vb_SIL : cvalid Backward Plain Under b_SIL.
Proof.
  apply sil_valid_iff. intros [s|] HP; simpl in HP; [| contradiction].
  exists None. split; [apply count_div, HP | reflexivity].
Qed.
Theorem imp_SIL_bot : derivable (rules (SIL_b iact_sem)) b_SIL.
Proof. apply derive_SIL_b, vb_SIL. Qed.

(** p̃ost ⊆ ⊥: an outcome all of whose possible starts have [0 < x] (or
    are ⊥) is ⊥, or a state with [x ≠ 0] (no start at all). *)
Definition b_PostDO : triple B := @tri B P_div cprog P_div.
Lemma vb_PostDO : cvalid Forward Dual Over b_PostDO.
Proof.
  unfold b_PostDO, tri, P_div, SomeP. simpl. unfold aimpl, dimg. simpl.
  intros [s'|] H; [| exact I].
  destruct (Nat.eq_dec (s' X) 0) as [Hx | Hx]; [exfalso | lia].
  assert (HP := H (Some s') (proj2 (count_run s' s') (Ri_refl s' Hx))).
  simpl in HP. lia.
Qed.
Theorem imp_PostDO_bot : derivable (rules (PostDO_b iact_sem)) b_PostDO.
Proof. apply derive_PostDO_b, vb_PostDO. Qed.

(** p̃ost ⊇ ⊥: Galois-equivalent to NC⊥. *)
Lemma vb_PostDU : cvalid Forward Dual Under b_NC.
Proof. apply galois_pre_dimg, vb_NC. Qed.
Theorem imp_PostDU_bot : derivable (rules (PostDU_b iact_sem)) b_NC.
Proof. apply derive_PostDU_b, vb_PostDU. Qed.

(** p̃re ⊆ ⊥: if every outcome is a state with [y = 10] (so no divergence),
    the start had [x = 0] and [y = 10]. *)
Definition b_PreDO : triple B :=
  @tri B (SomeP Done10 False) cprog (SomeP (fun s => s Y = 10) False).
Lemma vb_PreDO : cvalid Backward Dual Over b_PreDO.
Proof.
  unfold b_PreDO, tri, SomeP. simpl. unfold aimpl, wlp. simpl.
  intros [s|] H.
  - destruct (Nat.eq_dec (s X) 0) as [Hx | Hx].
    + split; [exact Hx |].
      exact (H (Some s) (proj2 (count_run s s) (Ri_refl s Hx))).
    + exfalso. apply (H None). simpl. apply count_div. lia.
  - exact (H None I).
Qed.
Theorem imp_PreDO_bot : derivable (rules (PreDO_b iact_sem)) b_PreDO.
Proof. apply derive_PreDO_b, vb_PreDO. Qed.

(** p̃re ⊇ ⊥: Galois-equivalent to HL⊥. *)
Lemma vb_PreDU : cvalid Backward Dual Under b_HL.
Proof. apply galois_post_wlp, vb_HL. Qed.
Theorem imp_PreDU_bot : derivable (rules (PreDU_b iact_sem)) b_HL.
Proof. apply derive_PreDU_b, vb_PreDU. Qed.

(** ** Back to Imp's own syntax

    Top-face validity transfers between [count] and its encoding
    ([enc_cvalid]), so the HL fact holds for the Imp program itself. *)
Corollary count_HL_source :
  cvalid Forward Plain Over (@mkTriple Imp Sum10 count Done10).
Proof. apply (enc_cvalid Forward Plain Over), v_HL. Qed.
