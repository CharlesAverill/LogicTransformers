(** * Example: a stack language with its own syntax, encoded into the core

    States are stacks of naturals. Two instructions:

    - [acc]: [n :: a :: r ↦ n :: (a + n) :: r] (add the top to the second);
    - [dec]: [n :: r ↦ (n - 1) :: r].

    Programs: instructions, sequencing, and [loop p] (run [p] while the
    top is nonzero). The language has its own big-step semantics
    ([sexec]), and [senc] encodes it into the core, with [loop p] as
    [(assume top≠0; p)*; assume top=0]. [senc_correct] proves the encoding
    preserves the semantics.

    The program [triangle = loop (acc; dec)] turns [n :: a :: r] into
    [0 :: (a + 1 + 2 + … + n) :: r]. It is deterministic and always
    terminates. It gets stuck (no run at all) on a one-element stack with a
    nonzero top.

    - [triangle_run]: exact input/output relation;
    - [triangle_no_div]: it never diverges (the top decreases).

    Every node of the cube gets a triple, proved valid from these and
    derived in that node's generated logic by completeness. *)

From Stdlib Require Import Arith Lia List.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube CubeLogic.
From LogicTransformers.Core Require Import
  Kernel KernelBot Generate GenerateBot CoreCousot.
From LogicTransformers.Examples Require Import Common.
Import ListNotations.

Definition stack : Type := list nat.

Inductive sinstr := IAcc | IDec.

Definition sinstr_sem (i : sinstr) (s s' : stack) : Prop :=
  match i, s with
  | IAcc, n :: a :: r => s' = n :: (a + n) :: r
  | IDec, n :: r => s' = pred n :: r
  | _, _ => False
  end.

Definition nz (s : stack) : Prop :=
  match s with n :: _ => n <> 0 | [] => False end.

(** ** Source syntax, source semantics, and the encoding *)

Inductive scom := SI (i : sinstr) | SSeq (p q : scom) | SLoop (p : scom).

Inductive sexec : scom -> stack -> stack -> Prop :=
  | X_I : forall i s s', sinstr_sem i s s' -> sexec (SI i) s s'
  | X_Seq : forall p q s s1 s2,
      sexec p s s1 -> sexec q s1 s2 -> sexec (SSeq p q) s s2
  | X_LoopExit : forall p s, ~ nz s -> sexec (SLoop p) s s
  | X_LoopIter : forall p s s1 s2,
      nz s -> sexec p s s1 -> sexec (SLoop p) s1 s2 -> sexec (SLoop p) s s2.

Fixpoint senc (p : scom) : kcom stack sinstr :=
  match p with
  | SI i => KAct i
  | SSeq p q => KSeq (senc p) (senc q)
  | SLoop p => kwhile nz (senc p)
  end.

Notation kevS := (kev sinstr_sem).

Lemma senc_loop_star : forall p,
    (forall s s', kevS (senc p) s s' -> sexec p s s') ->
    forall s s1, kevS (KStar (KSeq (KAssume nz) (senc p))) s s1 ->
    forall s2, sexec (SLoop p) s1 s2 -> sexec (SLoop p) s s2.
Proof.
  intros p IH s s1 H. remember (KStar (KSeq (KAssume nz) (senc p))) as k eqn:Ek.
  induction H; inversion Ek; subst; intros s3 H3; [exact H3 |].
  match goal with H' : kevS (KSeq _ _) _ _ |- _ => inversion H'; subst end.
  match goal with H' : kevS (KAssume _) _ _ |- _ => inversion H'; subst end.
  eapply X_LoopIter; [assumption | apply IH; eassumption | apply IHkev2; auto].
Qed.

Theorem senc_correct : forall p s s', sexec p s s' <-> kevS (senc p) s s'.
Proof.
  intros p s s'. split.
  - intros H. induction H; simpl.
    + apply KE_Act. assumption.
    + eapply KE_Seq; eassumption.
    + apply kwhile_run_iff. split; [apply KE_StarRefl | assumption].
    + apply kwhile_run_iff. simpl in IHsexec2.
      apply kwhile_run_iff in IHsexec2 as [Hs Hn]. split; [| exact Hn].
      eapply KE_StarStep; [eapply KE_Seq; [apply KE_Assume, H | exact IHsexec1]
                          | exact Hs].
  - revert s s'. induction p; intros s s' H; simpl in H.
    + inversion H; subst. apply X_I. assumption.
    + inversion H; subst. eapply X_Seq; eauto.
    + apply kwhile_run_iff in H as [Hs Hn].
      eapply senc_loop_star; [exact IHp | exact Hs | apply X_LoopExit, Hn].
Qed.

(** ** The program *)

Definition triangle : scom := SLoop (SSeq (SI IAcc) (SI IDec)).
Definition tprog : kcom stack sinstr := senc triangle.
Definition tbody : kcom stack sinstr := KSeq (KAct IAcc) (KAct IDec).

Fixpoint trin (n : nat) : nat := match n with 0 => 0 | S k => S k + trin k end.

Lemma tbody_sem : forall s s', kevS tbody s s' <->
    match s with
    | n :: a :: r => s' = pred n :: (a + n) :: r
    | _ => False
    end.
Proof.
  intros s s'. split.
  - intros H. inversion H; subst.
    repeat match goal with H' : kevS (KAct _) _ _ |- _ =>
      inversion H'; subst; clear H' end.
    simpl in *. destruct s as [| n [| a r]]; try contradiction. subst.
    simpl in *. assumption.
  - destruct s as [| n [| a r]]; try contradiction. intros ->.
    eapply KE_Seq; apply KE_Act; simpl; reflexivity.
Qed.

Notation tstar := (KStar (KSeq (KAssume nz) tbody)).

Lemma star_stuck : forall s s1,
    (forall s2, ~ kevS (KSeq (KAssume nz) tbody) s s2) ->
    kevS tstar s s1 -> s1 = s.
Proof.
  intros s s1 Hno H. inversion H; subst; [reflexivity |].
  exfalso. eapply Hno. eassumption.
Qed.

Lemma star_tri : forall s s1, kevS tstar s s1 ->
    forall n a r, s = n :: a :: r ->
    exists m a1, s1 = m :: a1 :: r /\ a1 + trin m = a + trin n.
Proof.
  intros s s1 H. remember tstar as k eqn:Ek.
  induction H; inversion Ek; subst; intros n a r ->.
  - exists n, a. auto.
  - match goal with H' : kevS (KSeq (KAssume _) _) _ _ |- _ =>
      inversion H'; subst end.
    match goal with H' : kevS (KAssume _) _ _ |- _ => inversion H'; subst end.
    match goal with H' : kevS tbody _ _ |- _ => apply tbody_sem in H' end.
    subst. destruct (IHkev2 eq_refl (pred n) (a + n) r eq_refl)
      as [m [a1 [-> Hm]]].
    exists m, a1. split; [reflexivity |].
    destruct n as [| k]; [simpl in *; contradiction |]. simpl in *. lia.
Qed.

Lemma star_run : forall n a r,
    kevS tstar (n :: a :: r) (0 :: (a + trin n) :: r).
Proof.
  induction n as [| k IH]; intros a r.
  - rewrite Nat.add_0_r. apply KE_StarRefl.
  - eapply KE_StarStep.
    + eapply KE_Seq; [apply KE_Assume; simpl; lia |].
      apply tbody_sem. reflexivity.
    + simpl. replace (a + S (k + trin k)) with (a + S k + trin k) by lia.
      apply IH.
Qed.

Definition Rt (s s' : stack) : Prop :=
  match s with
  | [] => s' = []
  | 0 :: r => s' = s
  | S k :: a :: r => s' = 0 :: (a + trin (S k)) :: r
  | [S k] => False
  end.

Lemma triangle_run : forall s s', kevS tprog s s' <-> Rt s s'.
Proof.
  intros s s'. unfold tprog. simpl. rewrite kwhile_run_iff. split.
  - intros [H Hn]. destruct s as [| n [| a r]].
    + apply star_stuck in H; [subst; reflexivity |].
      intros s2 H2. inversion H2; subst.
      match goal with H' : kevS (KAssume _) _ _ |- _ => inversion H'; subst end.
      simpl in *. contradiction.
    + apply star_stuck in H.
      * subst. destruct n; [reflexivity | simpl in Hn; lia].
      * intros s2 H2. inversion H2; subst.
        match goal with H' : kevS (KAssume _) _ _ |- _ =>
          inversion H'; subst end.
        match goal with H' : kevS tbody _ _ |- _ => apply tbody_sem in H' end.
        contradiction.
    + destruct (star_tri _ _ H n a r eq_refl) as [m [a1 [-> Hm]]].
      simpl in Hn. assert (m = 0) by lia. subst m. simpl in Hm.
      destruct n as [| k]; simpl in *; [f_equal; f_equal; lia |].
      f_equal. f_equal. lia.
  - destruct s as [| [| k] [| a r]]; simpl; intros H; subst;
      try contradiction.
    + split; [apply KE_StarRefl | simpl; auto].
    + split; [apply KE_StarRefl | simpl; auto].
    + split; [apply KE_StarRefl | simpl; auto].
    + split; [apply (star_run (S k) a r) | simpl; auto].
Qed.

Lemma triangle_no_div : forall s, ~ kdiv sinstr_sem tprog s.
Proof.
  apply (kwhile_no_div sinstr_sem
           (fun s => match s with n :: _ => n | [] => 0 end)).
  - intros s H. inversion H; subst;
      match goal with H' : kdiv _ (KAct _) _ |- _ => inversion H' end.
  - intros s s' Hnz Hc. apply tbody_sem in Hc.
    destruct s as [| n [| a r]]; try contradiction. subst. simpl in *. lia.
Qed.

(** ** Top face *)

Notation T := (KLang sinstr_sem).
Notation B := (KLangB sinstr_sem).

Definition tri {L : Language} (P : assertion L) c (Q : assertion L) :=
  mkTriple P c Q.

Definition Pn0 (s : stack) : Prop := exists n, s = [n; 0].
Definition Qtri (s : stack) : Prop := exists n, s = [0; trin n].

Lemma run_n0 : forall n, Rt [n; 0] [0; trin n].
Proof. intros [| k]; reflexivity. Qed.

(** HL: [n; 0] ends as [0; 1 + … + n]. *)
Definition t_HL : triple T := @tri T Pn0 tprog Qtri.
Lemma v_HL : cvalid Forward Plain Over t_HL.
Proof.
  apply hl_valid_iff. intros s s' [n ->] Hc. apply triangle_run in Hc.
  exists n. destruct n; simpl in *; subst; reflexivity.
Qed.
Theorem stack_HL : derivable (rules (HL_t sinstr_sem)) t_HL.
Proof. apply derive_HL_t, v_HL. Qed.

(** IL: every [0; 1 + … + n] is reached, from [n; 0]. *)
Lemma v_IL : cvalid Forward Plain Under t_HL.
Proof.
  apply il_valid_iff. intros s' [n ->]. exists [n; 0].
  split; [exists n; reflexivity | apply triangle_run, run_n0].
Qed.
Theorem stack_IL : derivable (rules (IL_t sinstr_sem)) t_HL.
Proof. apply derive_IL_t, v_IL. Qed.

(** NC: to end at [0; 6], start at a two-element [n; a] with
    [a + 1 + … + n = 6]. *)
Definition P6 (s : stack) : Prop := exists n a, s = [n; a] /\ a + trin n = 6.
Definition t_NC : triple T := @tri T P6 tprog (fun s => s = [0; 6]).
Lemma v_NC : cvalid Backward Plain Over t_NC.
Proof.
  apply nc_valid_iff. intros s s' Hc ->. apply triangle_run in Hc. simpl.
  unfold P6. destruct s as [| [| k] [| a r]]; simpl in Hc;
    try discriminate; try contradiction.
  - inversion Hc; subst. exists 0, 6. auto.
  - inversion Hc. subst. exists (S k), a. split; [reflexivity |].
    simpl in *. lia.
Qed.
Theorem stack_NC : derivable (rules (NC_t sinstr_sem)) t_NC.
Proof. apply derive_NC_t, v_NC. Qed.

(** SIL: from [3; 0] the program can end at [0; 6]. *)
Definition t_SIL : triple T :=
  @tri T (fun s => s = [3; 0]) tprog (fun s => s = [0; 6]).
Lemma v_SIL : cvalid Backward Plain Under t_SIL.
Proof.
  apply sil_valid_iff. intros s Hs. simpl in Hs. subst. exists [0; 6].
  split; [apply triangle_run; reflexivity | reflexivity].
Qed.
Theorem stack_SIL : derivable (rules (SIL_t sinstr_sem)) t_SIL.
Proof. apply derive_SIL_t, v_SIL. Qed.

(** p̃ost ⊆: a final stack all of whose possible starts are two-element
    stacks is [0; a] or has a nonzero top (no start at all). *)
Definition t_PostDO : triple T :=
  @tri T (fun s => exists n a, s = [n; a]) tprog
       (fun s => (exists a, s = [0; a]) \/ (exists k r, s = S k :: r)).
Lemma v_PostDO : cvalid Forward Dual Over t_PostDO.
Proof.
  unfold t_PostDO, tri. simpl. unfold aimpl, dimg. simpl. intros s' H.
  destruct s' as [| [| k] r].
  - exfalso. destruct (H []) as [n [a Hs]]; [apply triangle_run; reflexivity |].
    discriminate.
  - left. destruct (H (0 :: r)) as [n [a Hs]];
      [apply triangle_run; reflexivity |].
    inversion Hs; subst. exists a. reflexivity.
  - right. exists k, r. reflexivity.
Qed.
Theorem stack_PostDO : derivable (rules (PostDO_t sinstr_sem)) t_PostDO.
Proof. apply derive_PostDO_t, v_PostDO. Qed.

(** p̃ost ⊇: Galois-equivalent to NC. *)
Lemma v_PostDU : cvalid Forward Dual Under t_NC.
Proof. apply galois_pre_dimg, v_NC. Qed.
Theorem stack_PostDU : derivable (rules (PostDU_t sinstr_sem)) t_NC.
Proof. apply derive_PostDU_t, v_PostDU. Qed.

(** p̃re ⊆: if every run is sure to end at [0; 6], the start was a
    suitable [n; a], or a stuck one-element stack. *)
Definition P6s (s : stack) : Prop := P6 s \/ exists k, s = [S k].
Definition t_PreDO : triple T := @tri T P6s tprog (fun s => s = [0; 6]).
Lemma v_PreDO : cvalid Backward Dual Over t_PreDO.
Proof.
  unfold t_PreDO, tri. simpl. unfold aimpl, wlp. simpl. intros s H.
  unfold P6s, P6. destruct s as [| [| k] [| a r]].
  - exfalso. specialize (H [] (proj2 (triangle_run [] []) eq_refl)).
    discriminate.
  - exfalso. specialize (H [0] (proj2 (triangle_run [0] [0]) eq_refl)).
    discriminate.
  - left. specialize (H (0 :: a :: r)
                  (proj2 (triangle_run (0 :: a :: r) _) eq_refl)).
    inversion H; subst. exists 0, 6. auto.
  - right. exists k. reflexivity.
  - left. specialize (H (0 :: (a + trin (S k)) :: r)
                  (proj2 (triangle_run (S k :: a :: r) _) eq_refl)).
    inversion H; subst. exists (S k), a. split; [reflexivity |].
    simpl in *. lia.
Qed.
Theorem stack_PreDO : derivable (rules (PreDO_t sinstr_sem)) t_PreDO.
Proof. apply derive_PreDO_t, v_PreDO. Qed.

(** p̃re ⊇: Galois-equivalent to HL. *)
Lemma v_PreDU : cvalid Backward Dual Under t_HL.
Proof. apply galois_post_wlp, v_HL. Qed.
Theorem stack_PreDU : derivable (rules (PreDU_t sinstr_sem)) t_HL.
Proof. apply derive_PreDU_t, v_PreDU. Qed.

(** ** Bottom face: the program always terminates *)

Definition SomeP (P : stack -> Prop) (bot : Prop) : assertion B :=
  fun o => match o with Some s => P s | None => bot end.

(** HL⊥ (total correctness): [n; 0] terminates, as [0; 1 + … + n]. *)
Definition b_HL : triple B :=
  @tri B (SomeP Pn0 False) tprog (SomeP Qtri False).
Lemma vb_HL : cvalid Forward Plain Over b_HL.
Proof.
  apply hl_valid_iff. intros [s|] [s'|] HP Hc; simpl in *; try contradiction.
  - destruct HP as [n ->]. apply triangle_run in Hc. exists n.
    destruct n; simpl in *; subst; reflexivity.
  - exact (triangle_no_div s Hc).
Qed.
Theorem stack_HL_bot : derivable (rules (HL_b sinstr_sem)) b_HL.
Proof. apply derive_HL_b, vb_HL. Qed.

(** IL⊥: every [0; 1 + … + n] is reached from [n; 0]. *)
Lemma vb_IL : cvalid Forward Plain Under b_HL.
Proof.
  apply il_valid_iff. intros [s'|] Hs'; simpl in Hs'; [| contradiction].
  destruct Hs' as [n ->]. exists (Some [n; 0]).
  split; [exists n; reflexivity | apply triangle_run, run_n0].
Qed.
Theorem stack_IL_bot : derivable (rules (IL_b sinstr_sem)) b_HL.
Proof. apply derive_IL_b, vb_IL. Qed.

(** NC⊥: only ⊥ itself leads to ⊥ (termination). *)
Definition b_NC : triple B :=
  @tri B (fun o => o = None) tprog (fun o => o = None).
Lemma vb_NC : cvalid Backward Plain Over b_NC.
Proof.
  apply nc_valid_iff. intros [s|] o' Hc Ho'; simpl in *; subst; auto.
  exfalso. exact (triangle_no_div s Hc).
Qed.
Theorem stack_NC_bot : derivable (rules (NC_b sinstr_sem)) b_NC.
Proof. apply derive_NC_b, vb_NC. Qed.

(** SIL⊥: from [3; 0] the program can end at [0; 6]. *)
Definition b_SIL : triple B :=
  @tri B (SomeP (fun s => s = [3; 0]) False) tprog
       (SomeP (fun s => s = [0; 6]) False).
Lemma vb_SIL : cvalid Backward Plain Under b_SIL.
Proof.
  apply sil_valid_iff. intros [s|] Hs; simpl in Hs; [| contradiction].
  subst. exists (Some [0; 6]).
  split; [apply triangle_run; reflexivity | reflexivity].
Qed.
Theorem stack_SIL_bot : derivable (rules (SIL_b sinstr_sem)) b_SIL.
Proof. apply derive_SIL_b, vb_SIL. Qed.

(** p̃ost ⊆ ⊥: an outcome whose only possible start is ⊥ is ⊥ itself or a
    stack with a nonzero top (no start at all). *)
Definition b_PostDO : triple B :=
  @tri B (fun o => o = None) tprog
       (SomeP (fun s => exists k r, s = S k :: r) True).
Lemma vb_PostDO : cvalid Forward Dual Over b_PostDO.
Proof.
  unfold b_PostDO, tri, SomeP. simpl. unfold aimpl, dimg. simpl.
  intros [s'|] H; [| exact I].
  destruct s' as [| [| k] r].
  - exfalso. specialize (H (Some []) (proj2 (triangle_run [] []) eq_refl)).
    discriminate.
  - exfalso. specialize (H (Some (0 :: r))).
    simpl in H. specialize (H (proj2 (triangle_run (0 :: r) (0 :: r)) eq_refl)).
    discriminate.
  - exists k, r. reflexivity.
Qed.
Theorem stack_PostDO_bot : derivable (rules (PostDO_b sinstr_sem)) b_PostDO.
Proof. apply derive_PostDO_b, vb_PostDO. Qed.

(** p̃ost ⊇ ⊥: Galois-equivalent to NC⊥. *)
Lemma vb_PostDU : cvalid Forward Dual Under b_NC.
Proof. apply galois_pre_dimg, vb_NC. Qed.
Theorem stack_PostDU_bot : derivable (rules (PostDU_b sinstr_sem)) b_NC.
Proof. apply derive_PostDU_b, vb_PostDU. Qed.

(** p̃re ⊆ ⊥: if every outcome is [0; 6], the start was suitable. *)
Definition b_PreDO : triple B :=
  @tri B (SomeP P6s False) tprog (SomeP (fun s => s = [0; 6]) False).
Lemma vb_PreDO : cvalid Backward Dual Over b_PreDO.
Proof.
  unfold b_PreDO, tri, SomeP. simpl. unfold aimpl, wlp. simpl.
  intros [s|] H.
  - apply (v_PreDO s). intros s' Hc. exact (H (Some s') Hc).
  - exact (H None I).
Qed.
Theorem stack_PreDO_bot : derivable (rules (PreDO_b sinstr_sem)) b_PreDO.
Proof. apply derive_PreDO_b, vb_PreDO. Qed.

(** p̃re ⊇ ⊥: Galois-equivalent to HL⊥. *)
Lemma vb_PreDU : cvalid Backward Dual Under b_HL.
Proof. apply galois_post_wlp, vb_HL. Qed.
Theorem stack_PreDU_bot : derivable (rules (PreDU_b sinstr_sem)) b_HL.
Proof. apply derive_PreDU_b, vb_PreDU. Qed.
