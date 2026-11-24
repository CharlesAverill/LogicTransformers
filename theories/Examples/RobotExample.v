(** * Example: a robot on a grid (a language defined directly in the core)

    States are positions [(x, y)]. Atoms move the robot one step east or
    north. There is no separate source syntax: the language is the core
    instantiated with these atoms, and [kwhile] is its loop.

    The program wanders until it reaches column 5, choosing east or north
    at each step:

<<
      wander := while x < 5 do (east ⊕ north)
>>

    It is nondeterministic and may run forever (always choosing north).
    Its behaviour, characterized once:

    - [wander_run]: it ends in [s'] from [s] iff [x ≥ 5] and [s' = s], or
      [x < 5], [x' = 5] and [y ≤ y'];
    - [wander_div]: it can diverge from [s] iff [x < 5].

    Every node of the cube then gets a triple, proved valid from these two
    facts and derived in that node's generated logic by completeness
    (see [Examples.Common] for why). [robot_HL_by_hand] builds one
    derivation explicitly instead. *)

From Stdlib Require Import Arith Lia.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube CubeLogic Verified.
From LogicTransformers.Transformers Require Import Invert.
From LogicTransformers.Core Require Import
  Kernel KernelBot Generate GenerateBot CoreCousot VCore.
From LogicTransformers.Examples Require Import Common.

Definition pos : Type := (nat * nat)%type.

Inductive move := East | North.

Definition move_sem (m : move) (s s' : pos) : Prop :=
  match m with
  | East => s' = (S (fst s), snd s)
  | North => s' = (fst s, S (snd s))
  end.

Definition below5 (s : pos) : Prop := fst s < 5.
Definition step : kcom pos move := KChoice (KAct East) (KAct North).
Definition wander : kcom pos move := kwhile below5 step.
Definition body : kcom pos move := KSeq (KAssume below5) step.

Notation kevR := (kev move_sem).
Notation T := (KLang move_sem).
Notation B := (KLangB move_sem).

(** ** Characterizing the program *)

Lemma body_inv : forall s s', kevR body s s' ->
    fst s < 5 /\ fst s' <= 5 /\ fst s <= fst s' /\ snd s <= snd s'.
Proof.
  intros s s' H. inversion H; subst.
  match goal with H' : kev _ (KAssume _) _ _ |- _ => inversion H'; subst end.
  match goal with H' : kev _ step _ _ |- _ => inversion H'; subst end;
  match goal with H' : kev _ (KAct _) _ _ |- _ => inversion H'; subst end;
  simpl in *; subst; unfold below5 in *; simpl; lia.
Qed.

Lemma star_inv : forall s s', kevR (KStar body) s s' ->
    s' = s \/ (fst s < 5 /\ fst s' <= 5 /\ snd s <= snd s').
Proof.
  intros s s' H. remember (KStar body) as k eqn:Ek.
  induction H; inversion Ek; subst; [left; reflexivity |].
  apply body_inv in H. right.
  destruct (IHkev2 eq_refl) as [-> | Hr]; lia.
Qed.

Lemma north_steps : forall k x y, x < 5 ->
    kevR (KStar body) (x, y) (x, y + k).
Proof.
  induction k as [| k IH]; intros x y Hx.
  - rewrite Nat.add_0_r. apply KE_StarRefl.
  - eapply KE_StarStep.
    + eapply KE_Seq; [apply KE_Assume; exact Hx |].
      apply KE_ChoiceR, KE_Act. reflexivity.
    + replace (y + S k) with (S y + k) by lia. apply IH, Hx.
Qed.

Lemma east_steps : forall k x y, x + k <= 5 ->
    kevR (KStar body) (x, y) (x + k, y).
Proof.
  induction k as [| k IH]; intros x y Hx.
  - rewrite Nat.add_0_r. apply KE_StarRefl.
  - eapply KE_StarStep.
    + eapply KE_Seq; [apply KE_Assume; unfold below5; simpl; lia |].
      apply KE_ChoiceL, KE_Act. reflexivity.
    + replace (x + S k) with (S x + k) by lia. apply IH. lia.
Qed.

Definition Rw (s s' : pos) : Prop :=
  (5 <= fst s /\ s' = s) \/ (fst s < 5 /\ fst s' = 5 /\ snd s <= snd s').

Lemma wander_run : forall s s', kevR wander s s' <-> Rw s s'.
Proof.
  intros s s'. unfold wander. rewrite kwhile_run_iff. split.
  - intros [H Hn]. unfold below5 in Hn.
    destruct (star_inv s s' H) as [-> | Hr];
      [left; split; [lia | reflexivity] | right; lia].
  - intros [[Hx ->] | [Hx [Hx' Hy]]].
    + split; [apply KE_StarRefl | unfold below5; lia].
    + split; [| unfold below5; lia].
      destruct s as [x y], s' as [x' y']. simpl in *. subst.
      apply (kev_star_trans _ _ _ (x, y')).
      * pose proof (north_steps (y' - y) x y Hx) as Hn.
        replace (y + (y' - y)) with y' in Hn by lia. exact Hn.
      * assert (He : x + (5 - x) <= 5) by lia.
        pose proof (east_steps (5 - x) x y' He) as Hn.
        replace (x + (5 - x)) with 5 in Hn by lia. exact Hn.
Qed.

Lemma wander_div : forall s, kdiv move_sem wander s <-> fst s < 5.
Proof.
  intros s. split.
  - intros H. exact (kwhile_div_guard move_sem below5 step s H).
  - apply (kwhile_div_intro move_sem below5). intros s0 H. split; [exact H |].
    exists (fst s0, S (snd s0)).
    split; [apply KE_ChoiceR, KE_Act; reflexivity |].
    exact H.
Qed.

(** ** Top face (partial correctness) *)

Definition tri {L : Language} (P : assertion L) c (Q : assertion L) :=
  mkTriple P c Q.

(** HL: started at or left of column 5, it can only stop at column 5. *)
Definition t_HL : triple T :=
  @tri T (fun s => fst s <= 5) wander (fun s => fst s = 5).
Lemma v_HL : cvalid Forward Plain Over t_HL.
Proof.
  apply hl_valid_iff. intros s s' HP Hc. apply wander_run in Hc. simpl in *.
  destruct Hc as [[H1 ->] | [H1 [H2 H3]]]; lia.
Qed.
Theorem robot_HL : derivable (rules (HL_t move_sem)) t_HL.
Proof. apply derive_HL_t, v_HL. Qed.

(** IL: every position in column 5 is reachable from the origin. *)
Definition t_IL : triple T :=
  @tri T (fun s => s = (0, 0)) wander (fun s => fst s = 5).
Lemma v_IL : cvalid Forward Plain Under t_IL.
Proof.
  apply il_valid_iff. intros s' Hs'. simpl in *. exists (0, 0).
  split; [reflexivity | apply wander_run; right; simpl; lia].
Qed.
Theorem robot_IL : derivable (rules (IL_t move_sem)) t_IL.
Proof. apply derive_IL_t, v_IL. Qed.

(** NC: to stop at (5, 3) you must start left of column 5 and at most at
    height 3, or already be at (5, 3). *)
Definition P_NC (s : pos) : Prop := (fst s < 5 /\ snd s <= 3) \/ s = (5, 3).
Definition t_NC : triple T := @tri T P_NC wander (fun s => s = (5, 3)).
Lemma v_NC : cvalid Backward Plain Over t_NC.
Proof.
  apply nc_valid_iff. intros s s' Hc ->. simpl. apply wander_run in Hc.
  unfold P_NC. destruct Hc as [[_ ->] | [H1 [_ H3]]]; [right; auto | left].
  simpl in *. lia.
Qed.
Theorem robot_NC : derivable (rules (NC_t move_sem)) t_NC.
Proof. apply derive_NC_t, v_NC. Qed.

(** SIL: from anywhere left of column 5 and at most height 100, the robot
    can stop at (5, 100). *)
Definition t_SIL : triple T :=
  @tri T (fun s => fst s < 5 /\ snd s <= 100) wander (fun s => s = (5, 100)).
Lemma v_SIL : cvalid Backward Plain Under t_SIL.
Proof.
  apply sil_valid_iff. intros s HP. simpl in *. exists (5, 100).
  split; [apply wander_run; right; simpl; lia | reflexivity].
Qed.
Theorem robot_SIL : derivable (rules (SIL_t move_sem)) t_SIL.
Proof. apply derive_SIL_t, v_SIL. Qed.

(** p̃ost ⊆: a final position all of whose possible starts were at height
    at most 3 is left of column 5 (no start at all) or at height ≤ 3. *)
Definition t_PostDO : triple T :=
  @tri T (fun s => snd s <= 3) wander (fun s => fst s < 5 \/ snd s <= 3).
Lemma v_PostDO : cvalid Forward Dual Over t_PostDO.
Proof.
  unfold t_PostDO, tri. simpl. unfold aimpl, dimg. simpl. intros s' H.
  destruct (lt_dec (fst s') 5) as [Hl | Hl]; [left; exact Hl | right].
  apply H, wander_run. left. split; [lia | reflexivity].
Qed.
Theorem robot_PostDO : derivable (rules (PostDO_t move_sem)) t_PostDO.
Proof. apply derive_PostDO_t, v_PostDO. Qed.

(** p̃ost ⊇: Galois-equivalent to NC, so it is the same triple. *)
Lemma v_PostDU : cvalid Forward Dual Under t_NC.
Proof. apply galois_pre_dimg, v_NC. Qed.
Theorem robot_PostDU : derivable (rules (PostDU_t move_sem)) t_NC.
Proof. apply derive_PostDU_t, v_PostDU. Qed.

(** p̃re ⊆: if every run is sure to stop in column 5, the start was at or
    left of column 5. *)
Definition t_PreDO : triple T :=
  @tri T (fun s => fst s <= 5) wander (fun s => fst s = 5).
Lemma v_PreDO : cvalid Backward Dual Over t_PreDO.
Proof.
  unfold t_PreDO, tri. simpl. unfold aimpl, wlp. simpl. intros s H.
  destruct (le_dec (fst s) 5) as [Hl | Hl]; [exact Hl | exfalso].
  assert (Hr : Rw s s) by (left; split; [lia | reflexivity]).
  apply wander_run, H in Hr. lia.
Qed.
Theorem robot_PreDO : derivable (rules (PreDO_t move_sem)) t_PreDO.
Proof. apply derive_PreDO_t, v_PreDO. Qed.

(** p̃re ⊇: Galois-equivalent to HL, so it is the same triple. *)
Lemma v_PreDU : cvalid Backward Dual Under t_HL.
Proof. apply galois_post_wlp, v_HL. Qed.
Theorem robot_PreDU : derivable (rules (PreDU_t move_sem)) t_HL.
Proof. apply derive_PreDU_t, v_PreDU. Qed.

(** ** Bottom face (⊥ = [None] is nontermination) *)

Definition SomeP (P : pos -> Prop) (bot : Prop) : assertion B :=
  fun o => match o with Some s => P s | None => bot end.

(** HL⊥: from at or left of column 5, the robot either runs forever or
    stops in column 5. *)
Definition b_HL : triple B :=
  @tri B (SomeP (fun s => fst s <= 5) False) wander
       (SomeP (fun s => fst s = 5) True).
Lemma vb_HL : cvalid Forward Plain Over b_HL.
Proof.
  apply hl_valid_iff. intros [s|] [s'|] HP Hc; simpl in *; try contradiction;
    auto.
  apply wander_run in Hc. destruct Hc as [[H1 ->] | [H1 [H2 H3]]]; lia.
Qed.
Theorem robot_HL_bot : derivable (rules (HL_b move_sem)) b_HL.
Proof. apply derive_HL_b, vb_HL. Qed.

(** IL⊥: nontermination is reachable from the origin. *)
Definition b_IL : triple B :=
  @tri B (fun o => o = Some (0, 0)) wander (fun o => o = None).
Lemma vb_IL : cvalid Forward Plain Under b_IL.
Proof.
  apply il_valid_iff. intros o' Ho'. simpl in Ho'. subst. exists (Some (0, 0)).
  split; [reflexivity | apply wander_div; simpl; lia].
Qed.
Theorem robot_IL_bot : derivable (rules (IL_b move_sem)) b_IL.
Proof. apply derive_IL_b, vb_IL. Qed.

(** NC⊥: only starts left of column 5 (or ⊥ itself) can lead to ⊥. *)
Definition P_NCb : assertion B := SomeP (fun s => fst s < 5) True.
Definition b_NC : triple B := @tri B P_NCb wander (fun o => o = None).
Lemma vb_NC : cvalid Backward Plain Over b_NC.
Proof.
  apply nc_valid_iff. intros [s|] o' Hc Ho'; simpl in *; subst; [| exact I].
  apply wander_div, Hc.
Qed.
Theorem robot_NC_bot : derivable (rules (NC_b move_sem)) b_NC.
Proof. apply derive_NC_b, vb_NC. Qed.

(** SIL⊥: every start left of column 5 can run forever. *)
Definition b_SIL : triple B :=
  @tri B (SomeP (fun s => fst s < 5) False) wander (fun o => o = None).
Lemma vb_SIL : cvalid Backward Plain Under b_SIL.
Proof.
  apply sil_valid_iff. intros [s|] HP; simpl in HP; [| contradiction].
  exists None. split; [apply wander_div, HP | reflexivity].
Qed.
Theorem robot_SIL_bot : derivable (rules (SIL_b move_sem)) b_SIL.
Proof. apply derive_SIL_b, vb_SIL. Qed.

(** p̃ost ⊆ ⊥: an outcome all of whose possible starts lie left of
    column 5 (or are ⊥) is ⊥ or a position with no start at all. *)
Definition b_PostDO : triple B := @tri B P_NCb wander P_NCb.
Lemma vb_PostDO : cvalid Forward Dual Over b_PostDO.
Proof.
  unfold b_PostDO, tri, P_NCb, SomeP. simpl. unfold aimpl, dimg. simpl.
  intros [s'|] H; simpl; [| exact I].
  destruct (lt_dec (fst s') 5) as [Hl | Hl]; [exact Hl | exfalso].
  apply Hl, (H (Some s')). simpl. apply wander_run. left. split; [lia | auto].
Qed.
Theorem robot_PostDO_bot : derivable (rules (PostDO_b move_sem)) b_PostDO.
Proof. apply derive_PostDO_b, vb_PostDO. Qed.

(** p̃ost ⊇ ⊥: Galois-equivalent to NC⊥. *)
Lemma vb_PostDU : cvalid Forward Dual Under b_NC.
Proof. apply galois_pre_dimg, vb_NC. Qed.
Theorem robot_PostDU_bot : derivable (rules (PostDU_b move_sem)) b_NC.
Proof. apply derive_PostDU_b, vb_PostDU. Qed.

(** p̃re ⊆ ⊥: if every outcome is a stop in column 5 (in particular, no
    divergence), the robot started in column 5. *)
Definition b_PreDO : triple B :=
  @tri B (SomeP (fun s => fst s = 5) False) wander
      (SomeP (fun s => fst s = 5) False).
Lemma vb_PreDO : cvalid Backward Dual Over b_PreDO.
Proof.
  unfold b_PreDO, tri, SomeP. simpl. unfold aimpl, wlp. simpl.
  intros [s|] H; simpl.
  - destruct (lt_dec (fst s) 5) as [Hl | Hl].
    + exfalso. apply (H None). simpl. apply wander_div, Hl.
    + apply (H (Some s)). simpl. apply wander_run. left. split; [lia | auto].
  - apply (H None). exact I.
Qed.
Theorem robot_PreDO_bot : derivable (rules (PreDO_b move_sem)) b_PreDO.
Proof. apply derive_PreDO_b, vb_PreDO. Qed.

(** p̃re ⊇ ⊥: Galois-equivalent to HL⊥. *)
Lemma vb_PreDU : cvalid Backward Dual Under b_HL.
Proof. apply galois_post_wlp, vb_HL. Qed.
Theorem robot_PreDU_bot : derivable (rules (PreDU_b move_sem)) b_HL.
Proof. apply derive_PreDU_b, vb_PreDU. Qed.

(** ** A derivation built by hand

    The same HL triple as [robot_HL], derived directly from the generated
    rules and HL's consequence rule. The star rule is used with a
    constant family [X n = I], i.e. an invariant. Each body step is
    derived exactly (assume, then a choice of two atoms) and then weakened
    to [I]; the loop exit is weakened to the post. This is what the
    textbook invariant rule packages up. *)

Definition I_inv : assertion T := fun s => fst s <= 5.

Theorem robot_HL_by_hand : derivable (rules (HL_t move_sem)) t_HL.
Proof.
  set (Ib := fun s : pos => I_inv s /\ below5 s).
  set (QE := sp_rel move_sem move_sem East Ib).
  set (QN := sp_rel move_sem move_sem North Ib).
  assert (Dbody : derivable (rules (HL_t move_sem))
                            (mkTriple I_inv body I_inv)).
  { apply (hand_cons move_sem I_inv I_inv I_inv (fun s => QE s \/ QN s)).
    - apply (hand_gen move_sem _ _ _
               (F_Seq move_sem move_sem I_inv Ib _ (KAssume below5) step)).
      intros t [-> | ->].
      + apply (hand_gen move_sem _ _ _
                 (F_Assume move_sem move_sem I_inv below5)).
        intros t [].
      + apply (hand_gen move_sem _ _ _
                 (F_Choice move_sem move_sem Ib QE QN
                    (KAct East) (KAct North))).
        intros t [-> | ->];
          [apply (hand_gen move_sem _ _ _ (F_Act move_sem move_sem Ib East))
          | apply (hand_gen move_sem _ _ _ (F_Act move_sem move_sem Ib North))];
          intros t [].
    - intros s H. exact H.
    - intros s [[s0 [[H0 Hb] Hm]] | [s0 [[H0 Hb] Hm]]]; simpl in Hm; subst;
        unfold I_inv, below5 in *; simpl; lia. }
  apply (hand_cons move_sem _ I_inv _
           (fun s => (exists n : nat, I_inv s) /\ ~ below5 s)).
  - apply (hand_gen move_sem _ _ _
             (F_Seq move_sem move_sem I_inv (fun s => exists n : nat, I_inv s)
                _ (KStar body) (KAssume (fun s => ~ below5 s)))).
    intros t [-> | ->].
    + apply (hand_gen move_sem _ _ _
               (F_Star move_sem move_sem (fun _ => I_inv) body)).
      intros t [n ->]. exact Dbody.
    + apply (hand_gen move_sem _ _ _
               (F_Assume move_sem move_sem _ (fun s => ~ below5 s))).
      intros t [].
  - intros s H. exact H.
  - intros s [[_ HI] Hnb]. unfold I_inv, below5 in *. lia.
Qed.

(** ** Applying transformers to records

    Every logic above was pulled from a record. Here the chaining is
    explicit: start from a record, apply transformers, and read the
    results. *)

(** IL record ↦ SIL record (regenerated from the atoms' relation read off
    the IL record's derivations). *)
Definition robot_SIL_rec : VLogic T Backward Plain Under :=
  vto move_sem (ILv move_sem) Backward Plain Under.

Theorem robot_SIL_from_record :
  derivable (rules (vl_logic robot_SIL_rec)) t_SIL.
Proof. apply vl_derive, v_SIL. Qed.

(** Its soundness, pulled from the same record. *)
Theorem robot_SIL_record_sound : forall t,
    derivable (rules (vl_logic robot_SIL_rec)) t ->
    cvalid Backward Plain Under t.
Proof. apply vl_valid_of. Qed.

(** Top-face IL record ↦ bottom-face HL⊥ record. *)
Definition robot_HLb_rec : VLogic B Forward Plain Over :=
  vto_bot move_sem (ILv move_sem) Forward Plain Over.

Theorem robot_HLb_from_record :
  derivable (rules (vl_logic robot_HLb_rec)) b_HL.
Proof. apply vl_derive, vb_HL. Qed.

(** HL record ↦ NC record for the *inverse* robot language (the robot run
    backwards). The HL triple, swapped, is derivable there. *)
Definition robot_inv_rec : VLogic (inv T) Backward Plain Over :=
  vinvert (HLv move_sem).

Theorem robot_inverse_NC :
  derivable (rules (vl_logic robot_inv_rec)) (swap t_HL).
Proof.
  apply vl_derive. apply (proj1 (swap_cvalid Forward Plain Over t_HL)), v_HL.
Qed.
