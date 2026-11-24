(** * The Imp example, proved with rules in each logic

    The triples of [ImpExample], all 16 nodes, proved by applying rules
    ([Core.Rules], [Core.RulesBot]) in the records obtained by
    transformers ([Examples.Common]). No reasoning about runs: each proof
    composes rules, and the side conditions are facts about states and
    updates.

    The loop body [(x := x - 1; y := y + 1) ⊕ skip] is handled by the
    choice rule. The assignment rules are used backward (HL, NC, SIL) or
    forward (IL). Only the IL proof, which must exhibit a predecessor whose
    run ends in exactly a given state, needs [functional_extensionality]
    (in [upd_same] and [upd_upd]). *)

From Stdlib Require Import String Arith Lia FunctionalExtensionality.
From LogicTransformers.Imp Require Import Syntax BigStep Lang.
From LogicTransformers.Logics Require Import Hoare.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Verified.
From LogicTransformers.Core Require Import
  Kernel KernelBot ImpCore Rules RulesBot.
From LogicTransformers.Examples Require Import Common ImpExample.
From LogicTransformers.Core Require Import TripleNotations.
Local Open Scope triple_scope.

Local Open Scope string_scope.
Local Notation X := "x".
Local Notation Y := "y".

Definition ax : iact := IAsgn X (AMinus (AVar X) (ANum 1)).
Definition ay : iact := IAsgn Y (APlus (AVar Y) (ANum 1)).
Definition ibody : kcom state iact := KChoice (KSeq (KAct ax) (KAct ay)) KSkip.

Lemma cprog_eq : cprog = kwhile (bassn guard) ibody.
Proof. reflexivity. Qed.

Notation P := (prov iact_sem) (only parsing).
Notation Pb := (provb iact_sem) (only parsing).

Lemma not_guard : forall s, ~ bassn guard s -> s X = 0.
Proof.
  intros s H. destruct (s X) eqn:E; [reflexivity |].
  exfalso. apply H. apply guard_true. lia.
Qed.

Lemma guard_pos : forall s, bassn guard s -> 0 < s X.
Proof. intros s H. apply guard_true, H. Qed.

Lemma upd_same : forall (s : state) x, update s x (s x) = s.
Proof.
  intros s x. apply functional_extensionality. intros z. unfold update.
  destruct (String.eqb_spec x z); subst; reflexivity.
Qed.

Lemma upd_upd : forall (s : state) x v w,
    update (update s x v) x w = update s x w.
Proof.
  intros s x v w. apply functional_extensionality. intros z. unfold update.
  destruct (String.eqb x z); reflexivity.
Qed.

(** Effects of the two assignments, read off the atom relation. *)
Lemma ax_eff : forall s s', iact_sem ax s s' ->
    s' X = s X - 1 /\ s' Y = s Y.
Proof. intros s s' H. simpl in H. subst. unfold update. simpl. auto. Qed.

Lemma ay_eff : forall s s', iact_sem ay s s' ->
    s' X = s X /\ s' Y = s Y + 1.
Proof. intros s s' H. simpl in H. subst. unfold update. simpl. auto. Qed.

(** ** Top face *)

Theorem imp_HL_rules : HLv iact_sem ⊢ {{ Sum10 }} cprog {{ Done10 }}.
Proof.
  rewrite cprog_eq.
  apply (hl_cons _ _ _ Sum10 _ (fun s => Sum10 s /\ ~ bassn guard s));
    [intros s H; exact H | apply hl_while |].
  - apply hl_choice.
    + apply (hl_seq _ _ _ (fun s => forall s', iact_sem ay s s' -> Sum10 s')).
      * apply (hl_cons _ _ _
                 (fun s => forall s1, iact_sem ax s s1 ->
                           forall s2, iact_sem ay s1 s2 -> Sum10 s2) _
                 (fun s => forall s', iact_sem ay s s' -> Sum10 s'));
          [| apply hl_act | intros s H; exact H].
        intros s [HS Hg] s1 H1 s2 H2. apply guard_pos in Hg.
        destruct (ax_eff _ _ H1) as [E1 F1].
        destruct (ay_eff _ _ H2) as [E2 F2].
        unfold Sum10 in *. lia.
      * apply hl_act.
    + apply (hl_cons _ _ _ Sum10 _ Sum10);
        [intros s [H _]; exact H | apply hl_skip | intros s H; exact H].
  - intros s [HS Hn]. apply not_guard in Hn. unfold Sum10, Done10 in *. lia.
Qed.

Definition Xil (n : nat) (s : state) : Prop :=
  n <= 3 /\ s X = 3 - n /\ s Y = 7 + n.

Theorem imp_IL_rules :
  ILv iact_sem ⊢ ⟦ fun s => s X = 3 /\ s Y = 7 ⟧ cprog ⟦ Done10 ⟧.
Proof.
  rewrite cprog_eq.
  apply (il_cons _ _ _ (Xil 0) _
           (fun s => exists n, Xil n s /\ ~ bassn guard s));
    [| apply il_while |].
  - intros s [_ [H1 H2]]. lia.
  - intros n. apply il_choice_l.
    set (Pn := fun s => Xil n s /\ bassn guard s).
    set (R := fun s1 => exists s, Pn s /\ iact_sem ax s s1).
    apply (il_cons _ _ _ Pn _ (fun s2 => exists s1, R s1 /\ iact_sem ay s1 s2));
      [intros s H; exact H | apply (il_seq _ _ _ R); apply il_act |].
    intros s' [Hn [Hx Hy]].
    set (s1 := update s' Y (s' Y - 1)).
    set (s0 := update s1 X (s1 X + 1)).
    assert (E1x : s1 X = s' X) by (unfold s1, update; reflexivity).
    assert (E1y : s1 Y = s' Y - 1) by (unfold s1; apply update_eq).
    assert (E0x : s0 X = s' X + 1) by (unfold s0; rewrite update_eq; lia).
    assert (E0y : s0 Y = s' Y - 1) by (unfold s0, update; simpl; exact E1y).
    exists s1. split.
    + exists s0. split.
      * unfold Pn, Xil. split; [repeat split; lia |].
        apply guard_true. lia.
      * cbn [iact_sem ax].
        assert (Hv : aeval s0 (AMinus (AVar X) (ANum 1)) = s1 X)
          by (cbn [aeval]; lia).
        rewrite Hv. unfold s0. rewrite upd_upd, upd_same. reflexivity.
    + cbn [iact_sem ay].
      assert (Hv : aeval s1 (APlus (AVar Y) (ANum 1)) = s' Y)
        by (cbn [aeval]; lia).
      rewrite Hv. unfold s1. rewrite upd_upd, upd_same. reflexivity.
  - intros s [Hx Hy]. exists 3. split; [unfold Xil; lia |].
    intros Hg. apply guard_pos in Hg. lia.
Qed.

Theorem imp_NC_rules : P (NCv iact_sem) Sum10 cprog Done10.
Proof.
  rewrite cprog_eq.
  apply (nc_cons _ _ _ Sum10 _ (fun s => Sum10 s /\ ~ bassn guard s));
    [intros s H; exact H | apply nc_while |].
  - apply nc_choice.
    + set (R := fun s1 => exists s2, iact_sem ay s1 s2 /\ Sum10 s2).
      apply (nc_seq _ _ _ R); [| apply nc_act].
      apply (nc_cons _ _ _
               (fun s => exists s1, iact_sem ax s s1 /\ R s1) _ R);
        [| apply nc_act | intros s H; exact H].
      intros s [s1 [H1 [s2 [H2 HS]]]] Hg. apply guard_pos in Hg.
      destruct (ax_eff _ _ H1) as [E1 F1]. destruct (ay_eff _ _ H2) as [E2 F2].
      unfold Sum10 in *. lia.
    + apply (nc_cons _ _ _ Sum10 _ Sum10);
        [intros s H _; exact H | apply nc_skip | intros s H; exact H].
  - intros s [Hx Hy]. unfold Sum10. split; [lia |].
    intros Hg. apply guard_pos in Hg. lia.
Qed.

(** SIL, with "n iterations to go" as the variant. *)
Definition Xs (Inv : state -> Prop) (n : nat) (s : state) : Prop :=
  Inv s /\ s X = n.

Lemma sil_body : forall (Inv : state -> Prop),
    (forall s, 0 < s X -> Inv s ->
       Inv (update (update s X (s X - 1)) Y
                   (update s X (s X - 1) Y + 1))) ->
    forall n, P (SILv iact_sem) (Xs Inv (S n)) ibody (Xs Inv n).
Proof.
  intros Inv HInv n. apply sil_choice_l.
  set (R := fun s1 => exists s2, iact_sem ay s1 s2 /\ Xs Inv n s2).
  apply (sil_seq _ _ _ R); [| apply sil_act].
  apply (sil_cons _ _ _ (fun s => exists s1, iact_sem ax s s1 /\ R s1) _ R);
    [| apply sil_act | intros s H; exact H].
  intros s [HI Hx].
  exists (update s X (s X - 1)). split; [reflexivity |].
  exists (update (update s X (s X - 1)) Y (update s X (s X - 1) Y + 1)).
  split; [reflexivity |]. split.
  - apply HInv; [lia | exact HI].
  - unfold update. simpl. lia.
Qed.

Lemma sum_pres : forall (Q : nat -> Prop) s, 0 < s X ->
    Q (s X + s Y) ->
    let s2 := update (update s X (s X - 1)) Y (update s X (s X - 1) Y + 1) in
    Q (s2 X + s2 Y).
Proof.
  intros Q s Hx H s2. unfold s2, update. simpl.
  replace (s X - 1 + (s Y + 1)) with (s X + s Y) by lia. exact H.
Qed.

Theorem imp_SIL_rules : P (SILv iact_sem) Sum10 cprog (fun s => s Y = 10).
Proof.
  rewrite cprog_eq.
  apply (sil_cons _ _ _ (fun s => exists n, Xs Sum10 n s) _ (Xs Sum10 0));
    [| apply sil_while |].
  - intros s H. exists (s X). split; [exact H | reflexivity].
  - apply sil_body. intros s Hx HS.
    exact (sum_pres (fun v => v = 10) s Hx HS).
  - intros n s [_ Hx]. apply guard_true. lia.
  - intros s [_ Hx] Hg. apply guard_pos in Hg. lia.
  - intros s [HS Hx]. unfold Sum10 in HS. lia.
Qed.

(** p̃ost ⊆ via IL on the complemented triple. *)
Theorem imp_PostDO_rules :
  derivable (rules (vl_logic (PostDOv iact_sem))) t_PostDO.
Proof.
  apply (vl_transport_compl (PostDOv iact_sem) (ILv iact_sem)).
  change (P (ILv iact_sem) (fun s => ~ Sum10 s) cprog
            (fun s => ~ (s X <> 0 \/ s Y = 10))).
  rewrite cprog_eq.
  set (Xc := fun n (s : state) =>
               match n with 0 => ~ Sum10 s | S _ => False end).
  apply (il_cons _ _ _ (Xc 0) _
           (fun s => exists n, Xc n s /\ ~ bassn guard s));
    [intros s H; exact H | apply il_while |].
  - intros n.
    apply (il_cons _ _ _ (fun s => Xc n s /\ bassn guard s) _ (fun _ => False));
      [intros s H; exact H | apply il_false | intros s H; exact H].
  - intros s H. exists 0. simpl. unfold Sum10. split.
    + intros HS. apply H. lia.
    + intros Hg. apply guard_pos in Hg. apply H. lia.
Qed.

Theorem imp_PostDU_rules :
  derivable (rules (vl_logic (PostDUv iact_sem))) t_HL.
Proof.
  apply (vl_transport_same (PostDUv iact_sem) (NCv iact_sem)
           (fun t => iff_sym (galois_pre_dimg t))).
  exact imp_NC_rules.
Qed.

(** p̃re ⊆ via SIL on the complemented triple. *)
Theorem imp_PreDO_rules :
  derivable (rules (vl_logic (PreDOv iact_sem))) t_SIL.
Proof.
  apply (vl_transport_compl (PreDOv iact_sem) (SILv iact_sem)).
  change (P (SILv iact_sem) (fun s => ~ Sum10 s) cprog (fun s => ~ s Y = 10)).
  rewrite cprog_eq.
  set (NS := fun s : state => ~ Sum10 s).
  apply (sil_cons _ _ _ (fun s => exists n, Xs NS n s) _ (Xs NS 0));
    [| apply sil_while |].
  - intros s H. exists (s X). split; [exact H | reflexivity].
  - apply sil_body. intros s Hx HS.
    exact (sum_pres (fun v => v <> 10) s Hx HS).
  - intros n s [_ Hx]. apply guard_true. lia.
  - intros s [_ Hx] Hg. apply guard_pos in Hg. lia.
  - intros s [HS Hx]. unfold NS, Sum10 in HS. lia.
Qed.

Theorem imp_PreDU_rules :
  derivable (rules (vl_logic (PreDUv iact_sem))) t_HL.
Proof.
  apply (vl_transport_same (PreDUv iact_sem) (HLv iact_sem)
           (fun t => iff_sym (galois_post_wlp t))).
  exact imp_HL_rules.
Qed.

(** ** Bottom face *)

Theorem imp_HL_bot_rules :
  HLbv iact_sem ⊢⊥ {{ SomeP Sum10 False }} cprog {{ SomeP Done10 True }}.
Proof.
  rewrite cprog_eq.
  set (Ib := fun o : option state =>
               match o with Some s => Sum10 s | None => True end).
  set (Rb := fun o : option state =>
               match o with
               | Some s => forall s', iact_sem ay s s' -> Ib (Some s')
               | None => Ib None end).
  apply (hlb_cons _ _ _ (som Sum10) _
           (fun o => match o with
                     | Some s => Sum10 s /\ ~ bassn guard s
                     | None => True end));
    [intros o H; exact H | apply hlb_while_inv |].
  - apply hlb_choice.
    + apply (hlb_seq _ _ _ Rb); [| apply hlb_act].
      apply (hlb_cons _ _ _
               (fun o => match o with
                         | Some s => forall s', iact_sem ax s s' -> Rb (Some s')
                         | None => Rb None end) _ Rb);
        [| apply hlb_act | intros o H; exact H].
      intros [s|] H; [| contradiction]. destruct H as [HS Hg].
      apply guard_pos in Hg. intros s1 H1 s2 H2.
      destruct (ax_eff _ _ H1) as [E1 F1]. destruct (ay_eff _ _ H2) as [E2 F2].
      simpl. unfold Sum10 in *. lia.
    + apply (hlb_cons _ _ _ Ib _ Ib);
        [intros [s|] H; [exact (proj1 H) | contradiction]
        | apply hlb_skip | intros o H; exact H].
  - intros [s|] H; simpl in *; [| exact I]. destruct H as [HS Hn].
    apply not_guard in Hn. unfold Sum10, Done10 in *. lia.
Qed.

Theorem imp_IL_bot_rules :
  ILbv iact_sem ⊢⊥ ⟦ SomeP (fun s => s X = 1) False ⟧ cprog
                   ⟦ fun o => o = None ⟧.
Proof.
  rewrite cprog_eq.
  set (s0 := update empty_state X 1).
  apply (ilb_cons _ _ _ (fun o => o = Some s0) _ (fun o => o = None));
    [intros o ->; simpl; apply update_eq | | intros o H; exact H].
  apply (ilb_diverge _ _ (fun s => 0 < s X));
    [unfold s0; rewrite update_eq; lia |].
  intros s Hs. split; [apply guard_true, Hs |]. exists s.
  split; [exact Hs |]. apply ilb_choice_r, ilb_skip.
Qed.

Theorem imp_NC_bot_rules : Pb (NCbv iact_sem) P_div cprog (fun o => o = None).
Proof.
  rewrite cprog_eq.
  apply (ncb_cons _ _ _
           (fun o => match o with Some s => bassn guard s | None => True end)
           _ (fun o => o = None));
    [| apply ncb_div_guard | intros o H; exact H].
  intros [s|] H; simpl in *; [apply guard_pos, H | exact I].
Qed.

Theorem imp_SIL_bot_rules :
  Pb (SILbv iact_sem) (SomeP (fun s => 0 < s X) False) cprog
     (fun o => o = None).
Proof.
  rewrite cprog_eq.
  apply (silb_cons _ _ _ (som (fun s => 0 < s X)) _ (fun o => o = None));
    [intros o H; exact H | apply silb_diverge | intros o H; exact H].
  - apply silb_choice_r, silb_skip.
  - intros s Hs. apply guard_true, Hs.
Qed.

Theorem imp_PostDO_bot_rules :
  derivable (rules (vl_logic (PostDObv iact_sem))) b_PostDO.
Proof.
  apply (vl_transport_compl (PostDObv iact_sem) (ILbv iact_sem)).
  change (Pb (ILbv iact_sem) (fun o => ~ P_div o) cprog (fun o => ~ P_div o)).
  rewrite cprog_eq.
  set (Xc := fun n (s : state) =>
               match n with 0 => ~ 0 < s X | S _ => False end).
  apply (ilb_cons _ _ _ (som (Xc 0)) _
           (som (fun s => exists n, Xc n s /\ ~ bassn guard s)));
    [| apply ilb_while |].
  - intros [s|] H; simpl in *; [exact H | contradiction].
  - intros n.
    apply (ilb_cons _ _ _ (som (fun s => Xc n s /\ bassn guard s)) _
             (fun _ => False));
      [intros o H; exact H | apply ilb_false | intros [s|] H; exact H].
  - intros [s|] H; simpl in *; [| exfalso; exact (H I)].
    exists 0. split; [exact H |]. intros Hg. apply H, guard_pos, Hg.
Qed.

Theorem imp_PostDU_bot_rules :
  derivable (rules (vl_logic (PostDUbv iact_sem))) b_NC.
Proof.
  apply (vl_transport_same (PostDUbv iact_sem) (NCbv iact_sem)
           (fun t => iff_sym (galois_pre_dimg t))).
  exact imp_NC_bot_rules.
Qed.

(** p̃re ⊆ ⊥ via SIL⊥ on the complemented triple, by cases: ⊥ stays ⊥;
    [0 < x] diverges; [x = 0] stops at once with [y ≠ 10]. *)
Theorem imp_PreDO_bot_rules :
  derivable (rules (vl_logic (PreDObv iact_sem))) b_PreDO.
Proof.
  apply (vl_transport_compl (PreDObv iact_sem) (SILbv iact_sem)).
  set (Q10 := SomeP (fun s : state => s Y = 10) False).
  change (Pb (SILbv iact_sem) (fun o => ~ SomeP Done10 False o) cprog
             (fun o => ~ Q10 o)).
  rewrite cprog_eq.
  set (Xc := fun n (s : state) =>
               match n with 0 => s X = 0 /\ s Y <> 10 | S _ => False end).
  apply (silb_cons _ _ _
           (fun o => (o = None \/ som (fun s => 0 < s X) o) \/
                     som (fun s => exists n, Xc n s) o)
           _ (fun o => ~ Q10 o)); [| | intros o H; exact H].
  - intros [s|] H; simpl in *.
    + destruct (Nat.eq_dec (s X) 0) as [Hx | Hx].
      * right. exists 0. split; [exact Hx |]. intros Hy. apply H.
        unfold Done10. auto.
      * left. right. lia.
    + left. left. reflexivity.
  - apply silb_disj; [apply silb_disj |].
    + apply (silb_cons _ _ _ (fun o => o = None) _ (fun o => o = None));
        [intros o H; exact H | apply silb_bot
        | intros o ->; unfold Q10; simpl; auto].
    + apply (silb_cons _ _ _ (som (fun s => 0 < s X)) _ (fun o => o = None));
        [intros o H; exact H | | intros o ->; unfold Q10; simpl; auto].
      apply silb_diverge; [apply silb_choice_r, silb_skip |].
      intros s Hs. apply guard_true, Hs.
    + apply (silb_cons _ _ _ (som (fun s => exists n, Xc n s)) _ (som (Xc 0)));
        [intros o H; exact H | apply silb_while |].
      * intros n.
        apply silb_cons with (P' := fun _ => False) (Q' := som (Xc n));
          [intros [s|] H; exact H | apply silb_false | intros o H; exact H].
      * intros n s [].
      * intros s [Hx _] Hg. apply guard_pos in Hg. lia.
      * intros [s|] H; simpl in *; [unfold Q10, SomeP; exact (proj2 H)
                                   | contradiction].
Qed.

Theorem imp_PreDU_bot_rules :
  derivable (rules (vl_logic (PreDUbv iact_sem))) b_HL.
Proof.
  apply (vl_transport_same (PreDUbv iact_sem) (HLbv iact_sem)
           (fun t => iff_sym (galois_post_wlp t))).
  exact imp_HL_bot_rules.
Qed.
