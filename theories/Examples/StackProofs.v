(** * The stack example, proved with rules in each logic

    The triples of [StackExample], all 16 nodes, proved by applying rules
    ([Core.Rules], [Core.RulesBot]) in the records obtained by
    transformers. The loop [loop (acc; dec)] is handled by each node's
    while rule:

    - HL: invariant "[n; a] with [a + tri n] a triangular number";
    - IL: variant "after [k] iterations: [m; tri (m+k) - tri m]";
    - NC: backward invariant "[n; a] with [a + tri n = 6]";
    - SIL: descending variant "[k; 6 - tri k]";
    - HL⊥: total correctness, with the top of the stack as a
      well-founded variant;
    - the [Dual] nodes and NC⊥ by transport.

    No axioms are needed for the stack proofs beyond those of the records
    themselves. *)

From Stdlib Require Import Arith Lia List Wf_nat.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Verified.
From LogicTransformers.Core Require Import Kernel KernelBot Rules RulesBot.
From LogicTransformers.Examples Require Import Common StackExample.
From LogicTransformers.Core Require Import TripleNotations.
Local Open Scope triple_scope.
Import ListNotations.

Lemma tprog_eq : tprog = kwhile nz tbody.
Proof. reflexivity. Qed.

Notation P := (prov sinstr_sem) (only parsing).
Notation Pb := (provb sinstr_sem) (only parsing).

Lemma trin_mono : forall a b, a <= b -> trin a <= trin b.
Proof.
  intros a b H. induction H; [lia | simpl; lia].
Qed.

Definition top (s : stack) : nat := match s with n :: _ => n | [] => 0 end.

(** HL invariant. *)
Definition Inv (s : stack) : Prop :=
  exists n a m, s = [n; a] /\ a + trin n = trin m.

Lemma inv_step : forall s s1 s', Inv s -> nz s ->
    sinstr_sem IAcc s s1 -> sinstr_sem IDec s1 s' ->
    Inv s' /\ top s' < top s.
Proof.
  intros s s1 s' [n [a [m [-> E]]]] Hnz H1 H2. simpl in H1. subst.
  simpl in H2. subst. destruct n as [| k]; [simpl in Hnz; lia |].
  split; [| simpl; lia]. exists k, (a + S k), m. split; [reflexivity |].
  simpl in E. lia.
Qed.

(** ** Top face *)

Theorem stack_HL_rules : HLv sinstr_sem ⊢ {{ Pn0 }} tprog {{ Qtri }}.
Proof.
  rewrite tprog_eq.
  apply (hl_cons _ _ _ Inv _ (fun s => Inv s /\ ~ nz s));
    [| apply hl_while |].
  - intros s [n ->]. exists n, 0, n. split; reflexivity.
  - apply (hl_seq _ _ _ (fun s => forall s', sinstr_sem IDec s s' -> Inv s'));
      [| apply hl_act].
    apply (hl_cons _ _ _
             (fun s => forall s1, sinstr_sem IAcc s s1 ->
                       forall s', sinstr_sem IDec s1 s' -> Inv s') _
             (fun s => forall s', sinstr_sem IDec s s' -> Inv s'));
      [| apply hl_act | intros s H; exact H].
    intros s [HI Hnz] s1 H1 s' H2.
    exact (proj1 (inv_step s s1 s' HI Hnz H1 H2)).
  - intros s [[n [a [m [-> E]]]] Hn]. simpl in Hn.
    assert (n = 0) by lia. subst. exists m. simpl in E. f_equal. f_equal. lia.
Qed.

Definition Xil (k : nat) (s : stack) : Prop :=
  exists m, s = [m; trin (m + k) - trin m].

Lemma il_pred : forall k s', Xil (S k) s' ->
    exists s1, (exists s, (Xil k s /\ nz s) /\ sinstr_sem IAcc s s1) /\
               sinstr_sem IDec s1 s'.
Proof.
  intros k s' [m ->].
  set (a := trin (S m + k) - trin (S m)).
  exists [S m; a + S m]. split.
  - exists [S m; a]. split; [split; [exists (S m); reflexivity | simpl; lia] |].
    reflexivity.
  - simpl. f_equal. f_equal. unfold a.
    pose proof (trin_mono (S m) (S m + k) ltac:(lia)).
    replace (m + S k) with (S m + k) by lia.
    assert (E : trin (S m) = S m + trin m) by reflexivity.
    rewrite E in *. lia.
Qed.

Theorem stack_IL_rules : ILv sinstr_sem ⊢ ⟦ Pn0 ⟧ tprog ⟦ Qtri ⟧.
Proof.
  rewrite tprog_eq.
  apply (il_cons _ _ _ (Xil 0) _ (fun s => exists k, Xil k s /\ ~ nz s));
    [| apply il_while |].
  - intros s [m ->]. exists m. rewrite Nat.add_0_r, Nat.sub_diag. reflexivity.
  - intros k.
    set (Pk := fun s => Xil k s /\ nz s).
    set (R := fun s1 => exists s, Pk s /\ sinstr_sem IAcc s s1).
    apply (il_cons _ _ _ Pk _
             (fun s2 => exists s1, R s1 /\ sinstr_sem IDec s1 s2));
      [intros s H; exact H | apply (il_seq _ _ _ R); apply il_act |].
    intros s' H. exact (il_pred k s' H).
  - intros s [n ->]. exists n. split; [| simpl; lia].
    exists 0. simpl. f_equal. f_equal. lia.
Qed.

Theorem stack_NC_rules : P (NCv sinstr_sem) P6 tprog (fun s => s = [0; 6]).
Proof.
  rewrite tprog_eq.
  apply (nc_cons _ _ _ P6 _ (fun s => P6 s /\ ~ nz s));
    [intros s H; exact H | apply nc_while |].
  - set (R := fun s1 => exists s', sinstr_sem IDec s1 s' /\ P6 s').
    apply (nc_seq _ _ _ R); [| apply nc_act].
    apply (nc_cons _ _ _
             (fun s => exists s1, sinstr_sem IAcc s s1 /\ R s1) _ R);
      [| apply nc_act | intros s H; exact H].
    intros s [s1 [H1 [s' [H2 [m [b [Hs' Hb]]]]]]] Hnz.
    destruct s as [| n [| a r]]; simpl in H1; try contradiction. subst.
    simpl in H2. subst.
    match goal with E : _ :: _ = _ :: _ |- _ => inversion E; subst end.
    destruct n as [| k]; [simpl in Hnz; lia |].
    exists (S k), a. split; [reflexivity | simpl in *; lia].
  - intros s ->. split; [exists 0, 6; auto | simpl; lia].
Qed.

Definition Xsil (k : nat) (s : stack) : Prop := k <= 3 /\ s = [k; 6 - trin k].

Theorem stack_SIL_rules :
  P (SILv sinstr_sem) (fun s => s = [3; 0]) tprog (fun s => s = [0; 6]).
Proof.
  rewrite tprog_eq.
  apply (sil_cons _ _ _ (fun s => exists k, Xsil k s) _ (Xsil 0));
    [| apply sil_while |].
  - intros s ->. exists 3. split; [lia | reflexivity].
  - intros k.
    set (R := fun s1 => exists s', sinstr_sem IDec s1 s' /\ Xsil k s').
    apply (sil_seq _ _ _ R); [| apply sil_act].
    apply (sil_cons _ _ _
             (fun s => exists s1, sinstr_sem IAcc s s1 /\ R s1) _ R);
      [| apply sil_act | intros s H; exact H].
    intros s [Hk ->].
    exists [S k; 6 - trin (S k) + S k]. split; [reflexivity |].
    exists [k; 6 - trin (S k) + S k]. split; [reflexivity |].
    split; [lia |].
    destruct k as [| [| [| k]]]; simpl in *; try reflexivity; lia.
  - intros k s [_ ->]. simpl. lia.
  - intros s [_ ->]. simpl. lia.
  - intros s [_ ->]. reflexivity.
Qed.

(** p̃ost ⊆ via IL on the complemented triple. *)
Theorem stack_PostDO_rules :
  derivable (rules (vl_logic (PostDOv sinstr_sem))) t_PostDO.
Proof.
  apply (vl_transport_compl (PostDOv sinstr_sem) (ILv sinstr_sem)).
  set (Two := fun s : stack => exists n a, s = [n; a]).
  set (Ok := fun s : stack => (exists a, s = [0; a]) \/
                              (exists k r, s = S k :: r)).
  change (P (ILv sinstr_sem) (fun s => ~ Two s) tprog (fun s => ~ Ok s)).
  rewrite tprog_eq.
  set (X := fun n (s : stack) =>
              match n with 0 => ~ Two s | S _ => False end).
  apply (il_cons _ _ _ (X 0) _ (fun s => exists n, X n s /\ ~ nz s));
    [intros s H; exact H | apply il_while |].
  - intros n.
    apply (il_cons _ _ _ (fun s => X n s /\ nz s) _ (fun _ => False));
      [intros s H; exact H | apply il_false | intros s H; exact H].
  - intros s H. exists 0. simpl. unfold Ok, Two in *.
    destruct s as [| [| k] r].
    + split; [intros [n [a E]]; discriminate | simpl; auto].
    + split; [| simpl; lia].
      intros [n [a E]]. inversion E; subst. apply H. left. exists a. auto.
    + exfalso. apply H. right. exists k, r. auto.
Qed.

Theorem stack_PostDU_rules :
  derivable (rules (vl_logic (PostDUv sinstr_sem))) t_NC.
Proof.
  apply (vl_transport_same (PostDUv sinstr_sem) (NCv sinstr_sem)
           (fun t => iff_sym (galois_pre_dimg t))).
  exact stack_NC_rules.
Qed.

(** p̃re ⊆ via SIL on the complemented triple. *)
Definition shape_iters (k : nat) (s : stack) : Prop :=
  match s with n :: _ :: _ => n = k | _ => k = 0 end.

Definition Xpre (k : nat) (s : stack) : Prop := ~ P6s s /\ shape_iters k s.

Lemma pre_body : forall k,
    P (SILv sinstr_sem) (Xpre (S k)) tbody (Xpre k).
Proof.
  intros k.
  set (R := fun s1 => exists s', sinstr_sem IDec s1 s' /\ Xpre k s').
  apply (sil_seq _ _ _ R); [| apply sil_act].
  apply (sil_cons _ _ _ (fun s => exists s1, sinstr_sem IAcc s s1 /\ R s1) _ R);
    [| apply sil_act | intros s H; exact H].
  intros s [Hn Hsh]. destruct s as [| n [| a r]]; simpl in Hsh; try lia.
  subst n. exists (S k :: (a + S k) :: r). split; [reflexivity |].
  exists (k :: (a + S k) :: r). split; [reflexivity |]. split; [| reflexivity].
  intros [[m [b [E Hb]]] | [j E]]; [| discriminate].
  injection E as Em Eb Er. subst m b r. apply Hn. left. exists (S k), a.
  split; [reflexivity | simpl in *; lia].
Qed.

Theorem stack_PreDO_rules :
  derivable (rules (vl_logic (PreDOv sinstr_sem))) t_PreDO.
Proof.
  apply (vl_transport_compl (PreDOv sinstr_sem) (SILv sinstr_sem)).
  change (P (SILv sinstr_sem) (fun s => ~ P6s s) tprog
            (fun s => ~ s = [0; 6])).
  rewrite tprog_eq.
  apply (sil_cons _ _ _ (fun s => exists k, Xpre k s) _ (Xpre 0));
    [| apply sil_while; [apply pre_body | |] |].
  - intros s H. exists (match s with n :: _ :: _ => n | _ => 0 end).
    split; [exact H |]. destruct s as [| n [| a r]]; reflexivity.
  - intros k s [_ Hsh]. destruct s as [| n [| a r]]; simpl in *; lia.
  - intros s [Hn Hsh]. destruct s as [| n [| a r]]; simpl in *; try lia.
    destruct n as [| j]; [lia |]. exfalso. apply Hn. right. exists j. auto.
  - intros s [Hn _] ->. apply Hn. left. exists 0, 6. auto.
Qed.

Theorem stack_PreDU_rules :
  derivable (rules (vl_logic (PreDUv sinstr_sem))) t_HL.
Proof.
  apply (vl_transport_same (PreDUv sinstr_sem) (HLv sinstr_sem)
           (fun t => iff_sym (galois_post_wlp t))).
  exact stack_HL_rules.
Qed.

(** ** Bottom face *)

(** HL⊥, total correctness, with the top of the stack as variant. *)
Lemma total_body : forall (I : stack -> Prop),
    (forall s s1 s', I s -> nz s -> sinstr_sem IAcc s s1 ->
       sinstr_sem IDec s1 s' -> I s' /\ top s' < top s) ->
    forall w, Pb (HLbv sinstr_sem) (som (fun s => I s /\ nz s /\ top s = w))
                 tbody (som (fun s => I s /\ top s < w)).
Proof.
  intros I Hstep w.
  set (Qw := som (fun s => I s /\ top s < w)).
  set (Rb := fun o : option stack =>
               match o with
               | Some s => forall s', sinstr_sem IDec s s' -> Qw (Some s')
               | None => Qw None end).
  apply (hlb_seq _ _ _ Rb); [| apply hlb_act].
  apply (hlb_cons _ _ _
           (fun o => match o with
                     | Some s => forall s', sinstr_sem IAcc s s' -> Rb (Some s')
                     | None => Rb None end) _ Rb);
    [| apply hlb_act | intros o H; exact H].
  intros [s|] H; [| contradiction]. destruct H as [HI [Hnz Hw]].
  intros s1 H1 s' H2. simpl. subst w.
  exact (Hstep s s1 s' HI Hnz H1 H2).
Qed.

Theorem stack_HL_bot_rules :
  HLbv sinstr_sem ⊢⊥ {{ SomeP Pn0 False }} tprog {{ SomeP Qtri False }}.
Proof.
  rewrite tprog_eq.
  apply (hlb_cons _ _ _ (som Inv) _ (som (fun s => Inv s /\ ~ nz s)));
    [| apply (hlb_while_total _ _ nat lt lt_wf top) |].
  - intros [s|] H; simpl in *; [| contradiction].
    destruct H as [n ->]. exists n, 0, n. split; reflexivity.
  - apply total_body. intros s s1 s' HI Hnz H1 H2.
    exact (inv_step s s1 s' HI Hnz H1 H2).
  - intros [s|] H; simpl in *; [| contradiction].
    destruct H as [[n [a [m [-> E]]]] Hn]. simpl in Hn.
    assert (n = 0) by lia. subst. exists m. simpl in E. f_equal. f_equal. lia.
Qed.

Theorem stack_IL_bot_rules :
  ILbv sinstr_sem ⊢⊥ ⟦ SomeP Pn0 False ⟧ tprog ⟦ SomeP Qtri False ⟧.
Proof.
  rewrite tprog_eq.
  apply (ilb_cons _ _ _ (som (Xil 0)) _
           (som (fun s => exists k, Xil k s /\ ~ nz s)));
    [| apply ilb_while |].
  - intros [s|] H; simpl in *; [| contradiction]. destruct H as [m ->].
    exists m. rewrite Nat.add_0_r, Nat.sub_diag. reflexivity.
  - intros k.
    set (Pk := som (fun s => Xil k s /\ nz s)).
    set (Rb := fun o' : option stack =>
                 match o' with
                 | Some s1 => exists s, Pk (Some s) /\ sinstr_sem IAcc s s1
                 | None => Pk None end).
    apply (ilb_cons _ _ _ Pk _
             (fun o' => match o' with
                        | Some s2 => exists s1, Rb (Some s1) /\
                                                sinstr_sem IDec s1 s2
                        | None => Rb None end));
      [intros o H; exact H
      | apply (ilb_seq _ _ _ Rb);
        [apply (ilb_act sinstr_sem (ILbv sinstr_sem) Pk IAcc)
        | apply (ilb_act sinstr_sem (ILbv sinstr_sem) Rb IDec)]
      |].
    intros [s'|] H; simpl in *; [| contradiction].
    exact (il_pred k s' H).
  - intros [s|] H; simpl in *; [| contradiction]. destruct H as [n ->].
    exists n. split; [| simpl; lia]. exists 0. simpl. f_equal. f_equal. lia.
Qed.

(** NC⊥: only ⊥ leads to ⊥. Proved as HL⊥ total correctness of the
    complemented triple (every proper state terminates), transported
    through complement and Galois. *)
Theorem stack_NC_bot_rules :
  Pb (NCbv sinstr_sem) (fun o => o = None) tprog (fun o => o = None).
Proof.
  unfold Pb, provb.
  apply (vl_transport_compl (NCbv sinstr_sem) (PreDUbv sinstr_sem)).
  apply (vl_transport_same (PreDUbv sinstr_sem) (HLbv sinstr_sem)
           (fun t => iff_sym (galois_post_wlp t))).
  change (Pb (HLbv sinstr_sem) (fun o => ~ o = None) tprog
             (fun o => ~ o = None)).
  rewrite tprog_eq.
  apply (hlb_cons _ _ _ (som (fun _ => True)) _
           (som (fun s => True /\ ~ nz s)));
    [| apply (hlb_while_total _ _ nat lt lt_wf top) |].
  - intros [s|] H; simpl; [exact I | apply H; reflexivity].
  - apply total_body. intros s s1 s' _ Hnz H1 H2. split; [exact I |].
    destruct s as [| n [| a r]]; simpl in H1; try contradiction. subst.
    simpl in H2. subst. simpl in *. lia.
  - intros [s|] H; [discriminate | contradiction].
Qed.

Theorem stack_SIL_bot_rules :
  Pb (SILbv sinstr_sem) (SomeP (fun s => s = [3; 0]) False) tprog
     (SomeP (fun s => s = [0; 6]) False).
Proof.
  rewrite tprog_eq.
  apply (silb_cons _ _ _ (som (fun s => exists k, Xsil k s)) _ (som (Xsil 0)));
    [| apply silb_while |].
  - intros [s|] H; simpl in *; [| contradiction]. subst.
    exists 3. split; [lia | reflexivity].
  - intros k.
    set (Rb := fun o : option stack =>
                 match o with
                 | Some s => exists s', sinstr_sem IDec s s' /\
                                        som (Xsil k) (Some s')
                 | None => som (Xsil k) None end).
    apply (silb_seq _ _ _ Rb);
      [| apply (silb_act sinstr_sem (SILbv sinstr_sem) (som (Xsil k)) IDec)].
    apply (silb_cons _ _ _
             (fun o => match o with
                       | Some s =>
                           exists s1, sinstr_sem IAcc s s1 /\ Rb (Some s1)
                       | None => Rb None end) _ Rb);
      [| apply (silb_act sinstr_sem (SILbv sinstr_sem) Rb IAcc)
       | intros o H; exact H].
    intros [s|] H; [| contradiction]. destruct H as [Hk ->].
    exists [S k; 6 - trin (S k) + S k]. split; [reflexivity |].
    exists [k; 6 - trin (S k) + S k]. split; [reflexivity |].
    split; [lia |].
    destruct k as [| [| [| k]]]; simpl in *; try reflexivity; lia.
  - intros k s [_ ->]. simpl. lia.
  - intros s [_ ->]. simpl. lia.
  - intros [s|] H; simpl in *;
      [destruct H as [_ ->]; reflexivity | contradiction].
Qed.

(** p̃ost ⊆ ⊥ via IL⊥ on the complemented triple. *)
Theorem stack_PostDO_bot_rules :
  derivable (rules (vl_logic (PostDObv sinstr_sem))) b_PostDO.
Proof.
  apply (vl_transport_compl (PostDObv sinstr_sem) (ILbv sinstr_sem)).
  set (Ok := SomeP (fun s : stack => exists k r, s = S k :: r) True).
  change (Pb (ILbv sinstr_sem) (fun o => ~ o = None) tprog (fun o => ~ Ok o)).
  rewrite tprog_eq.
  set (X := fun n (s : stack) =>
              match n with 0 => True | S _ => False end).
  apply (ilb_cons _ _ _ (som (X 0)) _
           (som (fun s => exists n, X n s /\ ~ nz s)));
    [| apply ilb_while |].
  - intros [s|] H; simpl in *; [discriminate | contradiction].
  - intros n.
    apply (ilb_cons _ _ _ (som (fun s => X n s /\ nz s)) _ (fun _ => False));
      [intros o H; exact H | apply ilb_false | intros [s|] H; exact H].
  - intros [s|] H; simpl in *; [| exfalso; exact (H I)].
    exists 0. split; [exact I |]. unfold Ok, SomeP in H.
    destruct s as [| [| k] r]; simpl; auto.
    exfalso. apply H. exists k, r. reflexivity.
Qed.

Theorem stack_PostDU_bot_rules :
  derivable (rules (vl_logic (PostDUbv sinstr_sem))) b_NC.
Proof.
  apply (vl_transport_same (PostDUbv sinstr_sem) (NCbv sinstr_sem)
           (fun t => iff_sym (galois_pre_dimg t))).
  exact stack_NC_bot_rules.
Qed.

(** p̃re ⊆ ⊥ via SIL⊥ on the complemented triple: ⊥ stays ⊥, and proper
    states not in [P6s] reach a stack other than [[0; 6]]. *)
Theorem stack_PreDO_bot_rules :
  derivable (rules (vl_logic (PreDObv sinstr_sem))) b_PreDO.
Proof.
  apply (vl_transport_compl (PreDObv sinstr_sem) (SILbv sinstr_sem)).
  set (Q6 := SomeP (fun s : stack => s = [0; 6]) False).
  change (Pb (SILbv sinstr_sem) (fun o => ~ SomeP P6s False o) tprog
             (fun o => ~ Q6 o)).
  rewrite tprog_eq.
  apply (silb_cons _ _ _
           (fun o => o = None \/ som (fun s => exists k, Xpre k s) o)
           _ (fun o => ~ Q6 o)); [| apply silb_disj | intros o H; exact H].
  - intros [s|] H; simpl in *; [right | left; reflexivity].
    exists (match s with n :: _ :: _ => n | _ => 0 end).
    split; [exact H |]. destruct s as [| n [| a r]]; reflexivity.
  - apply (silb_cons _ _ _ (fun o => o = None) _ (fun o => o = None));
      [intros o H; exact H | apply silb_bot
      | intros o ->; unfold Q6; simpl; auto].
  - apply (silb_cons _ _ _ (som (fun s => exists k, Xpre k s)) _
             (som (Xpre 0)));
      [intros o H; exact H | apply silb_while |].
    + intros k.
      set (Rb := fun o : option stack =>
                   match o with
                   | Some s => exists s', sinstr_sem IDec s s' /\
                                          som (Xpre k) (Some s')
                   | None => som (Xpre k) None end).
      apply (silb_seq _ _ _ Rb);
        [| apply (silb_act sinstr_sem (SILbv sinstr_sem) (som (Xpre k)) IDec)].
      apply (silb_cons _ _ _
               (fun o => match o with
                         | Some s => exists s1, sinstr_sem IAcc s s1 /\
                                                Rb (Some s1)
                         | None => Rb None end) _ Rb);
        [| apply (silb_act sinstr_sem (SILbv sinstr_sem) Rb IAcc)
         | intros o H; exact H].
      intros [s|] H; [| contradiction]. destruct H as [Hn Hsh].
      destruct s as [| n [| a r]]; simpl in Hsh; try lia. subst n.
      exists (S k :: (a + S k) :: r). split; [reflexivity |].
      exists (k :: (a + S k) :: r). split; [reflexivity |].
      split; [| reflexivity].
      intros [[m [b [E Hb]]] | [j E]]; [| discriminate].
      injection E as Em Eb Er. subst m b r. apply Hn. left. exists (S k), a.
      split; [reflexivity | simpl in *; lia].
    + intros k s [_ Hsh]. destruct s as [| n [| a r]]; simpl in *; lia.
    + intros s [Hn Hsh]. destruct s as [| n [| a r]]; simpl in *; try lia.
      destruct n as [| j]; [lia |]. exfalso. apply Hn. right. exists j. auto.
    + intros [s|] H; simpl in *; [| contradiction]. destruct H as [Hn _].
      unfold Q6, SomeP. intros ->. apply Hn. left. exists 0, 6. auto.
Qed.

Theorem stack_PreDU_bot_rules :
  derivable (rules (vl_logic (PreDUbv sinstr_sem))) b_HL.
Proof.
  apply (vl_transport_same (PreDUbv sinstr_sem) (HLbv sinstr_sem)
           (fun t => iff_sym (galois_post_wlp t))).
  exact stack_HL_bot_rules.
Qed.
