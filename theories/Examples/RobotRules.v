(** * The robot example, proved with rules in each logic

    The same top-face triples as [RobotExample], proved by applying rules
    ([Core.Rules]) in the records obtained by transformers
    ([Examples.Common]). There is no reasoning about runs or the
    semantics: each proof composes rules, and the only side conditions are
    inclusions between assertions about positions.

    - HL: invariant rule;
    - IL: O'Hearn's variant rule, family "x + y = n";
    - NC: backward-invariant rule;
    - SIL: descending-variant rule, family "n steps from (5, 100)";
    - the [Dual] nodes: prove the complemented triple in IL or SIL, or the
      same triple in NC or HL (Galois), and transport. *)

From Stdlib Require Import Arith Lia.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Verified.
From LogicTransformers.Core Require Import Kernel Rules.
From LogicTransformers.Examples Require Import Common RobotExample.
From LogicTransformers.Core Require Import TripleNotations.
Local Open Scope triple_scope.

Notation P := (prov move_sem) (only parsing).

(** ** HL: the invariant rule *)

Theorem robot_HL_rules :
  HLv move_sem ⊢ {{ fun s => fst s <= 5 }} wander {{ fun s => fst s = 5 }}.
Proof.
  apply (hl_cons _ _ _ I_inv _ (fun s => I_inv s /\ ~ below5 s));
    [intros s H; exact H | apply hl_while |].
  - apply hl_choice.
    + apply (hl_cons _ _ _ (fun s => forall s', move_sem East s s' -> I_inv s')
               _ I_inv); [| apply hl_act | intros s H; exact H].
      intros s [HI Hb] s' Hm. simpl in Hm. subst.
      unfold I_inv, below5 in *. simpl. lia.
    + apply (hl_cons _ _ _ (fun s => forall s', move_sem North s s' -> I_inv s')
               _ I_inv); [| apply hl_act | intros s H; exact H].
      intros s [HI Hb] s' Hm. simpl in Hm. subst.
      unfold I_inv, below5 in *. simpl. lia.
  - intros s [HI Hn]. unfold I_inv, below5 in *. lia.
Qed.

(** ** IL: every column-5 position is reachable from the origin *)

Definition Xil (n : nat) (s : pos) : Prop := fst s + snd s = n /\ fst s <= 5.

Theorem robot_IL_rules :
  ILv move_sem ⊢ ⟦ fun s => s = (0, 0) ⟧ wander ⟦ fun s => fst s = 5 ⟧.
Proof.
  apply (il_cons _ _ _ (Xil 0) _ (fun s => exists n, Xil n s /\ ~ below5 s));
    [| apply il_while |].
  - intros [x y] [H1 H2]. simpl in *. f_equal; lia.
  - intros n.
    apply (il_cons _ _ _ (fun s => Xil n s /\ below5 s) _
             (fun s' => (exists s, (Xil n s /\ below5 s) /\ move_sem East s s')
                        \/ (exists s, (Xil n s /\ below5 s) /\
                                      move_sem North s s')));
      [intros s H; exact H
      | apply il_disj; [apply il_choice_l, il_act | apply il_choice_r, il_act]
      |].
    intros [x y] [H1 H2]. simpl in *. unfold Xil, below5.
    destruct (Nat.eq_dec x 5) as [-> | Hx].
    + left. exists (4, y). simpl. repeat split; lia.
    + destruct y as [| y].
      * left. exists (x - 1, 0). simpl.
        split; [repeat split; lia | f_equal; lia].
      * right. exists (x, y). simpl. repeat split; lia.
  - intros [x y] Hx. simpl in Hx. subst. exists (5 + y).
    unfold Xil, below5. simpl. repeat split; lia.
Qed.

(** ** NC: the backward-invariant rule *)

Theorem robot_NC_rules :
  P (NCv move_sem) P_NC wander (fun s => s = (5, 3)).
Proof.
  apply (nc_cons _ _ _ P_NC _ (fun s => P_NC s /\ ~ below5 s));
    [intros s H; exact H | apply nc_while |].
  - apply nc_choice.
    + apply (nc_cons _ _ _ (fun s => exists s', move_sem East s s' /\ P_NC s')
               _ P_NC); [| apply nc_act | intros s H; exact H].
      intros [x y] [[x' y'] [Hm HI]] Hb. simpl in Hm. inversion Hm; subst.
      unfold P_NC, below5 in *. simpl in *.
      destruct HI as [[H1 H2] | Heq]; [left; lia | inversion Heq; left; lia].
    + apply (nc_cons _ _ _ (fun s => exists s', move_sem North s s' /\ P_NC s')
               _ P_NC); [| apply nc_act | intros s H; exact H].
      intros [x y] [[x' y'] [Hm HI]] Hb. simpl in Hm. inversion Hm; subst.
      unfold P_NC, below5 in *. simpl in *.
      destruct HI as [[H1 H2] | Heq]; [left; lia | inversion Heq; exfalso; lia].
  - intros s ->. unfold P_NC, below5. simpl. split; [right; auto | lia].
Qed.

(** ** SIL: the descending-variant rule *)

Definition Xsil (n : nat) (s : pos) : Prop :=
  (n = 0 /\ s = (5, 100)) \/
  (fst s < 5 /\ snd s <= 100 /\ (5 - fst s) + (100 - snd s) = n).

Theorem robot_SIL_rules :
  P (SILv move_sem) (fun s => fst s < 5 /\ snd s <= 100) wander
    (fun s => s = (5, 100)).
Proof.
  apply (sil_cons _ _ _ (fun s => exists n, Xsil n s) _ (Xsil 0));
    [| apply sil_while |].
  - intros [x y] [H1 H2]. cbn [fst snd] in *. exists ((5 - x) + (100 - y)).
    right. cbn [fst snd]. repeat split; lia.
  - intros n.
    apply (sil_cons _ _ _
             (fun s => (exists s', move_sem North s s' /\ Xsil n s') \/
                       (exists s', move_sem East s s' /\ Xsil n s'))
             _ (Xsil n));
      [| apply sil_disj;
           [apply sil_choice_r, sil_act | apply sil_choice_l, sil_act]
      | intros s H; exact H].
    intros [x y] [[Hn _] | [H1 [H2 H3]]]; [discriminate |]. cbn [fst snd] in *.
    destruct (Nat.eq_dec y 100) as [-> | Hy].
    + right. exists (S x, 100). split; [reflexivity |].
      unfold Xsil. cbn [fst snd].
      destruct (Nat.eq_dec (S x) 5) as [Hx | Hx];
        [left; split; [lia | f_equal; lia] | right; repeat split; lia].
    + left. exists (x, S y). split; [reflexivity |].
      right. cbn [fst snd]. repeat split; lia.
  - intros n s [[Hn _] | [H1 _]]; [discriminate | exact H1].
  - intros s [[_ ->] | [H1 [H2 H3]]]; unfold below5; simpl; lia.
  - intros s [[_ ->] | [H1 [H2 H3]]]; [reflexivity | lia].
Qed.

(** ** The [Dual] nodes, by transport *)

(** p̃ost ⊆ via IL on the complemented triple. *)
Theorem robot_PostDO_rules :
  derivable (rules (vl_logic (PostDOv move_sem))) t_PostDO.
Proof.
  apply (vl_transport_compl (PostDOv move_sem) (ILv move_sem)).
  change (P (ILv move_sem) (fun s => ~ snd s <= 3) wander
            (fun s => ~ (fst s < 5 \/ snd s <= 3))).
  set (X := fun n (s : pos) =>
              match n with 0 => ~ snd s <= 3 | S _ => False end).
  apply (il_cons _ _ _ (X 0) _ (fun s => exists n, X n s /\ ~ below5 s));
    [intros s H; exact H | apply il_while |].
  - intros n.
    apply (il_cons _ _ _ (fun s => X n s /\ below5 s) _ (fun _ => False));
      [intros s H; exact H | apply il_false | intros s H; exact H].
  - intros s H. exists 0. unfold below5. simpl. tauto.
Qed.

(** p̃ost ⊇: the same triple as NC (Galois). *)
Theorem robot_PostDU_rules :
  derivable (rules (vl_logic (PostDUv move_sem))) t_NC.
Proof.
  apply (vl_transport_same (PostDUv move_sem) (NCv move_sem)
           (fun t => iff_sym (galois_pre_dimg t))).
  exact robot_NC_rules.
Qed.

(** p̃re ⊆ via SIL on the complemented triple. *)
Theorem robot_PreDO_rules :
  derivable (rules (vl_logic (PreDOv move_sem))) t_PreDO.
Proof.
  apply (vl_transport_compl (PreDOv move_sem) (SILv move_sem)).
  change (P (SILv move_sem) (fun s => ~ fst s <= 5) wander
            (fun s => ~ fst s = 5)).
  set (X := fun n (s : pos) =>
              match n with 0 => ~ fst s <= 5 | S _ => False end).
  apply (sil_cons _ _ _ (fun s => exists n, X n s) _ (X 0));
    [| apply sil_while |].
  - intros s H. exists 0. exact H.
  - intros n. apply sil_false.
  - intros n s [].
  - intros s H. unfold below5. simpl in *. lia.
  - intros s H. simpl in *. lia.
Qed.

(** p̃re ⊇: the same triple as HL (Galois). *)
Theorem robot_PreDU_rules :
  derivable (rules (vl_logic (PreDUv move_sem))) t_HL.
Proof.
  apply (vl_transport_same (PreDUv move_sem) (HLv move_sem)
           (fun t => iff_sym (galois_post_wlp t))).
  exact robot_HL_rules.
Qed.

(** ** Bottom face, with the bottom-face rules *)

From LogicTransformers.Core Require Import KernelBot RulesBot.

Notation Pb := (provb move_sem) (only parsing).

(** HL⊥: invariant rule, partial (divergence allowed). *)
Theorem robot_HL_bot_rules :
  HLbv move_sem ⊢⊥ {{ SomeP (fun s => fst s <= 5) False }} wander
                   {{ SomeP (fun s => fst s = 5) True }}.
Proof.
  set (Iv := fun s : pos => fst s <= 5).
  set (Ib := fun o : option pos =>
               match o with Some s => Iv s | None => True end).
  apply (hlb_cons _ _ _ (som Iv) _
           (fun o => match o with
                     | Some s => Iv s /\ ~ below5 s
                     | None => True end));
    [intros o H; exact H | apply hlb_while_inv |].
  - apply hlb_choice.
    + apply (hlb_cons _ _ _
               (fun o => match o with
                         | Some s =>
                             forall s', move_sem East s s' -> Ib (Some s')
                         | None => Ib None end) _ Ib);
        [| apply hlb_act | intros o H; exact H].
      intros [s|] H; [| contradiction]. destruct H as [HI Hb].
      intros s' Hm. simpl in Hm. subst. unfold Ib, Iv, below5 in *. simpl. lia.
    + apply (hlb_cons _ _ _
               (fun o => match o with
                         | Some s =>
                             forall s', move_sem North s s' -> Ib (Some s')
                         | None => Ib None end) _ Ib);
        [| apply hlb_act | intros o H; exact H].
      intros [s|] H; [| contradiction]. destruct H as [HI Hb].
      intros s' Hm. simpl in Hm. subst. unfold Ib, Iv, below5 in *. simpl. lia.
  - intros [s|] H; simpl in *; [| exact I]. unfold Iv, below5 in *. lia.
Qed.

(** IL⊥: divergence is reachable from the origin (always go north). *)
Theorem robot_IL_bot_rules :
  ILbv move_sem ⊢⊥ ⟦ fun o => o = Some (0, 0) ⟧ wander ⟦ fun o => o = None ⟧.
Proof.
  apply (ilb_diverge _ _ below5); [unfold below5; simpl; lia |].
  intros [x y] Hx. split; [exact Hx |]. exists (x, S y).
  split; [exact Hx |].
  change (Pb (ILbv move_sem) (fun o => o = Some (x, y))
            (KChoice (KAct East) (KAct North)) (fun o => o = Some (x, S y))).
  apply ilb_choice_r.
  apply (ilb_cons _ _ _ (fun o => o = Some (x, y)) _
           (fun o' => match o' with
                      | Some s' => exists s, Some s = Some (x, y) /\
                                             move_sem North s s'
                      | None => None = Some (x, y) end));
    [intros o H; exact H
    | apply (ilb_act move_sem (ILbv move_sem) (fun o => o = Some (x, y)) North)
    |].
  intros o ->. exists (x, y). split; reflexivity.
Qed.

(** NC⊥: only starts left of column 5 can diverge (guard necessity). *)
Theorem robot_NC_bot_rules :
  Pb (NCbv move_sem) P_NCb wander (fun o => o = None).
Proof. exact (ncb_div_guard move_sem (NCbv move_sem) below5 step). Qed.

(** SIL⊥: every start left of column 5 can diverge (coinvariant x < 5). *)
Theorem robot_SIL_bot_rules :
  Pb (SILbv move_sem) (SomeP (fun s => fst s < 5) False) wander
     (fun o => o = None).
Proof.
  apply (silb_diverge _ _ below5); [| intros s H; exact H].
  apply silb_choice_r.
  apply (silb_cons _ _ _
           (fun o => match o with
                     | Some s =>
                         exists s', move_sem North s s' /\ som below5 (Some s')
                     | None => som below5 None end) _ (som below5));
    [| apply (silb_act move_sem (SILbv move_sem) (som below5) North)
     | intros o H; exact H].
  intros [[x y]|] H; [| contradiction]. exists (x, S y). split; [reflexivity |].
  exact H.
Qed.

(** p̃ost ⊆ ⊥ via IL⊥ on the complemented triple. *)
Theorem robot_PostDO_bot_rules :
  derivable (rules (vl_logic (PostDObv move_sem))) b_PostDO.
Proof.
  apply (vl_transport_compl (PostDObv move_sem) (ILbv move_sem)).
  change (Pb (ILbv move_sem) (fun o => ~ P_NCb o) wander (fun o => ~ P_NCb o)).
  set (X := fun n (s : pos) =>
              match n with 0 => ~ below5 s | S _ => False end).
  apply (ilb_cons _ _ _ (som (X 0)) _
           (som (fun s => exists n, X n s /\ ~ below5 s)));
    [| apply ilb_while |].
  - intros [s|] H; simpl in *; [exact H | contradiction].
  - intros n. apply (ilb_cons _ _ _ (som (fun s => X n s /\ below5 s)) _
                       (fun _ => False));
      [intros o H; exact H | apply ilb_false | intros [s|] H; exact H].
  - intros [s|] H; simpl in *; [| exfalso; exact (H I)].
    exists 0. split; exact H.
Qed.

(** p̃ost ⊇ ⊥: the same triple as NC⊥ (Galois). *)
Theorem robot_PostDU_bot_rules :
  derivable (rules (vl_logic (PostDUbv move_sem))) b_NC.
Proof.
  apply (vl_transport_same (PostDUbv move_sem) (NCbv move_sem)
           (fun t => iff_sym (galois_pre_dimg t))).
  exact robot_NC_bot_rules.
Qed.

(** p̃re ⊆ ⊥ via SIL⊥ on the complemented triple, by cases: ⊥ stays ⊥;
    left of column 5 diverges; right of column 5 stops at once. *)
Theorem robot_PreDO_bot_rules :
  derivable (rules (vl_logic (PreDObv move_sem))) b_PreDO.
Proof.
  apply (vl_transport_compl (PreDObv move_sem) (SILbv move_sem)).
  set (Q5 := SomeP (fun s : pos => fst s = 5) False).
  change (Pb (SILbv move_sem) (fun o => ~ Q5 o) wander (fun o => ~ Q5 o)).
  set (X := fun n (s : pos) =>
              match n with 0 => 5 < fst s | S _ => False end).
  apply (silb_cons _ _ _
           (fun o => (o = None \/ som below5 o) \/
                     som (fun s => exists n, X n s) o)
           _ (fun o => ~ Q5 o)); [| | intros o H; exact H].
  - intros [s|] H; simpl in *.
    + destruct (lt_dec (fst s) 5) as [Hl | Hl]; [left; right; exact Hl |].
      right. exists 0. unfold Q5, SomeP in H. simpl. lia.
    + left. left. reflexivity.
  - apply silb_disj; [apply silb_disj |].
    + apply (silb_cons _ _ _ (fun o => o = None) _ (fun o => o = None));
        [intros o H; exact H | apply silb_bot
        | intros o ->; unfold Q5; simpl; auto].
    + apply (silb_cons _ _ _ (som below5) _ (fun o => o = None));
        [intros o H; exact H | | intros o ->; unfold Q5; simpl; auto].
      apply (silb_diverge _ _ below5); [| intros s H; exact H].
      apply silb_choice_r.
      apply (silb_cons _ _ _
               (fun o => match o with
                         | Some s => exists s', move_sem North s s' /\
                                                som below5 (Some s')
                         | None => som below5 None end) _ (som below5));
        [| apply (silb_act move_sem (SILbv move_sem) (som below5) North)
         | intros o H; exact H].
      intros [[x y]|] H; [| contradiction]. exists (x, S y).
      split; [reflexivity | exact H].
    + apply (silb_cons _ _ _ (som (fun s => exists n, X n s)) _ (som (X 0)));
        [intros o H; exact H | apply silb_while |].
      * intros n. apply silb_cons with (P' := fun _ => False) (Q' := som (X n));
          [intros [s|] H; exact H | apply silb_false | intros o H; exact H].
      * intros n s [].
      * intros s H. unfold below5. simpl in *. lia.
      * intros [s|] H; simpl in *; [unfold Q5, SomeP; lia | contradiction].
Qed.

(** p̃re ⊇ ⊥: the same triple as HL⊥ (Galois). *)
Theorem robot_PreDU_bot_rules :
  derivable (rules (vl_logic (PreDUbv move_sem))) b_HL.
Proof.
  apply (vl_transport_same (PreDUbv move_sem) (HLbv move_sem)
           (fun t => iff_sym (galois_post_wlp t))).
  exact robot_HL_bot_rules.
Qed.
