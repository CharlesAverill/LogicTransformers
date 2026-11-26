(** * Concurrent Imp: message passing, proved with rules at every node

<<
      mp  =  while f = 0 do skip end ; y := x     (reader)
          ∥  x := 42 ; f := 1                      (writer)
>>

    The reader busy-waits on the flag [f], then reads [x]. Under the
    interleaving semantics ([ParImp]) with an unfair scheduler:
    - from [f = 0], every terminating run ends with [y = 42] (HL);
    - the reader can spin forever if the writer is never scheduled (IL⊥);
    - from [f ≠ 0] the program always terminates (total HL⊥), so
      divergence needs [f = 0] (NC⊥).

    Each triple is about the encoded program [penc mp]: load [mp], then
    take steps while not done ([Core.SmallStepCore]). Assertions are on
    configurations [(program, state)]: preconditions look at the state,
    postconditions at final configurations ([fst k = PSkip]). Every proof
    applies rules in the records of [Examples.Common], and the last section
    transfers the results back to [mp] itself.

    The loop is the scheduler loop, so loop invariants are global,
    Owicki-Gries style invariants over both threads' positions:
    - [t1 i], [t2 j]: the reader's and writer's residual programs;
    - [inv i j]: what holds of the state at positions [(i, j)];
    - [G_step]: every step preserves the invariant [G]. HL, HL⊥ and NC
      (through its complement) all use it.
    Runs are given by [d n s], the configuration after [n] steps of the
    schedule "writer first". It gives the iteration variants of IL and
    SIL. [spin] gives the reader's spinning cycle (IL⊥, SIL⊥), and [I2]
    with [wt] the termination argument (total HL⊥).

    Only [sxfy_upd], which picks an exact predecessor for IL, uses
    [functional_extensionality]. The complement-derived nodes use
    [classic], as everywhere in the cube. *)

From Stdlib Require Import String Arith Lia Wf_nat FunctionalExtensionality.
From LogicTransformers.Imp Require Import Syntax.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Relational Verified.
From LogicTransformers.Transformers Require Import Complement.
From LogicTransformers.Core Require Import
  Kernel KernelBot SmallStepCore Rules RulesBot.
From LogicTransformers.ParImp Require Import ParImp.
From LogicTransformers.Examples Require Import Common.
From LogicTransformers.Core Require Import TripleNotations.

Local Open Scope com_scope.
Local Open Scope pcom_scope.
Local Open Scope string_scope.
Local Open Scope triple_scope.

Local Notation X := "x".
Local Notation Y := "y".
Local Notation F := "f".

Definition reader : pcom := <{ while "f" = 0 do skip end ; "y" := "x" }>.
Definition writer : pcom := <{ "x" := 42 ; "f" := 1 }>.
Definition mp : pcom := <{ reader ∥ writer }>.

Notation P := (prov pact_sem) (only parsing).
Notation Pb := (provb pact_sem) (only parsing).

(** Assertions on states, read on configurations. *)
Definition SomeP (Q : state -> Prop) (bot : Prop) : option state -> Prop :=
  fun o => match o with Some s => Q s | None => bot end.

(** ** Positions of the two threads *)

Local Notation W := (PWhile (BEq (AVar F) (ANum 0)) PSkip).
Local Notation Rd := (PAsgn Y (AVar X)).

Definition t1 (i : nat) : pcom :=
  match i with
  | 0 => PSeq W Rd
  | 1 => PSeq (PIf (BEq (AVar F) (ANum 0)) (PSeq PSkip W) PSkip) Rd
  | 2 => PSeq (PSeq PSkip W) Rd
  | 3 => PSeq PSkip Rd
  | 4 => Rd
  | _ => PSkip
  end.

Definition t2 (j : nat) : pcom :=
  match j with
  | 0 => PSeq (PAsgn X (ANum 42)) (PAsgn F (ANum 1))
  | 1 => PSeq PSkip (PAsgn F (ANum 1))
  | 2 => PAsgn F (ANum 1)
  | _ => PSkip
  end.

Lemma mp_eq : mp = PPar (t1 0) (t2 0).
Proof. reflexivity. Qed.

Ltac pinv :=
  repeat match goal with
  | H : pstep (PSkip, _) _ |- _ => inversion H
  | H : pstep (PSeq _ _, _) _ |- _ => inversion H; subst; clear H
  | H : pstep (PWhile _ _, _) _ |- _ => inversion H; subst; clear H
  | H : pstep (PIf _ _ _, _) _ |- _ => inversion H; subst; clear H
  | H : pstep (PAsgn _ _, _) _ |- _ => inversion H; subst; clear H
  | H : beval _ _ = _ |- _ =>
      simpl in H; first [apply Nat.eqb_eq in H | apply Nat.eqb_neq in H]
  end.

Lemma t1_step : forall i s k', pstep (t1 i, s) k' ->
    (i = 0 /\ k' = (t1 1, s)) \/
    (i = 1 /\ s F = 0 /\ k' = (t1 2, s)) \/
    (i = 1 /\ s F <> 0 /\ k' = (t1 3, s)) \/
    (i = 2 /\ k' = (t1 0, s)) \/
    (i = 3 /\ k' = (t1 4, s)) \/
    (i = 4 /\ k' = (t1 5, update s Y (s X))).
Proof.
  intros i s k' H. destruct i as [|[|[|[|[|i]]]]]; simpl in H; pinv;
    intuition (try reflexivity; auto).
Qed.

Lemma t2_step : forall j s k', pstep (t2 j, s) k' ->
    (j = 0 /\ k' = (t2 1, update s X 42)) \/
    (j = 1 /\ k' = (t2 2, s)) \/
    (j = 2 /\ k' = (t2 3, update s F 1)).
Proof.
  intros j s k' H. destruct j as [|[|[|j]]]; simpl in H; pinv;
    intuition (try reflexivity; auto).
Qed.

Lemma par_step : forall p1 p2 s k', pstep (PPar p1 p2, s) k' ->
    (exists p1' s', pstep (p1, s) (p1', s') /\ k' = (PPar p1' p2, s')) \/
    (exists p2' s', pstep (p2, s) (p2', s') /\ k' = (PPar p1 p2', s')) \/
    (p1 = PSkip /\ p2 = PSkip /\ k' = (PSkip, s)).
Proof.
  intros p1 p2 s k' H. inversion H; subst; [left | right; left | right; right];
    eauto.
Qed.

(** One step of the combined program, by which thread moved. *)
Ltac step_cases H :=
  apply par_step in H as
    [[p1' [s' [H ->]]] | [[p2' [s' [H ->]]] | [E1 [E2 ->]]]];
  [ apply t1_step in H as
      [[-> E] | [[-> [? E]] | [[-> [? E]] | [[-> E] | [[-> E] | [-> E]]]]]];
    injection E; intros; subst
  | apply t2_step in H as [[-> E] | [[-> E] | [-> E]]];
    injection E; intros; subst
  | ].

(** ** The global invariant *)

Definition inv (i j : nat) (s : state) : Prop :=
  match j with
  | 0 => s F = 0
  | 1 | 2 => s F = 0 /\ s X = 42
  | _ => s F = 1 /\ s X = 42
  end /\
  match i with
  | 0 | 1 | 2 => True
  | 3 | 4 => j = 3
  | _ => j = 3 /\ s Y = 42
  end.

Definition G (k : pcfg) : Prop :=
  (exists i j, i <= 5 /\ j <= 3 /\ fst k = PPar (t1 i) (t2 j) /\
               inv i j (snd k)) \/
  (fst k = PSkip /\ snd k Y = 42).

Lemma G_par : forall i j s, i <= 5 -> j <= 3 -> inv i j s ->
    G (PPar (t1 i) (t2 j), s).
Proof. intros i j s Hi Hj H. left. exists i, j. auto. Qed.

Lemma G_init : forall s, s F = 0 -> G (mp, s).
Proof.
  intros s H. rewrite mp_eq.
  apply G_par; [lia | lia | unfold inv; simpl; tauto].
Qed.

Ltac inv_close :=
  unfold inv in *; cbn [snd] in *; unfold update; simpl;
  intuition (try lia; try discriminate).

Ltac inv_to i' j' :=
  apply (G_par i' j'); [lia | lia |].

Lemma G_step : forall k k', G k -> pstep k k' -> G k'.
Proof.
  intros [p s] k' [[i [j [Hi [Hj [Ek Hv]]]]] | [Ek Hy]] Hs;
    simpl in Ek; subst p; [| inversion Hs].
  step_cases Hs.
  - inv_to 1 j. destruct j as [|[|[|[|j]]]]; try lia; inv_close.
  - inv_to 2 j. destruct j as [|[|[|[|j]]]]; try lia; inv_close.
  - inv_to 3 j. destruct j as [|[|[|[|j]]]]; try lia; inv_close.
  - inv_to 0 j. destruct j as [|[|[|[|j]]]]; try lia; inv_close.
  - inv_to 4 j. destruct j as [|[|[|[|j]]]]; try lia; inv_close.
  - inv_to 5 j. destruct j as [|[|[|[|j]]]]; try lia; inv_close.
  - inv_to i 1. destruct i as [|[|[|[|[|[|i]]]]]]; try lia; inv_close.
  - inv_to i 2. destruct i as [|[|[|[|[|[|i]]]]]]; try lia; inv_close.
  - inv_to i 3. destruct i as [|[|[|[|[|[|i]]]]]]; try lia; inv_close.
  - right. destruct i as [|[|[|[|[|[|i]]]]]]; try lia; try discriminate.
    destruct j as [|[|[|[|j]]]]; try lia; try discriminate.
    unfold inv in Hv. simpl in *. split; [reflexivity | tauto].
Qed.

Lemma G_final : forall k, G k -> ~ prunning k -> fst k = PSkip /\ snd k Y = 42.
Proof.
  intros k [[i [j [_ [_ [Ek _]]]]] | H] Hn; [| exact H].
  exfalso. apply Hn. unfold running. rewrite Ek. discriminate.
Qed.

(** ** The schedule "writer first" *)

Definition sx (s : state) : state := update s X 42.
Definition sxf (s : state) : state := update (sx s) F 1.
Definition sxfy (s : state) : state := update (sxf s) Y 42.

Definition d (n : nat) (s : state) : pcfg :=
  match n with
  | 0 => (PPar (t1 0) (t2 0), s)
  | 1 => (PPar (t1 0) (t2 1), sx s)
  | 2 => (PPar (t1 0) (t2 2), sx s)
  | 3 => (PPar (t1 0) (t2 3), sxf s)
  | 4 => (PPar (t1 1) (t2 3), sxf s)
  | 5 => (PPar (t1 3) (t2 3), sxf s)
  | 6 => (PPar (t1 4) (t2 3), sxf s)
  | 7 => (PPar (t1 5) (t2 3), sxfy s)
  | _ => (PSkip, sxfy s)
  end.

Lemma d_step : forall n s, n < 8 -> pstep (d n s) (d (S n) s).
Proof.
  intros n s Hn. destruct n as [|[|[|[|[|[|[|[|n]]]]]]]]; try lia;
    simpl; repeat constructor.
Qed.

Lemma d_running : forall n s, n < 8 -> prunning (d n s).
Proof.
  intros n s Hn. destruct n as [|[|[|[|[|[|[|[|n]]]]]]]]; try lia;
    unfold running; simpl; discriminate.
Qed.

Lemma d_final : forall s, d 8 s = (PSkip, sxfy s).
Proof. reflexivity. Qed.

(** An exact predecessor for IL: every final state with the message
    delivered is [sxfy] of a state with any chosen flag. *)
Lemma sxfy_upd : forall s' v, s' F = 1 -> s' X = 42 -> s' Y = 42 ->
    sxfy (update s' F v) = s'.
Proof.
  intros s' v Hf Hx Hy. apply functional_extensionality. intros z.
  unfold sxfy, sxf, sx, update.
  destruct (String.eqb_spec Y z); [subst; auto |].
  destruct (String.eqb_spec F z); [subst; auto |].
  destruct (String.eqb_spec X z); [subst; auto |].
  destruct (String.eqb_spec F z); [contradiction | reflexivity].
Qed.

Definition Done (s : state) : Prop := s F = 1 /\ s X = 42 /\ s Y = 42.

(** ** Top face *)

(** HL: from [f = 0], the reader receives the message. *)
Theorem mp_HL :
  HLv pact_sem ⊢ {{ fun k => snd k F = 0 }} penc mp
                 {{ fun k => fst k = PSkip /\ snd k Y = 42 }}.
Proof.
  apply (hl_seq _ _ _ G).
  - apply (hl_cons _ _ _
             (fun k => forall k', pact_sem (SLoad mp) k k' -> G k') _ G);
      [| apply hl_act | intros k H; exact H].
    intros k Hf k' E. simpl in E. subst k'. apply G_init, Hf.
  - apply (hl_cons _ _ _ G _ (fun k => G k /\ ~ prunning k));
      [intros k H; exact H | apply hl_while |].
    + apply (hl_cons _ _ _ (fun k => forall k', pact_sem SStep k k' -> G k')
               _ G); [| apply hl_act | intros k H; exact H].
      intros k [HG _] k' Hs. exact (G_step k k' HG Hs).
    + intros k [HG Hn]. exact (G_final k HG Hn).
Qed.

(** IL, for any precondition with an exact predecessor of each target. *)
Lemma mp_IL_gen : forall (Pre Fin : state -> Prop),
    (forall s', Fin s' -> exists s, Pre s /\ sxfy s = s') ->
    ILv pact_sem ⊢ ⟦ fun k => Pre (snd k) ⟧ penc mp
                   ⟦ fun k => fst k = PSkip /\ Fin (snd k) ⟧.
Proof.
  intros Pre Fin HF.
  set (Xn := fun n k => n <= 8 /\ exists s, Pre s /\ k = d n s).
  apply (il_seq _ _ _ (Xn 0)).
  - apply (il_cons _ _ _ (fun k => Pre (snd k)) _
             (fun k' => exists k, Pre (snd k) /\
                                  pact_sem (SLoad mp) k k'));
      [intros k H; exact H | apply il_act |].
    intros k' [_ [s [HP ->]]]. exists (PSkip, s). split; [exact HP |].
    reflexivity.
  - apply (il_cons _ _ _ (Xn 0) _
             (fun k => exists n, Xn n k /\ ~ prunning k));
      [intros k H; exact H | apply il_while |].
    + intros n.
      apply (il_cons _ _ _ (fun k => Xn n k /\ prunning k) _
               (fun k' => exists k, (Xn n k /\ prunning k) /\
                                    pact_sem SStep k k'));
        [intros k H; exact H | apply il_act |].
      intros k' [Hn [s [HP ->]]]. exists (d n s).
      split; [split; [split; [lia | eauto] | apply d_running; lia] |].
      apply d_step. lia.
    + intros [p s'] [Ep HFin]. simpl in Ep, HFin. subst p.
      destruct (HF s' HFin) as [s [HP Es]]. exists 8.
      split; [split; [lia | exists s; split; [exact HP |]] |].
      * rewrite d_final, Es. reflexivity.
      * intros Hr. apply Hr. reflexivity.
Qed.

(** IL: every final state with the message delivered is reachable from
    a state with [f = 0]. *)
Theorem mp_IL :
  ILv pact_sem ⊢ ⟦ fun k => snd k F = 0 ⟧ penc mp
                 ⟦ fun k => fst k = PSkip /\ Done (snd k) ⟧.
Proof.
  apply (mp_IL_gen (fun s => s F = 0) Done).
  intros s' [Hf [Hx Hy]]. exists (update s' F 0).
  split; [apply update_eq | apply sxfy_upd; assumption].
Qed.

(** NC: missing the message requires the flag to be set initially. The
    backward invariant is the complement of [G]. *)
Theorem mp_NC :
  P (NCv pact_sem) (fun k => snd k F <> 0) (penc mp)
    (fun k => fst k = PSkip /\ snd k Y <> 42).
Proof.
  apply (nc_seq _ _ _ (fun k => ~ G k)).
  - apply (nc_cons _ _ _
             (fun k => exists k', pact_sem (SLoad mp) k k' /\ ~ G k') _
             (fun k => ~ G k)); [| apply nc_act | intros k H; exact H].
    intros k [k' [E HG]] Hf. simpl in E. subst k'. apply HG, G_init, Hf.
  - apply (nc_cons _ _ _ (fun k => ~ G k) _
             (fun k => ~ G k /\ ~ prunning k));
      [intros k H; exact H | apply nc_while |].
    + apply (nc_cons _ _ _
               (fun k => exists k', pact_sem SStep k k' /\ ~ G k') _
               (fun k => ~ G k)); [| apply nc_act | intros k H; exact H].
      intros k [k' [Hs HG]] _ HGk. exact (HG (G_step k k' HGk Hs)).
    + intros k [Ep Hy]. split.
      * intros HG. destruct (G_final k HG); [| contradiction].
        intros Hr. apply Hr. exact Ep.
      * intros Hr. apply Hr. exact Ep.
Qed.

(** SIL: from any state, some schedule delivers the message. The
    variant is "steps to go" along the writer-first schedule. *)
Lemma mp_SIL_gen : forall (Pre : state -> Prop),
    P (SILv pact_sem) (fun k => Pre (snd k)) (penc mp)
      (fun k => fst k = PSkip /\ snd k Y = 42).
Proof.
  intros Pre.
  set (Xn := fun m k => m <= 8 /\ exists s, k = d (8 - m) s).
  apply (sil_seq _ _ _ (fun k => exists m, Xn m k)).
  - apply (sil_cons _ _ _
             (fun k => exists k', pact_sem (SLoad mp) k k' /\
                                  exists m, Xn m k') _
             (fun k => exists m, Xn m k));
      [| apply sil_act | intros k H; exact H].
    intros k _. exists (mp, snd k). split; [reflexivity |].
    exists 8. split; [lia | exists (snd k); reflexivity].
  - apply (sil_cons _ _ _ (fun k => exists m, Xn m k) _ (Xn 0));
      [intros k H; exact H | apply sil_while |].
    + intros m.
      apply (sil_cons _ _ _
               (fun k => exists k', pact_sem SStep k k' /\ Xn m k') _ (Xn m));
        [| apply sil_act | intros k H; exact H].
      intros k [Hm [s ->]]. exists (d (8 - m) s). split.
      * replace (8 - m) with (S (8 - S m)) by lia. apply d_step. lia.
      * split; [lia | exists s; reflexivity].
    + intros m k [Hm [s ->]]. apply d_running. lia.
    + intros k [_ [s ->]] Hn. apply Hn. reflexivity.
    + intros k [_ [s ->]]. simpl. split; [reflexivity |].
      unfold sxfy. apply update_eq.
Qed.

Theorem mp_SIL :
  P (SILv pact_sem) (fun k => True) (penc mp)
    (fun k => fst k = PSkip /\ snd k Y = 42).
Proof. exact (mp_SIL_gen (fun _ => True)). Qed.

(** p̃ost ⊆ via IL on the complemented triple. *)
Theorem mp_PostDO :
  P (PostDOv pact_sem) (fun k => snd k F = 0) (penc mp)
    (fun k => fst k = PSkip -> ~ Done (snd k)).
Proof.
  apply (vl_transport_compl (PostDOv pact_sem) (ILv pact_sem)).
  change (P (ILv pact_sem) (fun k => ~ snd k F = 0) (penc mp)
            (fun k => ~ (fst k = PSkip -> ~ Done (snd k)))).
  apply (il_cons _ _ _ (fun k => snd k F <> 0) _
           (fun k => fst k = PSkip /\ Done (snd k)));
    [intros k H; exact H | |].
  - apply (mp_IL_gen (fun s => s F <> 0) Done).
    intros s' [Hf [Hx Hy]]. exists (update s' F 2).
    split; [rewrite update_eq; discriminate | apply sxfy_upd; assumption].
  - intros [p s] H. simpl in *. destruct (pskip_dec p) as [-> | Hp].
    + split; [reflexivity |]. unfold Done.
      destruct (Nat.eq_dec (s F) 1), (Nat.eq_dec (s X) 42),
               (Nat.eq_dec (s Y) 42);
        try (exfalso; apply H; intros _ [? [? ?]]; lia).
      auto.
    + exfalso. apply H. intros Ep. contradiction.
Qed.

Theorem mp_PostDU :
  P (PostDUv pact_sem) (fun k => snd k F <> 0) (penc mp)
    (fun k => fst k = PSkip /\ snd k Y <> 42).
Proof.
  apply (vl_transport_same (PostDUv pact_sem) (NCv pact_sem)
           (fun t => iff_sym (galois_pre_dimg t))).
  exact mp_NC.
Qed.

(** p̃re ⊆ via SIL on the complemented triple: no initial state forces
    the reader to miss the message. *)
Theorem mp_PreDO :
  P (PreDOv pact_sem) (fun k => False) (penc mp)
    (fun k => fst k = PSkip /\ snd k Y <> 42).
Proof.
  apply (vl_transport_compl (PreDOv pact_sem) (SILv pact_sem)).
  change (P (SILv pact_sem) (fun k => ~ False) (penc mp)
            (fun k => ~ (fst k = PSkip /\ snd k Y <> 42))).
  apply (sil_cons _ _ _ (fun k => True) _
           (fun k => fst k = PSkip /\ snd k Y = 42));
    [intros k _; exact I | exact mp_SIL |].
  intros k [_ Hy] [_ Hn]. contradiction.
Qed.

Theorem mp_PreDU :
  P (PreDUv pact_sem) (fun k => snd k F = 0) (penc mp)
    (fun k => fst k = PSkip /\ snd k Y = 42).
Proof.
  apply (vl_transport_same (PreDUv pact_sem) (HLv pact_sem)
           (fun t => iff_sym (galois_post_wlp t))).
  exact mp_HL.
Qed.

(** ** Bottom face *)

Notation pre0 := (fun o => SomeP (fun s => s F = 0) False (option_map snd o)).

(** HL⊥: from [f = 0], the program diverges or delivers the message. *)
Theorem mp_HL_bot :
  HLbv pact_sem ⊢⊥ {{ pre0 }} penc mp
                   {{ fun o => pfinB o /\
                        SomeP (fun s => s Y = 42) True (option_map snd o) }}.
Proof.
  apply (hlb_seq _ _ _ (som G)).
  - apply (hlb_cons _ _ _
             (fun o => match o with
                       | Some k => forall k', pact_sem (SLoad mp) k k' ->
                                              som G (Some k')
                       | None => som G None end) _ (som G));
      [| apply hlb_act | intros o H; exact H].
    intros [k|] H; simpl in *; [| contradiction].
    intros k' ->. apply G_init, H.
  - apply (hlb_cons _ _ _ (som G) _
             (fun o => match o with
                       | Some k => G k /\ ~ prunning k
                       | None => True end));
      [intros o H; exact H | apply hlb_while_inv |].
    + refine (hlb_cons _ _ _ _ _ _ _ _
                (hlb_act pact_sem (HLbv pact_sem)
                   (fun o => match o with Some k => G k | None => True end)
                   SStep) _); [| intros o H; exact H].
      intros [k|] H; simpl in *; [| exact I].
      intros k' Hs. exact (G_step k k' (proj1 H) Hs).
    + intros [k|] H; simpl in *; [| auto].
      destruct H as [HG Hn]. exact (G_final k HG Hn).
Qed.

(** Total correctness from [f ≠ 0]: the reader never waits. *)
Definition I2 (k : pcfg) : Prop :=
  (exists i j, i <= 5 /\ i <> 2 /\ j <= 3 /\
               fst k = PPar (t1 i) (t2 j) /\ snd k F <> 0) \/
  fst k = PSkip.

Fixpoint wt (p : pcom) : nat :=
  match p with
  | PSkip => 0
  | PAsgn _ _ => 1
  | PSeq p1 p2 => wt p1 + wt p2 + 1
  | PIf _ _ p2 => wt p2 + 1
  | PWhile _ _ => 3
  | PPar p1 p2 => wt p1 + wt p2 + 1
  | PMulti _ => 1
  end.

Ltac i2_to i' j' :=
  split; [left; exists i', j'; cbn [fst snd];
          repeat split; try reflexivity; try lia; unfold update; simpl; lia
         | simpl; lia].

Lemma I2_step : forall k k', I2 k -> pstep k k' ->
    I2 k' /\ wt (fst k') < wt (fst k).
Proof.
  intros [p s] k' [[i [j [Hi [H2 [Hj [Ek Hf]]]]]] | Ek] Hs;
    cbn [fst snd] in *; subst p; [| inversion Hs].
  step_cases Hs.
  - i2_to 1 j.
  - exfalso. lia.
  - i2_to 3 j.
  - exfalso. lia.
  - i2_to 4 j.
  - i2_to 5 j.
  - i2_to i 1.
  - i2_to i 2.
  - i2_to i 3.
  - destruct i as [|[|[|[|[|[|i]]]]]]; try lia; try discriminate.
    destruct j as [|[|[|[|j]]]]; try lia; try discriminate.
    split; [right; reflexivity | simpl; lia].
Qed.

Theorem mp_HL_bot_total :
  HLbv pact_sem ⊢⊥ {{ som (fun k => snd k F <> 0) }} penc mp
                   {{ som (fun _ => True) }}.
Proof.
  apply (hlb_seq _ _ _ (som I2)).
  - apply (hlb_cons _ _ _
             (fun o => match o with
                       | Some k => forall k', pact_sem (SLoad mp) k k' ->
                                              som I2 (Some k')
                       | None => som I2 None end) _ (som I2));
      [| apply hlb_act | intros o H; exact H].
    intros [k|] H; simpl in *; [| contradiction].
    intros k' ->. left. exists 0, 0. simpl. repeat split; auto; lia.
  - apply (hlb_cons _ _ _ (som I2) _
             (som (fun k => I2 k /\ ~ prunning k)));
      [intros o H; exact H |
       apply (hlb_while_total _ _ _ lt lt_wf (fun k => wt (fst k))) |
       intros [k|] H; simpl in *; [exact I | exact H]].
    intros w.
    refine (hlb_cons _ _ _ _ _ _ _ _
              (hlb_act pact_sem (HLbv pact_sem)
                 (som (fun k0 => I2 k0 /\ wt (fst k0) < w)) SStep) _);
      [| intros o H; exact H].
    intros [k|] H; simpl in *; [| contradiction].
    destruct H as [HI [_ <-]]. intros k' Hs. exact (I2_step k k' HI Hs).
Qed.

(** The reader's spinning cycle, at a fixed state with [f = 0]. *)
Definition spin (s : state) (k : pcfg) : Prop :=
  exists i, i <= 2 /\ k = (PPar (t1 i) (t2 0), s).

(** IL⊥: divergence is reachable from [f = 0]: the writer is starved. *)
Theorem mp_IL_bot :
  ILbv pact_sem ⊢⊥ ⟦ pre0 ⟧ penc mp
                   ⟦ fun o => pfinB o /\ option_map snd o = None ⟧.
Proof.
  set (s0 := empty_state).
  apply (ilb_cons _ _ _ (fun o => o = Some (PSkip, s0)) _
           (fun o => o = None));
    [intros o ->; reflexivity | |
     intros [k|] [_ E]; [discriminate | reflexivity]].
  apply (ilb_seq _ _ _ (fun o => o = Some (mp, s0))).
  - refine (ilb_cons _ _ _ _ _ _ _ _
              (ilb_act pact_sem (ILbv pact_sem)
                 (fun o => o = Some (PSkip, s0)) (SLoad mp)) _);
      [intros o H; exact H |].
    intros o ->. exists (PSkip, s0). split; reflexivity.
  - apply (ilb_diverge _ _ (spin s0)); [exists 0; split; [lia | reflexivity] |].
    intros k [i [Hi ->]]. split; [unfold running; simpl; discriminate |].
    exists (PPar (t1 (match i with 0 => 1 | 1 => 2 | _ => 0 end)) (t2 0), s0).
    split.
    + exists (match i with 0 => 1 | 1 => 2 | _ => 0 end).
      split; [destruct i as [|[|]]; lia | reflexivity].
    + refine (ilb_cons _ _ _ _ _ _ _ _
                (ilb_act pact_sem (ILbv pact_sem)
                   (fun o => o = Some (PPar (t1 i) (t2 0), s0)) SStep) _);
        [intros o H; exact H |].
      intros o ->. exists (PPar (t1 i) (t2 0), s0). split; [reflexivity |].
      destruct i as [|[|[|i]]]; try lia; simpl; repeat constructor.
Qed.

(** NC⊥: divergence needs [f = 0]. Proved on the complemented triple, as
    total correctness from [f ≠ 0]: complement to p̃re ⊇⊥, then Galois to
    HL⊥. *)
Theorem mp_NC_bot :
  Pb (NCbv pact_sem)
    (fun o => SomeP (fun s => s F = 0) True (option_map snd o)) (penc mp)
    (fun o => pfinB o /\ option_map snd o = None).
Proof.
  apply (vl_transport_compl (NCbv pact_sem) (PreDUbv pact_sem)).
  apply (vl_transport_same (PreDUbv pact_sem) (HLbv pact_sem)
           (fun t => iff_sym (galois_post_wlp t))).
  change (Pb (HLbv pact_sem)
            (fun o => ~ SomeP (fun s => s F = 0) True (option_map snd o))
            (penc mp)
            (fun o => ~ (pfinB o /\ option_map snd o = None))).
  apply (hlb_cons _ _ _ (som (fun k => snd k F <> 0)) _
           (som (fun _ => True))); [| exact mp_HL_bot_total |].
  - intros [k|] H; simpl in *; [exact H | exfalso; apply H; exact I].
  - intros [k|] H; simpl in *; [intros [_ E]; discriminate | contradiction].
Qed.

(** SIL⊥: from every state with [f = 0], some schedule diverges. *)
Theorem mp_SIL_bot :
  Pb (SILbv pact_sem) pre0 (penc mp)
    (fun o => pfinB o /\ option_map snd o = None).
Proof.
  set (J := fun k : pcfg => exists i, i <= 2 /\
              fst k = PPar (t1 i) (t2 0) /\ snd k F = 0).
  apply (silb_seq _ _ _ (som J)).
  - refine (silb_cons _ _ _ _ _ _ _ _
              (silb_act pact_sem (SILbv pact_sem) (som J) (SLoad mp)) _);
      [| intros o H; exact H].
    intros [k|] H; simpl in *; [| contradiction].
    exists (mp, snd k). split; [reflexivity |].
    exists 0. split; [lia | split; [reflexivity | exact H]].
  - apply (silb_cons _ _ _ (som J) _ (fun o => o = None));
      [intros o H; exact H | apply silb_diverge |
       intros o ->; split; reflexivity].
    + refine (silb_cons _ _ _ _ _ _ _ _
                (silb_act pact_sem (SILbv pact_sem) (som J) SStep) _);
        [| intros o H; exact H].
      intros [[p s]|] H; simpl in *; [| contradiction].
      destruct H as [i [Hi [Ep Hf]]]. cbn [fst snd] in Ep, Hf. subst p.
      exists (PPar (t1 (match i with 0 => 1 | 1 => 2 | _ => 0 end)) (t2 0), s).
      split.
      * destruct i as [|[|[|i]]]; try lia; simpl; repeat constructor.
        simpl. rewrite Hf. reflexivity.
      * exists (match i with 0 => 1 | 1 => 2 | _ => 0 end).
        split; [destruct i as [|[|]]; lia | split; [reflexivity | exact Hf]].
    + intros k [i [_ [Ep _]]]. unfold running. rewrite Ep. discriminate.
Qed.

(** p̃ost ⊆⊥ via IL⊥ on the complemented triple: ⊥ is reached from
    outside [f ≠ 0]. *)
Theorem mp_PostDO_bot :
  Pb (PostDObv pact_sem)
    (fun o => SomeP (fun s => s F <> 0) True (option_map snd o)) (penc mp)
    (fun o => pfinB o -> SomeP (fun _ => True) False (option_map snd o)).
Proof.
  apply (vl_transport_compl (PostDObv pact_sem) (ILbv pact_sem)).
  change (Pb (ILbv pact_sem)
            (fun o => ~ SomeP (fun s => s F <> 0) True (option_map snd o))
            (penc mp)
            (fun o => ~ (pfinB o ->
                         SomeP (fun _ => True) False (option_map snd o)))).
  apply (ilb_cons _ _ _ pre0 _
           (fun o => pfinB o /\ option_map snd o = None));
    [| exact mp_IL_bot |].
  - intros [k|] H; simpl in *; [intros Hn; contradiction | contradiction].
  - intros [k|] H; simpl in *.
    + exfalso. apply H. intros _. exact I.
    + split; [exact I | reflexivity].
Qed.

Theorem mp_PostDU_bot :
  Pb (PostDUbv pact_sem)
    (fun o => SomeP (fun s => s F = 0) True (option_map snd o)) (penc mp)
    (fun o => pfinB o /\ option_map snd o = None).
Proof.
  apply (vl_transport_same (PostDUbv pact_sem) (NCbv pact_sem)
           (fun t => iff_sym (galois_pre_dimg t))).
  exact mp_NC_bot.
Qed.

(** p̃re ⊆⊥ via SIL⊥ on the complemented triple: every state from which
    all runs terminate has [f ≠ 0]. *)
Theorem mp_PreDO_bot :
  Pb (PreDObv pact_sem)
    (fun o => SomeP (fun s => s F <> 0) True (option_map snd o)) (penc mp)
    (fun o => pfinB o /\ SomeP (fun _ => True) False (option_map snd o)).
Proof.
  apply (vl_transport_compl (PreDObv pact_sem) (SILbv pact_sem)).
  change (Pb (SILbv pact_sem)
            (fun o => ~ SomeP (fun s => s F <> 0) True (option_map snd o))
            (penc mp)
            (fun o => ~ (pfinB o /\
                         SomeP (fun _ => True) False (option_map snd o)))).
  apply (silb_cons _ _ _ pre0 _
           (fun o => pfinB o /\ option_map snd o = None));
    [| exact mp_SIL_bot |].
  - intros [k|] H; simpl in *; [lia | exfalso; apply H; exact I].
  - intros [k|] [_ E]; simpl in *; [discriminate | intros [_ []]].
Qed.

Theorem mp_PreDU_bot :
  Pb (PreDUbv pact_sem) pre0 (penc mp)
    (fun o => pfinB o /\
       SomeP (fun s => s Y = 42) True (option_map snd o)).
Proof.
  apply (vl_transport_same (PreDUbv pact_sem) (HLbv pact_sem)
           (fun t => iff_sym (galois_post_wlp t))).
  exact mp_HL_bot.
Qed.

(** ** Back to the concurrent program itself

    Soundness of each record turns a proof above into validity of the
    encoded triple, and [penc_cvalid] / [penc_cvalid_bot] transfer it to
    [mp] under the interleaving semantics. *)

Corollary mp_correct :
  cvalid Forward Plain Over
    (@mkTriple ParImp (fun s => s F = 0) mp (fun s => s Y = 42)).
Proof. apply (penc_cvalid Forward Plain Over), (vl_valid_of _ _ mp_HL). Qed.

Corollary mp_delivery_reachable :
  cvalid Forward Plain Under (@mkTriple ParImp (fun s => s F = 0) mp Done).
Proof. apply (penc_cvalid Forward Plain Under), (vl_valid_of _ _ mp_IL). Qed.

Corollary mp_miss_needs_flag :
  cvalid Backward Plain Over
    (@mkTriple ParImp (fun s => s F <> 0) mp (fun s => s Y <> 42)).
Proof. apply (penc_cvalid Backward Plain Over), (vl_valid_of _ _ mp_NC). Qed.

Corollary mp_delivery_possible :
  cvalid Backward Plain Under
    (@mkTriple ParImp (fun _ => True) mp (fun s => s Y = 42)).
Proof.
  apply (penc_cvalid Backward Plain Under), (vl_valid_of _ _ mp_SIL).
Qed.

Corollary mp_partial_bot :
  cvalid Forward Plain Over
    (@mkTriple ParImpB (SomeP (fun s => s F = 0) False) mp
       (SomeP (fun s => s Y = 42) True)).
Proof.
  apply (penc_cvalid_bot Forward Plain Over), (vl_valid_of _ _ mp_HL_bot).
Qed.

Corollary mp_starvation :
  cvalid Forward Plain Under
    (@mkTriple ParImpB (SomeP (fun s => s F = 0) False) mp
       (fun o => o = None)).
Proof.
  apply (penc_cvalid_bot Forward Plain Under), (vl_valid_of _ _ mp_IL_bot).
Qed.

Corollary mp_divergence_needs_flag :
  cvalid Backward Plain Over
    (@mkTriple ParImpB (SomeP (fun s => s F = 0) True) mp
       (fun o => o = None)).
Proof.
  apply (penc_cvalid_bot Backward Plain Over), (vl_valid_of _ _ mp_NC_bot).
Qed.

Corollary mp_can_diverge :
  cvalid Backward Plain Under
    (@mkTriple ParImpB (SomeP (fun s => s F = 0) False) mp
       (fun o => o = None)).
Proof.
  apply (penc_cvalid_bot Backward Plain Under), (vl_valid_of _ _ mp_SIL_bot).
Qed.
