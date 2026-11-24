(** * Tutorial: instantiating the framework with Imp

    The companion file to [tutorial/README.md]. Imp's small-step semantics
    ([Imp.SmallStep]) is plugged into the core through
    [Core.SmallStepCore]. A countdown loop is proved with rules at three
    cube nodes, and the results are transferred back to Imp with its
    usual big-step semantics. *)

From Stdlib Require Import String Arith Lia FunctionalExtensionality.
From LogicTransformers.Imp Require Import Syntax BigStep SmallStep Equiv Lang.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Relational Verified.
From LogicTransformers.Core Require Import
  Kernel KernelBot SmallStepCore Rules RulesBot.
From LogicTransformers.Examples Require Import Common.
From LogicTransformers.Core Require Import TripleNotations.

Local Open Scope com_scope.
Local Open Scope string_scope.
Local Open Scope triple_scope.

(** ** Step 1: the step relation, on configurations *)

Definition istep (k k' : com * state) : Prop :=
  cstep (fst k) (snd k) (fst k') (snd k').

(** ** Step 2: the two requirements *)

Lemma skip_stuck : forall s k', ~ istep (CSkip, s) k'.
Proof. intros s [c' s'] H. inversion H. Qed.

Lemma skip_dec : forall c, c = CSkip \/ c <> CSkip.
Proof. intros []; (left; reflexivity) || (right; discriminate). Qed.

(** ** Step 3: the language, its encoding, and the transfer theorems *)

Definition ImpS : Language := SLang istep CSkip.
Definition ImpSB : Language := SLangB istep CSkip.

Definition isem := sact_sem istep.
Definition ienc : com -> kcom (com * state) (sact com) := senc CSkip.
Notation irunning := (@running com state CSkip).
Notation ifin := (@fin com state CSkip).
Notation ifinB := (@finB com state CSkip).

(** [ImpS] is Imp's usual semantics. *)
Lemma smulti_cmulti : forall k k',
    smulti istep k k' <-> cmulti (fst k) (snd k) (fst k') (snd k').
Proof.
  intros k k'. split.
  - intros H. induction H; [apply MS_Refl |].
    eapply MS_Step; [exact H | exact IHsmulti].
  - destruct k as [c s], k' as [c' s']. simpl. intros H.
    induction H; [apply SM_Refl |].
    apply (SM_Step istep _ (c', st')); [exact H | exact IHcmulti].
Qed.

Lemma ImpS_Imp : forall c s s', sem ImpS c s s' <-> sem Imp c s s'.
Proof.
  intros c s s'. simpl. rewrite smulti_cmulti, big_small_equiv. reflexivity.
Qed.

(** Transfer between Imp (big-step) and the encoded program. *)
Theorem ienc_cvalid : forall d p a (P Q : state -> Prop) c,
    cvalid d p a (@mkTriple Imp P c Q) <->
    cvalid d p a (@mkTriple (KLang isem) (fun k => P (snd k)) (ienc c)
                    (liftG snd ifin d p a Q)).
Proof.
  intros d p a P Q c.
  transitivity (cvalid d p a (@mkTriple ImpS P c Q));
    [| apply senc_cvalid; [exact skip_stuck | exact skip_dec]].
  rewrite !cvalid_cvr. split; apply cvr_transfer; intros s s';
    rewrite ImpS_Imp; reflexivity.
Qed.

Theorem ienc_cvalid_bot : forall d p a (P Q : option state -> Prop) c,
    cvalid d p a (@mkTriple ImpSB P c Q) <->
    cvalid d p a (@mkTriple (KLangB isem)
                    (fun o => P (option_map snd o)) (ienc c)
                    (liftG (option_map snd) ifinB d p a Q)).
Proof. intros. apply senc_cvalid_bot; [exact skip_stuck | exact skip_dec]. Qed.

(** ** Step 4: a program and its proofs *)

Local Notation g := (BNot (BLe (AVar "x") (ANum 0))).
Local Notation A := (CAsgn "x" (AMinus (AVar "x") (ANum 1))).
Local Notation W := (CWhile g A).

Definition countdown : com := <{ while "x" > 0 do "x" := "x" - 1 end }>.

Lemma countdown_eq : countdown = W.
Proof. reflexivity. Qed.

(** The loop invariant: where the program can be, and that it only
    finishes with [x = 0]. *)
Definition I (k : com * state) : Prop :=
  fst k = W \/ fst k = CIf g (CSeq A W) CSkip \/ fst k = CSeq A W \/
  fst k = CSeq CSkip W \/ (fst k = CSkip /\ snd k "x" = 0).

Lemma I_step : forall k k', I k -> istep k k' -> I k'.
Proof.
  intros [c s] [c' s'] HI H. unfold I, istep in *. simpl in *.
  destruct HI as [E | [E | [E | [E | [E Hx]]]]]; subst c;
    inversion H; clear H; subst;
    try match goal with H' : cstep _ _ _ _ |- _ => inversion H'; subst end;
    try match goal with
        | Hb : beval _ _ = false |- _ =>
            simpl in Hb; apply Bool.negb_false_iff, Nat.leb_le in Hb
        end;
    intuition (try reflexivity; try lia).
Qed.

(** HL: [countdown] always ends with [x = 0]. *)
Theorem countdown_HL :
  HLv isem ⊢ {{ fun k => True }} ienc countdown
             {{ fun k => fst k = CSkip /\ snd k "x" = 0 }}.
Proof.
  apply (hl_seq _ _ _ I).
  - apply (hl_cons _ _ _
             (fun k => forall k', isem (SLoad countdown) k k' -> I k') _ I);
      [| apply hl_act | intros k H; exact H].
    intros k _ k' E. simpl in E. subst k'. left. reflexivity.
  - apply (hl_cons _ _ _ I _ (fun k => I k /\ ~ irunning k));
      [intros k H; exact H | apply hl_while |].
    + apply (hl_cons _ _ _ (fun k => forall k', isem SStep k k' -> I k')
               _ I); [| apply hl_act | intros k H; exact H].
      intros k [HI _] k' Hs. exact (I_step k k' HI Hs).
    + intros k [HI Hn]. unfold I in HI.
      destruct HI as [E | [E | [E | [E | H]]]]; try exact H;
        exfalso; apply Hn; unfold running; rewrite E; discriminate.
Qed.

(** IL: every state with [x = 0] is the end of a run from a state with
    [x = 1]. For a target [s'], the run starts at [pre1 s'], and
    [d m s'] is the configuration after [m] steps. *)
Definition pre1 (s' : state) : state := update s' "x" 1.
Definition post1 (s' : state) : state :=
  update (pre1 s') "x" (aeval (pre1 s') (AMinus (AVar "x") (ANum 1))).

Definition d (m : nat) (s' : state) : com * state :=
  match m with
  | 0 => (W, pre1 s')
  | 1 => (CIf g (CSeq A W) CSkip, pre1 s')
  | 2 => (CSeq A W, pre1 s')
  | 3 => (CSeq CSkip W, post1 s')
  | 4 => (W, post1 s')
  | 5 => (CIf g (CSeq A W) CSkip, post1 s')
  | _ => (CSkip, post1 s')
  end.

Lemma d_step : forall m s', m < 6 -> istep (d m s') (d (S m) s').
Proof.
  intros m s' Hm. unfold istep.
  destruct m as [|[|[|[|[|[|m]]]]]]; try lia; simpl; repeat constructor.
Qed.

(** Imp states are functions, so landing on exactly [s'] needs
    [functional_extensionality]. *)
Lemma post1_eq : forall s', s' "x" = 0 -> post1 s' = s'.
Proof.
  intros s' Hx. apply functional_extensionality. intros z.
  unfold post1, pre1, update.
  destruct (String.eqb_spec "x" z); [subst; simpl; lia | reflexivity].
Qed.

Theorem countdown_IL :
  ILv isem ⊢ ⟦ fun k => snd k "x" = 1 ⟧ ienc countdown
             ⟦ fun k => fst k = CSkip /\ snd k "x" = 0 ⟧.
Proof.
  set (X := fun m k => m <= 6 /\ exists s', s' "x" = 0 /\ k = d m s').
  apply (il_seq _ _ _ (X 0)).
  - apply (il_cons _ _ _ (fun k => snd k "x" = 1) _
             (fun k' => exists k, snd k "x" = 1 /\
                                  isem (SLoad countdown) k k'));
      [intros k H; exact H | apply il_act |].
    intros k' [_ [s' [_ ->]]]. exists (CSkip, pre1 s').
    split; reflexivity.
  - apply (il_cons _ _ _ (X 0) _
             (fun k => exists m, X m k /\ ~ irunning k));
      [intros k H; exact H | apply il_while |].
    + intros m.
      apply (il_cons _ _ _ (fun k => X m k /\ irunning k) _
               (fun k' => exists k, (X m k /\ irunning k) /\
                                    isem SStep k k'));
        [intros k H; exact H | apply il_act |].
      intros k' [Hm [s' [Hx ->]]]. exists (d m s'). split; [split |].
      * split; [lia | exists s'; auto].
      * destruct m as [|[|[|[|[|[|m]]]]]]; try lia; unfold running; simpl;
          discriminate.
      * apply d_step. lia.
    + intros [c s'] [Ec Hx]. simpl in Ec, Hx. subst c. exists 6.
      split; [split; [lia | exists s'; split; [exact Hx |]] |].
      * simpl. rewrite (post1_eq s' Hx). reflexivity.
      * intros Hr. apply Hr. reflexivity.
Qed.

(** A dual node by transport: p̃re ⊇ is HL's Galois partner. *)
Theorem countdown_PreDU :
  prov isem (PreDUv isem) (fun k => True) (ienc countdown)
    (fun k => fst k = CSkip /\ snd k "x" = 0).
Proof.
  apply (vl_transport_same (PreDUv isem) (HLv isem)
           (fun t => iff_sym (galois_post_wlp t))).
  exact countdown_HL.
Qed.

(** ** Step 5: back to Imp *)

Corollary countdown_correct :
  cvalid Forward Plain Over
    (@mkTriple Imp (fun _ => True) countdown (fun s => s "x" = 0)).
Proof.
  apply (ienc_cvalid Forward Plain Over), (vl_valid_of _ _ countdown_HL).
Qed.

Corollary countdown_reaches_zero :
  cvalid Forward Plain Under
    (@mkTriple Imp (fun s => s "x" = 1) countdown (fun s => s "x" = 0)).
Proof.
  apply (ienc_cvalid Forward Plain Under), (vl_valid_of _ _ countdown_IL).
Qed.
