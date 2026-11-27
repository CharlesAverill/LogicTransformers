(** * A heap language, faults, and the frame rule

    Separation logic, generated. The language is an instance of the
    core: states are a store and a heap, or a fault [None]; atoms are
    assignment, load, store, allocation and deallocation, and touching
    an unallocated cell faults. Its sixteen logics are generated like
    any other language's.

    - [slv P c Q]: separation logic's fault-avoiding partial correctness
      is the Hoare corner, with faults excluded from the postcondition
      ([slv_iff]).
    - [star], [pts], [wand]: separation is a choice of assertions over
      the heap; the cube does not need to know about it.
    - [frame_prop]: every command is *local*: a run from a larger heap
      either is a run from the smaller heap with the extra cells
      untouched, or the smaller heap faults. Proved once, from the
      locality of each atom ([atom_local]).
    - [frame_rule]: so the frame rule holds in *every* generated Hoare
      logic for this language: from [{P} c {Q}] infer
      [{P * F} c {Q * F}] when [c] writes no store variable [F] reads.

    The frame rule is not generated with the logic: it is a rule about
    the generated logics, licensed by a semantic fact (locality), as the
    atom rules of other languages are licensed by what their atoms do.
    It holds for the Hoare corner. For incorrectness logic it fails in
    this plain heap model (a freed cell may reappear in the frame), which
    is why incorrectness separation logic adds negative heap assertions.

    Heaps are compared as functions, so the proofs use
    [functional_extensionality]. *)

From Stdlib Require Import String List Arith Lia FunctionalExtensionality.
From LogicTransformers.Imp Require Import Syntax Hoare.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Verified.
From LogicTransformers.Core Require Import Kernel Rules.
Import ListNotations.

(** ** Heaps *)

Definition heap := nat -> option nat.
Definition hstate := (state * heap)%type.

Definition hupd (h : heap) (l : nat) (v : option nat) : heap :=
  fun l' => if Nat.eqb l' l then v else h l'.

Definition disj (h1 h2 : heap) : Prop := forall l, h1 l = None \/ h2 l = None.

Definition hunion (h1 h2 : heap) : heap :=
  fun l => match h1 l with Some v => Some v | None => h2 l end.

Lemma hupd_eq : forall h l v, hupd h l v l = v.
Proof. intros. unfold hupd. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma hupd_ne : forall h l v l', l' <> l -> hupd h l v l' = h l'.
Proof.
  intros. unfold hupd. destruct (Nat.eqb_spec l' l); [lia | reflexivity].
Qed.

Lemma hunion_l : forall h1 h2 l v, h1 l = Some v -> hunion h1 h2 l = Some v.
Proof. intros. unfold hunion. rewrite H. reflexivity. Qed.

Lemma hunion_r : forall h1 h2 l, h1 l = None -> hunion h1 h2 l = h2 l.
Proof. intros. unfold hunion. rewrite H. reflexivity. Qed.

(** Updating a cell of the left part. *)
Lemma hupd_hunion : forall h h1 l v, h1 l = None ->
    hupd (hunion h h1) l v = hunion (hupd h l v) h1.
Proof.
  intros h h1 l v H. apply functional_extensionality. intros l'.
  unfold hupd, hunion. destruct (Nat.eqb_spec l' l) as [-> |]; [| reflexivity].
  destruct v; [reflexivity | symmetry; exact H].
Qed.

Lemma disj_hupd : forall h h1 l v, disj h h1 -> h1 l = None ->
    disj (hupd h l v) h1.
Proof.
  intros h h1 l v D H l'. unfold hupd.
  destruct (Nat.eqb_spec l' l) as [-> |]; [right; exact H | apply D].
Qed.

(** ** The language *)

Inductive hact : Type :=
  | HAsgn (x : var) (a : aexp)
  | HLoad (x : var) (a : aexp)
  | HStore (a1 a2 : aexp)
  | HAlloc (x : var)
  | HFree (a : aexp).

(** [None] is a fault; faults are final. *)
Definition hsem (c : hact) (r r' : option hstate) : Prop :=
  match r with
  | None => r' = None
  | Some (s, h) =>
      match c with
      | HAsgn x a => r' = Some (update s x (aeval s a), h)
      | HLoad x a =>
          match h (aeval s a) with
          | Some v => r' = Some (update s x v, h)
          | None => r' = None
          end
      | HStore a1 a2 =>
          match h (aeval s a1) with
          | Some _ => r' = Some (s, hupd h (aeval s a1) (Some (aeval s a2)))
          | None => r' = None
          end
      | HAlloc x =>
          exists l, h l = None /\ r' = Some (update s x l, hupd h l (Some 0))
      | HFree a =>
          match h (aeval s a) with
          | Some _ => r' = Some (s, hupd h (aeval s a) None)
          | None => r' = None
          end
      end
  end.

Inductive hcmd : Type :=
  | CSkip'
  | CAct (a : hact)
  | CSeq' (c1 c2 : hcmd)
  | CIf' (b : bexp) (c1 c2 : hcmd)
  | CWhile' (b : bexp) (c : hcmd).

(** Tests read the store only, and let faults through. *)
Definition test (b : bexp) (r : option hstate) : Prop :=
  match r with Some (s, _) => bassn b s | None => True end.
Definition ntest (b : bexp) (r : option hstate) : Prop :=
  match r with Some (s, _) => ~ bassn b s | None => True end.

Fixpoint enc (c : hcmd) : kcom (option hstate) hact :=
  match c with
  | CSkip' => KSkip
  | CAct a => KAct a
  | CSeq' c1 c2 => KSeq (enc c1) (enc c2)
  | CIf' b c1 c2 =>
      KChoice (KSeq (KAssume (test b)) (enc c1))
              (KSeq (KAssume (ntest b)) (enc c2))
  | CWhile' b c =>
      KSeq (KStar (KSeq (KAssume (test b)) (enc c))) (KAssume (ntest b))
  end.

Notation hkev := (kev hsem).

(** ** Separation logic's validity is the Hoare corner *)

Definition hprop := state -> heap -> Prop.

Definition lift (P : hprop) (r : option hstate) : Prop :=
  match r with Some (s, h) => P s h | None => False end.

Definition slv (P : hprop) (c : hcmd) (Q : hprop) : Prop :=
  forall s h, P s h -> forall r, hkev (enc c) (Some (s, h)) r -> lift Q r.

Section Generated.

Variable V : VLogic (KLang hsem) Forward Plain Over.

Definition sl (P : hprop) (c : hcmd) (Q : hprop) : Prop :=
  prov hsem V (lift P) (enc c) (lift Q).

Theorem slv_iff : forall P c Q, sl P c Q <-> slv P c Q.
Proof.
  intros P c Q. unfold sl. rewrite hl_iff. split.
  - intros H s h HP r Hk. exact (H (Some (s, h)) r HP Hk).
  - intros H [[s h] |] r HP Hk; [exact (H s h HP r Hk) | contradiction].
Qed.

End Generated.

(** ** Assertions *)

Definition star (P Q : hprop) : hprop :=
  fun s h => exists h1 h2, disj h1 h2 /\ h = hunion h1 h2 /\ P s h1 /\ Q s h2.

Definition single (l v : nat) : heap :=
  fun l' => if Nat.eqb l' l then Some v else None.

Definition pts (a : aexp) (v : nat) : hprop :=
  fun s h => h = single (aeval s a) v.

Definition wand (P Q : hprop) : hprop :=
  fun s h => forall h', disj h h' -> P s h' -> Q s (hunion h h').

(** ** Locality *)

Lemma atom_local : forall a s h h1 r, disj h h1 ->
    hsem a (Some (s, hunion h h1)) r ->
    hsem a (Some (s, h)) None \/
    exists s' h', r = Some (s', hunion h' h1) /\ disj h' h1 /\
                  hsem a (Some (s, h)) (Some (s', h')).
Proof.
  intros a s h h1 r D H. destruct a as [x e | x e | e1 e2 | x | e]; simpl in *.
  - right. exists (update s x (aeval s e)), h. auto.
  - destruct (h (aeval s e)) as [v |] eqn:E.
    + rewrite (hunion_l h h1 _ v E) in H. right.
      exists (update s x v), h. auto.
    + left. reflexivity.
  - destruct (h (aeval s e1)) as [v |] eqn:E.
    + rewrite (hunion_l h h1 _ v E) in H. right.
      assert (N : h1 (aeval s e1) = None)
        by (destruct (D (aeval s e1)); congruence).
      exists s, (hupd h (aeval s e1) (Some (aeval s e2))).
      split; [rewrite H, hupd_hunion by exact N; reflexivity |].
      split; [apply disj_hupd; assumption | reflexivity].
    + left. reflexivity.
  - destruct H as [l [Hl ->]]. right.
    assert (E1 : h l = None)
      by (unfold hunion in Hl; destruct (h l); congruence).
    assert (E2 : h1 l = None) by (rewrite hunion_r in Hl by exact E1; exact Hl).
    exists (update s x l), (hupd h l (Some 0)).
    split; [rewrite hupd_hunion by exact E2; reflexivity |].
    split; [apply disj_hupd; assumption | exists l; auto].
  - destruct (h (aeval s e)) as [v |] eqn:E.
    + rewrite (hunion_l h h1 _ v E) in H. right.
      assert (N : h1 (aeval s e) = None)
        by (destruct (D (aeval s e)); congruence).
      exists s, (hupd h (aeval s e) None).
      split; [rewrite H, hupd_hunion by exact N; reflexivity |].
      split; [apply disj_hupd; assumption | reflexivity].
    + left. reflexivity.
Qed.

Lemma none_none : forall c, hkev (enc c) None None.
Proof.
  induction c; simpl.
  - apply KE_Skip.
  - apply KE_Act. reflexivity.
  - eapply KE_Seq; eassumption.
  - apply KE_ChoiceL. eapply KE_Seq; [apply KE_Assume; exact I | assumption].
  - eapply KE_Seq; [apply KE_StarRefl | apply KE_Assume; exact I].
Qed.

(** Commands built from local atoms and store-only tests are local. *)
Inductive good : kcom (option hstate) hact -> Prop :=
  | G_Skip : good KSkip
  | G_Act : forall a, good (KAct a)
  | G_Assume : forall B, B None ->
      (forall s h h', B (Some (s, h)) <-> B (Some (s, h'))) -> good (KAssume B)
  | G_Seq : forall k1 k2, good k1 -> good k2 -> good (KSeq k1 k2)
  | G_Choice : forall k1 k2, good k1 -> good k2 -> good (KChoice k1 k2)
  | G_Star : forall k, good k -> good (KStar k).

Lemma good_enc : forall c, good (enc c).
Proof.
  induction c; simpl; repeat constructor; auto; intros s h h'; reflexivity.
Qed.

Lemma good_none : forall k, good k -> hkev k None None.
Proof.
  intros k G. induction G.
  - apply KE_Skip.
  - apply KE_Act. reflexivity.
  - apply KE_Assume. assumption.
  - eapply KE_Seq; eassumption.
  - apply KE_ChoiceL. assumption.
  - apply KE_StarRefl.
Qed.

Theorem frame_prop : forall k r0 r, hkev k r0 r -> good k ->
    forall s h h1, r0 = Some (s, hunion h h1) -> disj h h1 ->
    hkev k (Some (s, h)) None \/
    exists s' h', r = Some (s', hunion h' h1) /\ disj h' h1 /\
                  hkev k (Some (s, h)) (Some (s', h')).
Proof.
  intros k r0 r H. induction H; intros G s0 h h1 E D; subst.
  - right. exists s0, h.
    split; [reflexivity | split; [exact D | apply KE_Skip]].
  - destruct (atom_local a s0 h h1 s' D H) as [F | [s2 [h' [E1 [D1 H1]]]]].
    + left. apply KE_Act, F.
    + right. exists s2, h'. split; [exact E1 | split; [exact D1 |]].
      apply KE_Act, H1.
  - inversion G as [| | ? HN HB | | |]; subst. right. exists s0, h.
    split; [reflexivity | split; [exact D |]].
    apply KE_Assume. apply (proj1 (HB s0 (hunion h h1) h)), H.
  - inversion G as [| | | ? ? G1 G2 | |]; subst.
    destruct (IHkev1 G1 s0 h h1 eq_refl D) as [F | [s1' [h' [E1 [D1 H1]]]]].
    + left. eapply KE_Seq; [exact F | apply good_none; assumption].
    + subst s1.
      destruct (IHkev2 G2 s1' h' h1 eq_refl D1)
        as [F | [s2' [h2 [E2 [D2 H2]]]]].
      * left. eapply KE_Seq; eassumption.
      * right. exists s2', h2. split; [exact E2 | split; [exact D2 |]].
        eapply KE_Seq; eassumption.
  - inversion G as [| | | | ? ? G1 G2 |]; subst.
    destruct (IHkev G1 s0 h h1 eq_refl D) as [F | [sx [h' [E1 [D1 H1]]]]].
    + left. apply KE_ChoiceL, F.
    + right. exists sx, h'. split; [exact E1 | split; [exact D1 |]].
      apply KE_ChoiceL, H1.
  - inversion G as [| | | | ? ? G1 G2 |]; subst.
    destruct (IHkev G2 s0 h h1 eq_refl D) as [F | [sx [h' [E1 [D1 H1]]]]].
    + left. apply KE_ChoiceR, F.
    + right. exists sx, h'. split; [exact E1 | split; [exact D1 |]].
      apply KE_ChoiceR, H1.
  - right. exists s0, h.
    split; [reflexivity | split; [exact D | apply KE_StarRefl]].
  - pose proof G as G'. inversion G as [| | | | | ? G1]; subst.
    destruct (IHkev1 G1 s0 h h1 eq_refl D) as [F | [s1' [h' [E1 [D1 H1]]]]].
    + left. eapply KE_StarStep; [exact F | apply good_none; exact G'].
    + subst s1.
      destruct (IHkev2 G' s1' h' h1 eq_refl D1)
        as [F | [s2' [h2 [E2 [D2 H2]]]]].
      * left. eapply KE_StarStep; eassumption.
      * right. exists s2', h2. split; [exact E2 | split; [exact D2 |]].
        eapply KE_StarStep; eassumption.
Qed.

(** ** Which store variables a command writes *)

Definition awr (a : hact) : list var :=
  match a with
  | HAsgn x _ | HLoad x _ | HAlloc x => [x]
  | _ => []
  end.

Fixpoint wr (c : hcmd) : list var :=
  match c with
  | CSkip' => []
  | CAct a => awr a
  | CSeq' c1 c2 | CIf' _ c1 c2 => wr c1 ++ wr c2
  | CWhile' _ c => wr c
  end.

Inductive kwr (W : list var) : kcom (option hstate) hact -> Prop :=
  | W_Skip : kwr W KSkip
  | W_Act : forall a, incl (awr a) W -> kwr W (KAct a)
  | W_Assume : forall B, kwr W (KAssume B)
  | W_Seq : forall k1 k2, kwr W k1 -> kwr W k2 -> kwr W (KSeq k1 k2)
  | W_Choice : forall k1 k2, kwr W k1 -> kwr W k2 -> kwr W (KChoice k1 k2)
  | W_Star : forall k, kwr W k -> kwr W (KStar k).

Lemma kwr_enc : forall c, kwr (wr c) (enc c).
Proof.
  assert (M : forall W W' k, incl W W' -> kwr W k -> kwr W' k).
  { intros W W' k I H. induction H; constructor; auto.
    eapply incl_tran; eassumption. }
  assert (L : forall W1 W2 k, kwr W1 k -> kwr (W1 ++ W2) k)
    by (intros W1 W2 k H; eapply M; [| exact H]; intros x Hx;
        apply in_or_app; auto).
  assert (Rt : forall W1 W2 k, kwr W2 k -> kwr (W1 ++ W2) k)
    by (intros W1 W2 k H; eapply M; [| exact H]; intros x Hx;
        apply in_or_app; auto).
  induction c; simpl.
  - constructor.
  - constructor. apply incl_refl.
  - constructor; [apply L | apply Rt]; assumption.
  - constructor; constructor; [constructor | apply L | constructor
                               | apply Rt]; assumption.
  - constructor; [do 2 constructor; [constructor | assumption] |].
    constructor.
Qed.

Lemma none_final : forall k r r', hkev k r r' -> r = None -> r' = None.
Proof.
  intros k r r' H. induction H; intros E; subst; auto.
Qed.

Lemma store_frame : forall W k r r', hkev k r r' -> kwr W k ->
    forall s h s' h', r = Some (s, h) -> r' = Some (s', h') ->
    forall x, ~ In x W -> s' x = s x.
Proof.
  intros W k r r' H. induction H; intros Kw s0 h0 sf hf E E' x Hx; subst.
  - injection E'; intros; subst. reflexivity.
  - inversion Kw; subst. destruct a as [y e | y e | e1 e2 | y | e];
      simpl in H.
    + injection H; intros; subst. apply update_neq.
      intros ->. apply Hx, H1. left. reflexivity.
    + destruct (h0 (aeval s0 e)); [| discriminate].
      injection H; intros; subst. apply update_neq.
      intros ->. apply Hx, H1. left. reflexivity.
    + destruct (h0 (aeval s0 e1)); [| discriminate].
      injection H; intros; subst. reflexivity.
    + destruct H as [l [_ E]]. injection E; intros; subst.
      apply update_neq. intros ->. apply Hx, H1. left. reflexivity.
    + destruct (h0 (aeval s0 e)); [| discriminate].
      injection H; intros; subst. reflexivity.
  - injection E'; intros; subst. reflexivity.
  - inversion Kw as [| | | ? ? K1 K2 | |]; subst.
    destruct s1 as [[sm hm] |].
    + rewrite (IHkev2 K2 sm hm sf hf eq_refl eq_refl x Hx).
      exact (IHkev1 K1 s0 h0 sm hm eq_refl eq_refl x Hx).
    + discriminate (none_final _ _ _ H0 eq_refl).
  - inversion Kw; subst. eapply IHkev; eauto.
  - inversion Kw; subst. eapply IHkev; eauto.
  - injection E'; intros; subst. reflexivity.
  - pose proof Kw as Kw'. inversion Kw as [| | | | | ? K1]; subst.
    destruct s1 as [[sm hm] |].
    + rewrite (IHkev2 Kw' sm hm sf hf eq_refl eq_refl x Hx).
      exact (IHkev1 K1 s0 h0 sm hm eq_refl eq_refl x Hx).
    + discriminate (none_final _ _ _ H0 eq_refl).
Qed.

(** ** The frame rule *)

(** [F] reads no store variable in [W]. *)
Definition indep (W : list var) (F : hprop) : Prop :=
  forall s s' h, (forall x, ~ In x W -> s' x = s x) -> F s h -> F s' h.

Theorem frame_valid : forall P c Q F, indep (wr c) F ->
    slv P c Q -> slv (star P F) c (star Q F).
Proof.
  intros P c Q F HF V s h [h0 [h1 [D [-> [HP HFh]]]]] r Hk.
  destruct (frame_prop _ _ _ Hk (good_enc c) s h0 h1 eq_refl D)
    as [Fault | [s' [h' [-> [D' Hk']]]]].
  - destruct (V s h0 HP None Fault).
  - simpl. exists h', h1. split; [exact D' | split; [reflexivity |]].
    split; [exact (V s h0 HP _ Hk') |].
    apply (HF s s' h1); [| exact HFh].
    exact (store_frame (wr c) _ _ _ Hk' (kwr_enc c) s h0 s' h'
             eq_refl eq_refl).
Qed.

Section FrameRule.

Variable V : VLogic (KLang hsem) Forward Plain Over.

(** The frame rule, in any generated Hoare logic for the heap language. *)
Theorem frame_rule : forall P c Q F, indep (wr c) F ->
    sl V P c Q -> sl V (star P F) c (star Q F).
Proof.
  intros P c Q F HF H. apply slv_iff. apply slv_iff in H.
  apply frame_valid; assumption.
Qed.

End FrameRule.

(** ** Heap algebra *)

Lemma hunion_comm : forall h1 h2, disj h1 h2 -> hunion h1 h2 = hunion h2 h1.
Proof.
  intros h1 h2 D. apply functional_extensionality. intros l. unfold hunion.
  destruct (D l) as [E | E]; rewrite E; destruct (h1 l), (h2 l);
    congruence.
Qed.

Lemma disj_sym : forall h1 h2, disj h1 h2 -> disj h2 h1.
Proof. intros h1 h2 D l. destruct (D l); auto. Qed.

Lemma star_comm : forall P Q s h, star P Q s h -> star Q P s h.
Proof.
  intros P Q s h [h1 [h2 [D [-> [HP HQ]]]]]. exists h2, h1.
  split; [apply disj_sym, D |]. split; [apply hunion_comm, D |]. auto.
Qed.

Lemma star_mono : forall (P P' Q Q' : hprop) s h,
    (forall s h, P s h -> P' s h) -> (forall s h, Q s h -> Q' s h) ->
    star P Q s h -> star P' Q' s h.
Proof.
  intros P P' Q Q' s h HP HQ [h1 [h2 [D [E [H1 H2]]]]].
  exists h1, h2. auto.
Qed.

(** Store-only facts may be copied into both halves. *)
Definition pure (phi : state -> Prop) (P : hprop) : hprop :=
  fun s h => phi s /\ P s h.

Lemma star_share : forall phi P Q s h, phi s -> star P Q s h ->
    star (pure phi P) (pure phi Q) s h.
Proof.
  intros phi P Q s h Hp [h1 [h2 [D [E [H1 H2]]]]].
  exists h1, h2. unfold pure. auto.
Qed.

(** ** Small axioms and structural rules, in any generated Hoare logic *)

Section SmallAxioms.

Variable V : VLogic (KLang hsem) Forward Plain Over.
Local Notation sl := (sl V).

Lemma sl_cons : forall (P P' Q Q' : hprop) c,
    (forall s h, P s h -> P' s h) -> (forall s h, Q' s h -> Q s h) ->
    sl P' c Q' -> sl P c Q.
Proof.
  intros P P' Q Q' c HP HQ H. apply slv_iff. apply slv_iff in H.
  intros s h Hp r Hk. specialize (H s h (HP s h Hp) r Hk).
  destruct r as [[s' h'] |]; [apply HQ, H | exact H].
Qed.

Lemma sl_seq : forall P R Q c1 c2,
    sl P c1 R -> sl R c2 Q -> sl P (CSeq' c1 c2) Q.
Proof.
  intros P R Q c1 c2 H1 H2. unfold sl in *. simpl.
  eapply hl_seq; eassumption.
Qed.

(** Load, with a store-only context [R] that does not read [x]. *)
Lemma sl_load : forall (R : state -> Prop) x e v,
    (forall s n, aeval (update s x n) e = aeval s e) ->
    (forall s n, R s -> R (update s x n)) ->
    sl (pure R (pts e v)) (CAct (HLoad x e))
       (fun s h => R s /\ s x = v /\ pts e v s h).
Proof.
  intros R x e v He HR. apply slv_iff.
  intros s h [Hr Hp] r Hk. inversion Hk; subst. simpl in *.
  unfold pts in Hp. subst h.
  assert (E : single (aeval s e) v (aeval s e) = Some v)
    by (unfold single; rewrite Nat.eqb_refl; reflexivity).
  match goal with K : match single _ _ _ with _ => _ end |- _ =>
    rewrite E in K; subst end. simpl.
  split; [apply HR, Hr |]. split; [apply update_eq |].
  unfold pts. rewrite He. reflexivity.
Qed.

(** Store, with a store-only context [R]. *)
Lemma sl_store : forall (R : state -> Prop) e e',
    sl (fun s h => R s /\ exists v, pts e v s h) (CAct (HStore e e'))
       (fun s h => R s /\ pts e (aeval s e') s h).
Proof.
  intros R e e'. apply slv_iff.
  intros s h [Hr [v Hp]] r Hk. inversion Hk; subst. simpl in *.
  unfold pts in Hp. subst h.
  assert (E : single (aeval s e) v (aeval s e) = Some v)
    by (unfold single; rewrite Nat.eqb_refl; reflexivity).
  match goal with K : match single _ _ _ with _ => _ end |- _ =>
    rewrite E in K; subst end. simpl. split; [exact Hr |].
  unfold pts. apply functional_extensionality. intros l.
  unfold hupd, single. destruct (Nat.eqb l (aeval s e)); reflexivity.
Qed.

End SmallAxioms.
