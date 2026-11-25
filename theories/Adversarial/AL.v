(** * Adversarial logic, single thread

    Vanegue's adversarial logic (SAS 2022) reasons about a *victim*
    program and an *adversary* that interact through channels, and asks
    which bad outcomes the adversary can reach. It is under-approximate:
    a triple [[P] c [Q]] says every state in [Q] is the end of a run of
    [c] from a state in [P].

    This file builds the language and its single-thread logic natively,
    following Averill's ILAL formalization as a guide:
    - a state has a victim half and an adversary half, each a store and
      channels ([estate]);
    - atoms (assign, rand, read, write, [adv_assert]) run in a *mode*
      ([Victim] or [Adversary]) that says which half they touch
      ([asem]);
    - thread commands ([tcom]) add skip, assume, sequencing, choice,
      iteration and [local], and translate into the core ([tenc]).

    Only the language is defined here; the logic is generated.
    [Examples.Common] turns any core language into all sixteen corners:
    it generates HL from the semantics, and every other corner, IL
    included ([vto]), by a transformer. Single-thread adversarial logic
    is the generated IL record [ALv m], and its soundness and
    completeness ([al_valid_iff]) are fields of that record. The other
    corners come with it: for example [ALsil m] is SIL for adversarial
    programs ("from these states, every run can reach the outcome").

    Proofs use the generic rules of [Core.Rules], which hold for every
    language, with facts about what each atom does ([asem_read],
    [asem_assign], ...) as side conditions. Vanegue's own rule
    statements ([al_assign], [al_read], [al_write], [al_adv_success],
    [al_local], ...) are checked to hold in any IL record for the atoms.

    Updating a store or channel to the value it already has is an
    equality of functions, so the atom rules use
    [functional_extensionality], as ILAL does. The generated records
    use [classic], through [Examples.Common]. *)

From Stdlib Require Import String List NArith FunctionalExtensionality.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Verified.
From LogicTransformers.Core Require Import Kernel Rules.
From LogicTransformers.Examples Require Import Common.
Import ListNotations.

(** ** States *)

Definition store := string -> N.
Definition chans := string -> list N.

Record estate := mkE { vs : store; vch : chans; avs : store; ach : chans }.

Inductive mode := Victim | Adversary.

Definition supd (s : store) (x : string) (v : N) : store :=
  fun y => if String.eqb x y then v else s y.
Definition cupd (c : chans) (x : string) (l : list N) : chans :=
  fun y => if String.eqb x y then l else c y.

Definition mstore (m : mode) (σ : estate) : store :=
  match m with Victim => vs σ | Adversary => avs σ end.
Definition mchan (m : mode) (σ : estate) : chans :=
  match m with Victim => vch σ | Adversary => ach σ end.
Definition mupd (m : mode) (σ : estate) (x : string) (v : N) : estate :=
  match m with
  | Victim => mkE (supd (vs σ) x v) (vch σ) (avs σ) (ach σ)
  | Adversary => mkE (vs σ) (vch σ) (supd (avs σ) x v) (ach σ)
  end.
Definition mchupd (m : mode) (σ : estate) (c : string) (l : list N)
  : estate :=
  match m with
  | Victim => mkE (vs σ) (cupd (vch σ) c l) (avs σ) (ach σ)
  | Adversary => mkE (vs σ) (vch σ) (avs σ) (cupd (ach σ) c l)
  end.

(** ** Atoms and commands *)

Inductive atom : Type :=
  | AAsgn (x : string) (e : store -> N)
  | ARand (x : string)
  | ARead (c x : string)
  | AWrite (c x : string)
  | AAdvAssert (B : store -> Prop).

Definition asem (m : mode) (a : atom) (σ σ' : estate) : Prop :=
  match a with
  | AAsgn x e => σ' = mupd m σ x (e (mstore m σ))
  | ARand x => exists v, σ' = mupd m σ x v
  | ARead c x => exists v l, mchan m σ c = v :: l /\
                             σ' = mchupd m (mupd m σ x v) c l
  | AWrite c x => σ' = mchupd m σ c (mchan m σ c ++ [mstore m σ x])
  | AAdvAssert B => m = Adversary /\ σ' = σ
  end.

Inductive tcom : Type :=
  | TSkip
  | TAtom (a : atom)
  | TAssume (B : store -> Prop)
  | TSeq (c1 c2 : tcom)
  | TChoice (c1 c2 : tcom)
  | TStar (c : tcom)
  | TLocal (x : string) (e : store -> N) (c : tcom).

Definition massume (m : mode) (B : store -> Prop) : estate -> Prop :=
  fun σ => B (mstore m σ).

(** [local x = e in c]: set [x] to [e], run [c], and leave [x]
    arbitrary on exit, as in ILAL's [EDLocal]. *)
Fixpoint tenc (m : mode) (c : tcom) : kcom estate atom :=
  match c with
  | TSkip => KSkip
  | TAtom a => KAct a
  | TAssume B => KAssume (massume m B)
  | TSeq c1 c2 => KSeq (tenc m c1) (tenc m c2)
  | TChoice c1 c2 => KChoice (tenc m c1) (tenc m c2)
  | TStar c => KStar (tenc m c)
  | TLocal x e c => KSeq (KAct (AAsgn x e)) (KSeq (tenc m c) (KAct (ARand x)))
  end.

(** ** Update laws *)

Lemma supd_same : forall s x, supd s x (s x) = s.
Proof.
  intros s x. apply functional_extensionality. intros y. unfold supd.
  destruct (String.eqb_spec x y); subst; reflexivity.
Qed.

Lemma supd_supd : forall s x v w, supd (supd s x v) x w = supd s x w.
Proof.
  intros s x v w. apply functional_extensionality. intros y. unfold supd.
  destruct (String.eqb x y); reflexivity.
Qed.

Lemma cupd_same : forall c x, cupd c x (c x) = c.
Proof.
  intros c x. apply functional_extensionality. intros y. unfold cupd.
  destruct (String.eqb_spec x y); subst; reflexivity.
Qed.

Lemma cupd_cupd : forall c x l l', cupd (cupd c x l) x l' = cupd c x l'.
Proof.
  intros c x l l'. apply functional_extensionality. intros y. unfold cupd.
  destruct (String.eqb x y); reflexivity.
Qed.

Lemma supd_eq : forall s x v, supd s x v x = v.
Proof. intros. unfold supd. rewrite String.eqb_refl. reflexivity. Qed.

Lemma cupd_eq : forall c x l, cupd c x l x = l.
Proof. intros. unfold cupd. rewrite String.eqb_refl. reflexivity. Qed.

Lemma mupd_same : forall m σ x, mupd m σ x (mstore m σ x) = σ.
Proof. intros [] [] x; simpl; rewrite supd_same; reflexivity. Qed.

Lemma mupd_mupd : forall m σ x v w, mupd m (mupd m σ x v) x w = mupd m σ x w.
Proof. intros [] [] x v w; simpl; rewrite supd_supd; reflexivity. Qed.

Lemma mstore_mupd : forall m σ x v, mstore m (mupd m σ x v) x = v.
Proof. intros [] [] x v; simpl; apply supd_eq. Qed.

Lemma mchan_mupd : forall m σ x v, mchan m (mupd m σ x v) = mchan m σ.
Proof. intros [] [] x v; reflexivity. Qed.

Lemma mstore_mchupd : forall m σ c l, mstore m (mchupd m σ c l) = mstore m σ.
Proof. intros [] [] c l; reflexivity. Qed.

Lemma mchupd_same : forall m σ c, mchupd m σ c (mchan m σ c) = σ.
Proof. intros [] [] c; simpl; rewrite cupd_same; reflexivity. Qed.

Lemma mchupd_mchupd : forall m σ c l l',
    mchupd m (mchupd m σ c l) c l' = mchupd m σ c l'.
Proof. intros [] [] c l l'; simpl; rewrite cupd_cupd; reflexivity. Qed.

Lemma mchan_mchupd : forall m σ c l, mchan m (mchupd m σ c l) c = l.
Proof. intros [] [] c l; simpl; apply cupd_eq. Qed.

Lemma mupd_mchupd : forall m σ x v c l,
    mupd m (mchupd m σ c l) x v = mchupd m (mupd m σ x v) c l.
Proof. intros [] [] x v c l; reflexivity. Qed.

(** ** What each atom does, in value form

    Facts about [asem], not rules: one step of each atom, with the
    computed value as a side condition so that the next state mentions
    the previous one once. Proofs feed them to the generated logic's
    atom rule ([Core.Rules.il_act_pt]). *)

Lemma asem_assign : forall m σ x e v, e (mstore m σ) = v ->
    asem m (AAsgn x e) σ (mupd m σ x v).
Proof. intros m σ x e v <-. reflexivity. Qed.

Lemma asem_write : forall m σ c x l v,
    mchan m σ c = l -> mstore m σ x = v ->
    asem m (AWrite c x) σ (mchupd m σ c (l ++ [v])).
Proof. intros m σ c x l v <- <-. reflexivity. Qed.

Lemma asem_read : forall m σ c x v l, mchan m σ c = v :: l ->
    asem m (ARead c x) σ (mchupd m (mupd m σ x v) c l).
Proof. intros m σ c x v l H. exists v, l. auto. Qed.

Lemma asem_adv : forall σ B, asem Adversary (AAdvAssert B) σ σ.
Proof. intros. split; reflexivity. Qed.

(** ** The generated logics *)

Definition ALv (m : mode) : VLogic (KLang (asem m)) Forward Plain Under :=
  ILv (asem m).
Definition ALsil (m : mode) : VLogic (KLang (asem m)) Backward Plain Under :=
  SILv (asem m).
Definition ALhl (m : mode) : VLogic (KLang (asem m)) Forward Plain Over :=
  HLv (asem m).

(** Vanegue's validity: every [Q] state is reached from a [P] state. *)
Definition al_valid (m : mode) (P : estate -> Prop) (c : tcom)
    (Q : estate -> Prop) : Prop :=
  forall σ', Q σ' -> exists σ, P σ /\ kev (asem m) (tenc m c) σ σ'.

Theorem al_valid_iff : forall m P c Q,
    prov (asem m) (ALv m) P (tenc m c) Q <-> al_valid m P c Q.
Proof. intros. apply il_iff. Qed.

(** ** Vanegue's single-thread rules, in any IL record *)

Section Rules.

Variable m : mode.
Variable V : VLogic (KLang (asem m)) Forward Plain Under.

Definition al (P : estate -> Prop) (c : tcom) (Q : estate -> Prop) : Prop :=
  prov (asem m) V P (tenc m c) Q.

Notation kev := (kev (asem m)).

Lemma al_iff : forall P c Q,
    al P c Q <-> (forall σ', Q σ' -> exists σ, P σ /\ kev (tenc m c) σ σ').
Proof. intros. apply il_iff. Qed.

(** Structural rules *)

Lemma al_empty : forall P c, al P c (fun _ => False).
Proof. intros. apply il_false. Qed.

Lemma al_unit : forall P, al P TSkip P.
Proof. intros. apply il_skip. Qed.

Lemma al_cons : forall P P' Q Q' c,
    (forall σ, P σ -> P' σ) -> (forall σ, Q' σ -> Q σ) ->
    al P c Q -> al P' c Q'.
Proof.
  intros P P' Q Q' c HP HQ H. pose proof (proj1 (al_iff _ _ _) H) as K.
  clear H. rename K into H. apply al_iff.
  intros σ' Hq. destruct (H σ' (HQ σ' Hq)) as [σ [Hp Hk]]. eauto.
Qed.

Lemma al_disj : forall P1 Q1 P2 Q2 c,
    al P1 c Q1 -> al P2 c Q2 ->
    al (fun σ => P1 σ \/ P2 σ) c (fun σ => Q1 σ \/ Q2 σ).
Proof.
  intros P1 Q1 P2 Q2 c H1 H2. pose proof (proj1 (al_iff _ _ _) H1) as K1.
  pose proof (proj1 (al_iff _ _ _) H2) as K2. clear H1 H2.
  rename K1 into H1, K2 into H2. apply al_iff.
  intros σ' [Hq | Hq]; [destruct (H1 σ' Hq) as [σ [Hp Hk]]
                       | destruct (H2 σ' Hq) as [σ [Hp Hk]]]; eauto.
Qed.

Lemma al_seq : forall P R Q c1 c2,
    al P c1 R -> al R c2 Q -> al P (TSeq c1 c2) Q.
Proof. intros. eapply il_seq; eassumption. Qed.

Lemma al_choice_l : forall P Q c1 c2, al P c1 Q -> al P (TChoice c1 c2) Q.
Proof. intros. apply il_choice_l. assumption. Qed.

Lemma al_choice_r : forall P Q c1 c2, al P c2 Q -> al P (TChoice c1 c2) Q.
Proof. intros. apply il_choice_r. assumption. Qed.

Lemma al_iter_zero : forall P c, al P (TStar c) P.
Proof.
  intros P c. apply al_iff. intros σ Hp. exists σ. split; [exact Hp |].
  apply KE_StarRefl.
Qed.

Lemma al_iter_nonzero : forall P Q c,
    al P (TSeq (TStar c) c) Q -> al P (TStar c) Q.
Proof.
  intros P Q c H. pose proof (proj1 (al_iff _ _ _) H) as K.
  clear H. rename K into H. apply al_iff. intros σ' Hq.
  destruct (H σ' Hq) as [σ [Hp Hk]]. exists σ. split; [exact Hp |].
  inversion Hk; subst. eapply kev_star_snoc; eassumption.
Qed.

Lemma al_backward_variant : forall (X : nat -> estate -> Prop) c,
    (forall n, al (X n) c (X (S n))) ->
    al (X 0) (TStar c) (fun σ => exists n, X n σ).
Proof.
  intros X c H. apply al_iff.
  assert (G : forall n σ', X n σ' ->
              exists σ, X 0 σ /\ kev (KStar (tenc m c)) σ σ').
  { induction n as [|n IH]; intros σ' Hx.
    - exists σ'. split; [exact Hx | apply KE_StarRefl].
    - destruct (proj1 (al_iff _ _ _) (H n) σ' Hx) as [σ1 [Hx1 Hk]].
      destruct (IH σ1 Hx1) as [σ [Hx0 Hs]].
      exists σ. split; [exact Hx0 | eapply kev_star_snoc; eassumption]. }
  intros σ' [n Hx]. exact (G n σ' Hx).
Qed.

(** Atom rules, in Vanegue's form *)

Lemma al_assume : forall P B,
    al P (TAssume B) (fun σ => P σ /\ massume m B σ).
Proof.
  intros P B. apply al_iff. intros σ [Hp Hb]. exists σ.
  split; [exact Hp | apply KE_Assume, Hb].
Qed.

Lemma al_assign : forall P x e,
    al P (TAtom (AAsgn x e))
       (fun σ => exists x', P (mupd m σ x x') /\
                 mstore m σ x = e (mstore m (mupd m σ x x'))).
Proof.
  intros P x e. apply al_iff. intros σ' [x' [Hp He]].
  exists (mupd m σ' x x'). split; [exact Hp |]. apply KE_Act. simpl.
  rewrite mupd_mupd, <- He, mupd_same. reflexivity.
Qed.

Lemma al_rand : forall P x,
    al P (TAtom (ARand x)) (fun σ => exists x', P (mupd m σ x x')).
Proof.
  intros P x. apply al_iff. intros σ' [x' Hp].
  exists (mupd m σ' x x'). split; [exact Hp |]. apply KE_Act. simpl.
  exists (mstore m σ' x). rewrite mupd_mupd, mupd_same. reflexivity.
Qed.

Lemma al_read : forall P c x,
    al P (TAtom (ARead c x))
       (fun σ => exists v x' l,
          P (mchupd m (mupd m σ x x') c (v :: l)) /\
          mchan m σ c = l /\ mstore m σ x = v).
Proof.
  intros P c x. apply al_iff. intros σ' [v [x' [l [Hp [Hl Hv]]]]].
  exists (mchupd m (mupd m σ' x x') c (v :: l)). split; [exact Hp |].
  apply KE_Act. simpl. exists v, l. split; [apply mchan_mchupd |].
  rewrite mupd_mchupd, mchupd_mchupd, mupd_mupd, <- Hv, mupd_same, <- Hl.
  rewrite <- (mchan_mupd m σ' x (mstore m σ' x)), mupd_same, mchupd_same.
  reflexivity.
Qed.

Lemma al_write : forall P c x,
    al P (TAtom (AWrite c x))
       (fun σ => exists l,
          P (mchupd m σ c l) /\ mchan m σ c = l ++ [mstore m σ x]).
Proof.
  intros P c x. apply al_iff. intros σ' [l [Hp Hl]].
  exists (mchupd m σ' c l). split; [exact Hp |]. apply KE_Act. simpl.
  rewrite mchan_mchupd, mstore_mchupd, mchupd_mchupd, <- Hl, mchupd_same.
  reflexivity.
Qed.

Lemma al_local : forall P Q x e c,
    al (fun σ => exists σ0, P σ0 /\ σ = mupd m σ0 x (e (mstore m σ0))) c Q ->
    al P (TLocal x e c)
       (fun σ => exists σb x0, Q σb /\ σ = mupd m σb x x0).
Proof.
  intros P Q x e c H. pose proof (proj1 (al_iff _ _ _) H) as K.
  clear H. rename K into H. apply al_iff.
  intros σ' [σb [x0 [Hq ->]]].
  destruct (H σb Hq) as [σ1 [[σ0 [Hp ->]] Hk]].
  exists σ0. split; [exact Hp |].
  eapply KE_Seq; [apply KE_Act; reflexivity |].
  eapply KE_Seq; [exact Hk | apply KE_Act; simpl; eauto].
Qed.


End Rules.

(** Adversarial assertions run in adversary mode. *)
Section AdvAssert.

Variable V : VLogic (KLang (asem Adversary)) Forward Plain Under.

Lemma al_adv_success : forall Q B,
    al Adversary V Q (TAtom (AAdvAssert B))
       (fun σ => Q σ /\ B (avs σ)).
Proof.
  intros Q B. apply al_iff. intros σ [Hq _]. exists σ.
  split; [exact Hq | apply KE_Act; simpl; auto].
Qed.

Lemma al_adv_failure : forall Q B,
    al Adversary V Q (TAtom (AAdvAssert B))
       (fun σ => Q σ /\ ~ B (avs σ)).
Proof.
  intros Q B. apply al_iff. intros σ [Hq _]. exists σ.
  split; [exact Hq | apply KE_Act; simpl; auto].
Qed.


End AdvAssert.
