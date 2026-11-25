(** * Which edges exist: uniform correspondences and transformers

    This file makes precise which transformations between corners of the
    cube are possible without looking at the semantics.

    A corner is [(d, p, a)]. Its validity is [cvr P Q d p a R]
    ([Framework.Relational]), for any relation [R].

    ** Variance

    Enlarging a program's relation can only falsify triples at the four
    corners of the Hoare-logic group (HL, NC, p̃ost ⊇, p̃re ⊇): they are
    *antitone* in the relation ([cvr_anti]). It can only validate triples
    at the other four (IL, p̃ost ⊆, SIL, p̃re ⊆): they are *monotone*
    ([cvr_mono]).

    ** Uniform correspondences ([ucorr])

    A correspondence from corner A to corner B maps each triple's pre and
    post, without looking at the program, so that validity at A and at B
    agree for every relation. Galois connections (the identity map) and
    complement duality (negating both) are correspondences.

    [ucorr_iff_group]: two corners correspond exactly when they are in the
    same group, given two distinct states:
    - group 0: HL, p̃re ⊇, p̃ost ⊇, NC;
    - group 1: IL, p̃ost ⊆;
    - group 2: SIL, p̃re ⊆.
    Across groups 0 and 1/2 the obstruction is variance. Between groups 1
    and 2 it is direction ([no_ucorr_IL_SIL]).

    ** Uniform transformers ([no_monotone_crossing])

    A *uniform transformer* is a function on rule sets alone: it does not
    receive the semantics. It is *monotone* if more source rules never
    give fewer target rules. Every transformer that maps rules one at a
    time is monotone ([rulewise_monotone]); flip, complement and Galois
    all work that way.

    No monotone uniform transformer turns every sound and complete logic
    at an antitone corner into a sound and complete logic at a monotone
    corner, or the other way round. The source logics used in the proof
    are the most naive ones: every valid triple as an axiom.

    A non-uniform transformer can always cross, trivially, by ignoring
    its input and returning the target's valid triples as axioms. So both
    conditions are needed. [Core.VCore]'s [vto] crosses from HL by reading
    the source's derivations *negatively*: an action can take [s] to [s']
    when [{s} a {≠ s'}] is *not* derivable. More source rules can then
    mean fewer target rules. This theorem shows that some such
    non-monotone dependence is unavoidable for any uniform transformer
    that crosses between the groups. *)

From Stdlib Require Import Bool Arith Classical.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Relational.
From LogicTransformers.Transformers Require Import Complement.

(** ** Groups and variance *)

Definition group (d : direction) (p : polarity) (a : approximation) : nat :=
  match p, d, a with
  | Plain, Forward, Over => 0
  | Dual, Backward, Under => 0
  | Dual, Forward, Under => 0
  | Plain, Backward, Over => 0
  | Plain, Forward, Under => 1
  | Dual, Forward, Over => 1
  | Plain, Backward, Under => 2
  | Dual, Backward, Over => 2
  end.

Definition isanti d p a : bool := Nat.eqb (group d p a) 0.

Definition rsub {S : Type} (R1 R2 : S -> S -> Prop) : Prop :=
  forall s s', R1 s s' -> R2 s s'.

Lemma cvr_anti : forall {S : Type} d p a (P Q : S -> Prop) R1 R2,
    isanti d p a = true -> rsub R1 R2 ->
    cvr P Q d p a R2 -> cvr P Q d p a R1.
Proof.
  intros S d p a P Q R1 R2 Ha Hs. unfold rsub in Hs.
  destruct p, d, a; simpl in *; try discriminate; firstorder.
Qed.

Lemma cvr_mono : forall {S : Type} d p a (P Q : S -> Prop) R1 R2,
    isanti d p a = false -> rsub R1 R2 ->
    cvr P Q d p a R1 -> cvr P Q d p a R2.
Proof.
  intros S d p a P Q R1 R2 Ha Hs. unfold rsub in Hs.
  destruct p, d, a; simpl in *; try discriminate; firstorder.
Qed.

Definition rempty {S : Type} : S -> S -> Prop := fun _ _ => False.
Definition rfull {S : Type} : S -> S -> Prop := fun _ _ => True.

(** A triple valid for the empty relation, invalid for the full one. *)
Lemma witness_anti : forall {S : Type} (s0 : S) d p a,
    isanti d p a = true ->
    exists P Q : S -> Prop,
      cvr P Q d p a rempty /\ ~ cvr P Q d p a rfull.
Proof.
  intros S s0 d p a Ha. unfold rempty, rfull.
  destruct p, d, a; simpl in Ha; try discriminate; simpl.
  - exists (fun _ => True), (fun _ => False). split.
    + intros s s' _ [].
    + intros H. exact (H s0 s0 I I).
  - exists (fun _ => False), (fun _ => True). split.
    + intros s s' [].
    + intros H. exact (H s0 s0 I I).
  - exists (fun _ => False), (fun _ => True). split.
    + intros s' _ s [].
    + intros H. exact (H s0 I s0 I).
  - exists (fun _ => True), (fun _ => False). split.
    + intros s _ s' [].
    + intros H. exact (H s0 I s0 I).
Qed.

(** A triple valid for the full relation, invalid for the empty one. *)
Lemma witness_mono : forall {S : Type} (s0 : S) d p a,
    isanti d p a = false ->
    exists P Q : S -> Prop,
      cvr P Q d p a rfull /\ ~ cvr P Q d p a rempty.
Proof.
  intros S s0 d p a Ha. unfold rempty, rfull.
  destruct p, d, a; simpl in Ha; try discriminate; simpl.
  - exists (fun _ => True), (fun _ => True). split.
    + intros s' _. exists s'. auto.
    + intros H. destruct (H s0 I) as [s [_ []]].
  - exists (fun _ => True), (fun _ => True). split.
    + intros s _. exists s. auto.
    + intros H. destruct (H s0 I) as [s' [[] _]].
  - exists (fun _ => False), (fun _ => False). split.
    + intros s' H. exact (H s0 I).
    + intros H. exact (H s0 (fun _ h => h)).
  - exists (fun _ => False), (fun _ => False). split.
    + intros s H. exact (H s0 I).
    + intros H. exact (H s0 (fun _ h => h)).
Qed.

(** ** Uniform correspondences *)

Definition ucorr {S : Type} d p a d' p' a' : Prop :=
  exists fP fQ : (S -> Prop) -> (S -> Prop) -> (S -> Prop),
    forall (R : S -> S -> Prop) P Q,
      cvr P Q d p a R <-> cvr (fP P Q) (fQ P Q) d' p' a' R.

Lemma ucorr_refl : forall {S : Type} d p a, @ucorr S d p a d p a.
Proof.
  intros S d p a. exists (fun P _ => P), (fun _ Q => Q). reflexivity.
Qed.

Lemma ucorr_trans : forall {S : Type} d1 p1 a1 d2 p2 a2 d3 p3 a3,
    @ucorr S d1 p1 a1 d2 p2 a2 -> @ucorr S d2 p2 a2 d3 p3 a3 ->
    @ucorr S d1 p1 a1 d3 p3 a3.
Proof.
  intros S d1 p1 a1 d2 p2 a2 d3 p3 a3 [f1 [g1 H1]] [f2 [g2 H2]].
  exists (fun P Q => f2 (f1 P Q) (g1 P Q)),
         (fun P Q => g2 (f1 P Q) (g1 P Q)).
  intros R P Q. rewrite H1. apply H2.
Qed.

(** The generators: Galois connections (the identity on pre and post)
    and complement duality (negating both), each in both directions. *)

(** A language whose only program is a given relation, to reuse the
    cube's duality theorems. *)
Definition Lrel {S : Type} (R : S -> S -> Prop) : Language :=
  mkLanguage unit S (fun _ => R).

Lemma cvr_Lrel : forall {S : Type} (R : S -> S -> Prop) (P Q : S -> Prop)
    d p a,
    cvalid d p a (@mkTriple (Lrel R) P tt Q) <-> @cvr S P Q d p a R.
Proof. intros. apply (cvalid_cvr (Lrel R)). Qed.

Lemma ucorr_compl : forall {S : Type} d p a,
    @ucorr S d p a d (flip_pol p) (flip_approx a).
Proof.
  intros S d p a.
  exists (fun P _ => fun s => ~ P s), (fun _ Q => fun s => ~ Q s).
  intros R P Q. rewrite <- !cvr_Lrel.
  exact (complement_duality d p a (@mkTriple (Lrel R) P tt Q)).
Qed.

Lemma ucorr_compl_back : forall {S : Type} d p a,
    @ucorr S d (flip_pol p) (flip_approx a) d p a.
Proof.
  intros S d p a.
  exists (fun P _ => fun s => ~ P s), (fun _ Q => fun s => ~ Q s).
  intros R P Q. rewrite <- !cvr_Lrel.
  rewrite (complement_duality d p a
             (@mkTriple (Lrel R) (fun s => ~ P s) tt (fun s => ~ Q s))).
  split; apply (cvalid_proper (L := Lrel R));
    unfold triple_equiv, aequiv, complement, compl; simpl;
    repeat split; intros H; try tauto; apply NNPP; exact H.
Qed.

Lemma ucorr_galois_wlp : forall {S : Type},
    @ucorr S Forward Plain Over Backward Dual Under.
Proof.
  intros S. exists (fun P _ => P), (fun _ Q => Q). intros R P Q.
  rewrite <- !cvr_Lrel. apply galois_post_wlp.
Qed.

Lemma ucorr_galois_wlp_back : forall {S : Type},
    @ucorr S Backward Dual Under Forward Plain Over.
Proof.
  intros S. exists (fun P _ => P), (fun _ Q => Q). intros R P Q.
  rewrite <- !cvr_Lrel. symmetry. apply galois_post_wlp.
Qed.

Lemma ucorr_galois_dimg : forall {S : Type},
    @ucorr S Backward Plain Over Forward Dual Under.
Proof.
  intros S. exists (fun P _ => P), (fun _ Q => Q). intros R P Q.
  rewrite <- !cvr_Lrel. apply galois_pre_dimg.
Qed.

Lemma ucorr_galois_dimg_back : forall {S : Type},
    @ucorr S Forward Dual Under Backward Plain Over.
Proof.
  intros S. exists (fun P _ => P), (fun _ Q => Q). intros R P Q.
  rewrite <- !cvr_Lrel. symmetry. apply galois_pre_dimg.
Qed.

(** Every corner corresponds, both ways, to its group's representative:
    HL for group 0, IL for group 1, SIL for group 2. *)
Definition rep (g : nat) : direction * polarity * approximation :=
  match g with
  | 0 => (Forward, Plain, Over)
  | 1 => (Forward, Plain, Under)
  | _ => (Backward, Plain, Under)
  end.

Lemma to_rep : forall {S : Type} d p a,
    let '(d', p', a') := rep (group d p a) in
    @ucorr S d p a d' p' a' /\ @ucorr S d' p' a' d p a.
Proof.
  intros S d p a. destruct p, d, a; simpl.
  - split; apply ucorr_refl.
  - split; apply ucorr_refl.
  - split.
    + exact (ucorr_trans _ _ _ _ _ _ _ _ _ ucorr_galois_dimg
               (ucorr_compl_back Forward Plain Over)).
    + exact (ucorr_trans _ _ _ _ _ _ _ _ _ (ucorr_compl Forward Plain Over)
               ucorr_galois_dimg_back).
  - split; apply ucorr_refl.
  - split; [apply (ucorr_compl_back Forward Plain Under) |
            apply (ucorr_compl Forward Plain Under)].
  - split; [apply (ucorr_compl_back Forward Plain Over) |
            apply (ucorr_compl Forward Plain Over)].
  - split; [apply (ucorr_compl_back Backward Plain Under) |
            apply (ucorr_compl Backward Plain Under)].
  - split; [apply ucorr_galois_wlp_back | apply ucorr_galois_wlp].
Qed.

Lemma ucorr_group : forall {S : Type} d p a d' p' a',
    group d p a = group d' p' a' -> @ucorr S d p a d' p' a'.
Proof.
  intros S d p a d' p' a' Hg.
  pose proof (to_rep (S := S) d p a) as H1.
  pose proof (to_rep (S := S) d' p' a') as H2.
  rewrite Hg in H1. destruct (rep (group d' p' a')) as [[dr pr] ar].
  exact (ucorr_trans _ _ _ _ _ _ _ _ _ (proj1 H1) (proj2 H2)).
Qed.

(** Variance blocks correspondences across group 0, both ways. *)
Lemma no_ucorr_anti_mono : forall {S : Type} (s0 : S) d p a d' p' a',
    isanti d p a = true -> isanti d' p' a' = false ->
    ~ @ucorr S d p a d' p' a'.
Proof.
  intros S s0 d p a d' p' a' Ha Hm [fP [fQ H]].
  destruct (witness_anti s0 d p a Ha) as [P [Q [He Hf]]].
  apply Hf. apply H. apply (cvr_mono d' p' a' _ _ rempty rfull Hm).
  - intros s s' [].
  - apply H, He.
Qed.

Lemma no_ucorr_mono_anti : forall {S : Type} (s0 : S) d p a d' p' a',
    isanti d p a = false -> isanti d' p' a' = true ->
    ~ @ucorr S d p a d' p' a'.
Proof.
  intros S s0 d p a d' p' a' Hm Ha [fP [fQ H]].
  destruct (witness_mono s0 d p a Hm) as [P [Q [Hf He]]].
  apply He. apply H. apply (cvr_anti d' p' a' _ _ rempty rfull Ha).
  - intros s s' [].
  - apply H, Hf.
Qed.

(** Direction blocks correspondences between groups 1 and 2, both ways.
    IL triples say "some source reaches each target"; SIL triples say
    "each source reaches some target". *)
Lemma no_ucorr_IL_SIL : forall {S : Type} (x y : S), x <> y ->
    ~ @ucorr S Forward Plain Under Backward Plain Under.
Proof.
  intros S x y Hxy [fP [fQ H]].
  set (P := fun _ : S => True). set (Q := fun s : S => s = x).
  assert (Hx : forall s, fP P Q s -> s = x).
  { intros s Hs.
    assert (Hv : cvr (fP P Q) (fQ P Q) Backward Plain Under
                   (fun u v => u = x /\ v = x)).
    { apply H. simpl. intros s' Hs'. exists x. unfold P. auto. }
    destruct (Hv s Hs) as [s' [[E _] _]]. exact E. }
  assert (Hy : forall s, fP P Q s -> s = y).
  { intros s Hs.
    assert (Hv : cvr (fP P Q) (fQ P Q) Backward Plain Under
                   (fun u v => u = y /\ v = x)).
    { apply H. simpl. intros s' Hs'. exists y. unfold P. auto. }
    destruct (Hv s Hs) as [s' [[E _] _]]. exact E. }
  assert (Hv : cvr P Q Forward Plain Under rempty).
  { apply H. simpl. intros s Hs. exfalso. apply Hxy.
    rewrite <- (Hx s Hs). exact (Hy s Hs). }
  destruct (Hv x eq_refl) as [s [_ []]].
Qed.

Lemma no_ucorr_SIL_IL : forall {S : Type} (x y : S), x <> y ->
    ~ @ucorr S Backward Plain Under Forward Plain Under.
Proof.
  intros S x y Hxy [fP [fQ H]].
  set (P := fun s : S => s = x). set (Q := fun _ : S => True).
  assert (Hx : forall t, fQ P Q t -> t = x).
  { intros t Ht.
    assert (Hv : cvr (fP P Q) (fQ P Q) Forward Plain Under
                   (fun u v => u = x /\ v = x)).
    { apply H. simpl. intros s Hs. exists x. unfold Q. auto. }
    destruct (Hv t Ht) as [s [_ [_ E]]]. exact E. }
  assert (Hy : forall t, fQ P Q t -> t = y).
  { intros t Ht.
    assert (Hv : cvr (fP P Q) (fQ P Q) Forward Plain Under
                   (fun u v => u = x /\ v = y)).
    { apply H. simpl. intros s Hs. exists y. unfold Q. auto. }
    destruct (Hv t Ht) as [s [_ [_ E]]]. exact E. }
  assert (Hv : cvr P Q Backward Plain Under rempty).
  { apply H. simpl. intros t Ht. exfalso. apply Hxy.
    rewrite <- (Hx t Ht). exact (Hy t Ht). }
  destruct (Hv x eq_refl) as [s' [[] _]].
Qed.

(** The three groups are exactly the classes of corresponding corners. *)
Theorem ucorr_iff_group : forall {S : Type} (x y : S), x <> y ->
    forall d p a d' p' a',
    @ucorr S d p a d' p' a' <-> group d p a = group d' p' a'.
Proof.
  intros S x y Hxy d p a d' p' a'. split; [| apply ucorr_group].
  intros H. destruct (Nat.eq_dec (group d p a) (group d' p' a')) as [E | Hne];
    [exact E | exfalso].
  destruct (isanti d p a) eqn:A1, (isanti d' p' a') eqn:A2.
  - unfold isanti in A1, A2. apply Nat.eqb_eq in A1, A2. congruence.
  - exact (no_ucorr_anti_mono x d p a d' p' a' A1 A2 H).
  - exact (no_ucorr_mono_anti x d p a d' p' a' A1 A2 H).
  - assert (G : (group d p a = 1 /\ group d' p' a' = 2) \/
                (group d p a = 2 /\ group d' p' a' = 1)).
    { unfold isanti in A1, A2. revert A1 A2 Hne.
      destruct p, d, a, p', d', a'; simpl; intros;
        try discriminate; try congruence; auto. }
    destruct G as [[G1 G2] | [G1 G2]].
    + apply (no_ucorr_IL_SIL x y Hxy).
      apply (ucorr_trans _ _ _ d p a);
        [apply ucorr_group; rewrite G1; reflexivity |].
      apply (ucorr_trans _ _ _ d' p' a'); [exact H |].
      apply ucorr_group. rewrite G2. reflexivity.
    + apply (no_ucorr_SIL_IL x y Hxy).
      apply (ucorr_trans _ _ _ d p a);
        [apply ucorr_group; rewrite G1; reflexivity |].
      apply (ucorr_trans _ _ _ d' p' a'); [exact H |].
      apply ucorr_group. rewrite G2. reflexivity.
Qed.

(** ** Uniform transformers *)

Section Transformers.

Context {Pr St : Type}.

(** Rule sets are over triples of programs [Pr] and states [St]; the
    semantics is a separate parameter [sem], which a uniform transformer
    never sees. [L0] only fixes the triple type. *)
Definition L0 : Language := mkLanguage Pr St (fun _ _ _ => False).

Definition VS d p a (sem : Pr -> St -> St -> Prop) (t : @triple L0) : Prop :=
  cvr (pre t) (post t) d p a (sem (cmd t)).

Lemma cvr_ext : forall {S : Type} (P P' Q Q' : S -> Prop) d p a R,
    (forall s, P s <-> P' s) -> (forall s, Q s <-> Q' s) ->
    cvr P Q d p a R -> cvr P' Q' d p a R.
Proof.
  intros S P P' Q Q' d p a R HP HQ.
  destruct p, d, a; simpl; intros H.
  - intros s s' Hp Hr. apply HQ, (H s s'); [apply HP, Hp | exact Hr].
  - intros s' Hq. destruct (H s' (proj2 (HQ s') Hq)) as [s [Hp Hr]].
    exists s. split; [apply HP, Hp | exact Hr].
  - intros s s' Hr Hq. apply HP, (H s s' Hr), HQ, Hq.
  - intros s Hp. destruct (H s (proj2 (HP s) Hp)) as [s' [Hr Hq]].
    exists s'. split; [exact Hr | apply HQ, Hq].
  - intros s' Hall. apply HQ, H. intros s Hr. apply HP, Hall, Hr.
  - intros s' Hq s Hr. apply HP, (H s' (proj2 (HQ s') Hq) s Hr).
  - intros s Hall. apply HP, H. intros s' Hr. apply HQ, Hall, Hr.
  - intros s Hp s' Hr. apply HQ, (H s (proj2 (HP s) Hp) s' Hr).
Qed.

Lemma VS_proper : forall d p a sem, proper_validity (VS d p a sem).
Proof.
  intros d p a sem [P c Q] [P' c' Q'] [HP [Hc HQ]] H.
  unfold VS in *. simpl in *. subst c'.
  exact (cvr_ext P P' Q Q' _ _ _ _ HP HQ H).
Qed.

Definition rlsound (R : @ruleset L0) (W : @triple L0 -> Prop) : Prop :=
  forall ps c, R ps c -> (forall t, ps t -> W t) -> W c.
Definition rsound (R : @ruleset L0) (W : @triple L0 -> Prop) : Prop :=
  forall t, derivable R t -> W t.
Definition rcomplete (R : @ruleset L0) (W : @triple L0 -> Prop) : Prop :=
  forall t, W t -> derivable R t.

(** The most naive logic: every valid triple is an axiom. *)
Definition axioms (W : @triple L0 -> Prop) : @ruleset L0 :=
  fun ps c => (forall t, ~ ps t) /\ W c.

Lemma axioms_lsound : forall W, rlsound (axioms W) W.
Proof. intros W ps c [_ H] _. exact H. Qed.

Lemma axioms_complete : forall W, rcomplete (axioms W) W.
Proof.
  intros W t H. apply (D_Rule _ (fun _ => False) t).
  - split; [intros t' [] | exact H].
  - intros t' [].
Qed.

Definition monotone (T : @ruleset L0 -> @ruleset L0) : Prop :=
  forall R1 R2 : @ruleset L0, (forall ps c, R1 ps c -> R2 ps c) ->
  forall ps c, T R1 ps c -> T R2 ps c.

(** A transformer that maps each source rule instance to target rule
    instances, independently of the other rules. *)
Definition rulewise (f : ((@triple L0 -> Prop) * @triple L0) ->
                         ((@triple L0 -> Prop) * @triple L0) -> Prop)
    : @ruleset L0 -> @ruleset L0 :=
  fun R ps c => exists ps0 c0, R ps0 c0 /\ f (ps0, c0) (ps, c).

Lemma rulewise_monotone : forall f, monotone (rulewise f).
Proof.
  intros f R1 R2 Hs ps c [ps0 [c0 [HR Hf]]].
  exists ps0, c0. split; [apply Hs, HR | exact Hf].
Qed.

(** [T] turns every locally sound and complete logic at corner A into a
    sound and complete logic at corner B, whatever the semantics. *)
Definition crosses (T : @ruleset L0 -> @ruleset L0) d p a d' p' a' : Prop :=
  forall sem (R : @ruleset L0),
    rlsound R (VS d p a sem) -> rcomplete R (VS d p a sem) ->
    rsound (T R) (VS d' p' a' sem) /\ rcomplete (T R) (VS d' p' a' sem).

Definition sempty : Pr -> St -> St -> Prop := fun _ _ _ => False.
Definition sfull : Pr -> St -> St -> Prop := fun _ _ _ => True.

Theorem no_monotone_crossing : forall (p0 : Pr) (s0 : St) d p a d' p' a',
    isanti d p a <> isanti d' p' a' ->
    forall T, monotone T -> ~ crosses T d p a d' p' a'.
Proof.
  intros p0 s0 d p a d' p' a' Hv T HT H.
  destruct (isanti d p a) eqn:A1, (isanti d' p' a') eqn:A2;
    try (exfalso; apply Hv; reflexivity).
  - (* antitone source, monotone target *)
    assert (Hinc : forall ps c, axioms (VS d p a sfull) ps c ->
                               axioms (VS d p a sempty) ps c).
    { intros ps c [Hp Hc]. split; [exact Hp |].
      exact (cvr_anti d p a _ _ _ _ A1 (fun s s' _ => I) Hc). }
    destruct (witness_mono s0 d' p' a' A2) as [P [Q [Hf He]]].
    set (t := @mkTriple L0 P p0 Q).
    destruct (H sfull _ (axioms_lsound _) (axioms_complete _)) as [_ Hc].
    destruct (H sempty _ (axioms_lsound _) (axioms_complete _)) as [Hs _].
    apply He. apply (Hs t).
    apply (derivable_mono (T (axioms (VS d p a sfull))));
      [exact (HT _ _ Hinc) |].
    apply Hc. exact Hf.
  - (* monotone source, antitone target *)
    assert (Hinc : forall ps c, axioms (VS d p a sempty) ps c ->
                               axioms (VS d p a sfull) ps c).
    { intros ps c [Hp Hc]. split; [exact Hp |].
      exact (cvr_mono d p a _ _ _ _ A1
               (fun s s' (h : False) => match h with end) Hc). }
    destruct (witness_anti s0 d' p' a' A2) as [P [Q [He Hf]]].
    set (t := @mkTriple L0 P p0 Q).
    destruct (H sempty _ (axioms_lsound _) (axioms_complete _)) as [_ Hc].
    destruct (H sfull _ (axioms_lsound _) (axioms_complete _)) as [Hs _].
    apply Hf. apply (Hs t).
    apply (derivable_mono (T (axioms (VS d p a sempty))));
      [exact (HT _ _ Hinc) |].
    apply Hc. exact He.
Qed.

(** The headline instance: no monotone uniform transformer turns Hoare
    logic into incorrectness logic, or back. *)
Corollary no_monotone_HL_to_IL : forall (p0 : Pr) (s0 : St) T,
    monotone T -> ~ crosses T Forward Plain Over Forward Plain Under.
Proof.
  intros p0 s0 T HT.
  apply (no_monotone_crossing p0 s0); [discriminate | exact HT].
Qed.

Corollary no_monotone_IL_to_HL : forall (p0 : Pr) (s0 : St) T,
    monotone T -> ~ crosses T Forward Plain Under Forward Plain Over.
Proof.
  intros p0 s0 T HT.
  apply (no_monotone_crossing p0 s0); [discriminate | exact HT].
Qed.

End Transformers.
