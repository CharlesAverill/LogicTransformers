(** * Validity notions of the cube

    For a program [c] with semantics [R = sem c]:

    - [img c P] is the forward image of [P] (the states reachable from [P]),
    - [preimg c Q] is the preimage of [Q] (the states that can reach [Q]).

    Two knobs give four validity notions:

<<
                     Over (image ⊆ other)     Under (other ⊆ image)
      Forward        Hoare  img P ⊆ Q          Incorrectness  Q ⊆ img P
      Backward       NC     preimg Q ⊆ P       SIL            P ⊆ preimg Q
>>

    Here NC is necessary-condition logic and SIL is sufficient
    incorrectness logic. *)

From LogicTransformers.Framework Require Import Language ProgramLogic.

Inductive direction := Forward | Backward.
Inductive approximation := Over | Under.

Definition flip_dir (d : direction) : direction :=
  match d with Forward => Backward | Backward => Forward end.

Definition flip_approx (a : approximation) : approximation :=
  match a with Over => Under | Under => Over end.

(** Cousot's third coordinate: a transformer [τ] or its complement dual
    [τ̃ = ¬ ∘ τ ∘ ¬]. *)
Inductive polarity := Plain | Dual.

Definition flip_pol (p : polarity) : polarity :=
  match p with Plain => Dual | Dual => Plain end.

Section Cube.

Context {L : Language}.

Definition img (c : prog L) (P : assertion L) : assertion L :=
  fun s' => exists s, P s /\ sem L c s s'.

Definition preimg (c : prog L) (Q : assertion L) : assertion L :=
  fun s => exists s', sem L c s s' /\ Q s'.

Definition cube_valid (d : direction) (a : approximation)
    (t : triple L) : Prop :=
  match d, a with
  | Forward, Over => aimpl (img (cmd t) (pre t)) (post t)
  | Forward, Under => aimpl (post t) (img (cmd t) (pre t))
  | Backward, Over => aimpl (preimg (cmd t) (post t)) (pre t)
  | Backward, Under => aimpl (pre t) (preimg (cmd t) (post t))
  end.

Lemma cube_valid_proper : forall d a, proper_validity (cube_valid d a).
Proof.
  intros d a [P c Q] [P' c' Q'] [HP [Hc HQ]] V.
  simpl in *. subst c'.
  unfold aequiv in HP, HQ.
  destruct d, a; simpl in *; unfold aimpl, img, preimg in *.
  - intros s' [s [Hs Hr]]. apply HQ, V. exists s. split; [apply HP|]; auto.
  - intros s' Hs'. destruct (V s' (proj2 (HQ s') Hs')) as [s [Hs Hr]].
    exists s. split; [apply HP|]; auto.
  - intros s [s' [Hr Hs']]. apply HP, V. exists s'. split; [|apply HQ]; auto.
  - intros s Hs. destruct (V s (proj2 (HP s) Hs)) as [s' [Hr Hs']].
    exists s'. split; [|apply HQ]; auto.
Qed.

(** Unfolded forms of the four validity notions. *)

Lemma hl_valid_iff : forall t,
    cube_valid Forward Over t <->
    (forall s s', pre t s -> sem L (cmd t) s s' -> post t s').
Proof. intros [P c Q]; simpl; unfold aimpl, img; firstorder. Qed.

Lemma il_valid_iff : forall t,
    cube_valid Forward Under t <->
    (forall s', post t s' -> exists s, pre t s /\ sem L (cmd t) s s').
Proof. intros [P c Q]; simpl; unfold aimpl, img; firstorder. Qed.

Lemma nc_valid_iff : forall t,
    cube_valid Backward Over t <->
    (forall s s', sem L (cmd t) s s' -> post t s' -> pre t s).
Proof. intros [P c Q]; simpl; unfold aimpl, preimg; firstorder. Qed.

Lemma sil_valid_iff : forall t,
    cube_valid Backward Under t <->
    (forall s, pre t s -> exists s', sem L (cmd t) s s' /\ post t s').
Proof. intros [P c Q]; simpl; unfold aimpl, preimg; firstorder. Qed.

(** ** Weakest liberal preconditions and the wlp-dual of SIL

    [wlp c Q] holds in the states all of whose terminating runs end in
    [Q]. A triple is [dual_valid] when [P] contains [wlp c Q]. This is not
    a vertex of the cube. It is what SIL turns into under complement (see
    [Complement.dual_sil_duality]), and a triple is both HL-valid and
    [dual_valid] exactly when [P] is the weakest liberal precondition. *)

Definition wlp (c : prog L) (Q : assertion L) : assertion L :=
  fun s => forall s', sem L c s s' -> Q s'.

Definition dual_valid (t : triple L) : Prop :=
  aimpl (wlp (cmd t) (post t)) (pre t).

(** ** The cube in Cousot's coordinates

    Each corner of a face is a transformer: [post] ([img]), [pre]
    ([preimg]), [p̃ost] ([dimg]) or [p̃re] ([wlp]). Each corner has an
    [Over] node ([τ(·) ⊆ ·]) and an [Under] node ([· ⊆ τ(·)]). Forward
    transformers take the pre and are compared with the post; backward
    ones are the other way round. *)

(** [p̃ost c P]: the states all of whose predecessors are in [P]. *)
Definition dimg (c : prog L) (P : assertion L) : assertion L :=
  fun s' => forall s, sem L c s s' -> P s.

Definition cvalid (d : direction) (p : polarity) (a : approximation)
    (t : triple L) : Prop :=
  match p with
  | Plain => cube_valid d a t
  | Dual =>
      match d, a with
      | Forward, Over => aimpl (dimg (cmd t) (pre t)) (post t)
      | Forward, Under => aimpl (post t) (dimg (cmd t) (pre t))
      | Backward, Over => aimpl (wlp (cmd t) (post t)) (pre t)
      | Backward, Under => aimpl (pre t) (wlp (cmd t) (post t))
      end
  end.

Lemma cvalid_proper : forall d p a, proper_validity (cvalid d p a).
Proof.
  intros d [|] a; [apply cube_valid_proper |].
  intros [P c Q] [P' c' Q'] [HP [Hc HQ]] V.
  simpl in *. subst c'. unfold aequiv in HP, HQ.
  destruct d, a; simpl in *; unfold aimpl, dimg, wlp in *.
  - intros s' H. apply HQ, V. intros s Hr. apply HP, H, Hr.
  - intros s' Hs' s Hr. apply HP, (V s'); [apply HQ, Hs' | exact Hr].
  - intros s H. apply HP, V. intros s' Hr. apply HQ, H, Hr.
  - intros s Hs s' Hr. apply HQ, (V s); [apply HP, Hs | exact Hr].
Qed.

(** The two Galois connections that collapse pairs of nodes ("different
    logics to prove the same property"). Both are constructive. *)

Theorem galois_post_wlp : forall t,
    cvalid Forward Plain Over t <-> cvalid Backward Dual Under t.
Proof.
  intros [P c Q]. simpl. unfold aimpl, img, wlp. split.
  - intros H s HP s' Hr. apply H. exists s. auto.
  - intros H s' [s [HP Hr]]. exact (H s HP s' Hr).
Qed.

Theorem galois_pre_dimg : forall t,
    cvalid Backward Plain Over t <-> cvalid Forward Dual Under t.
Proof.
  intros [P c Q]. simpl. unfold aimpl, preimg, dimg. split.
  - intros H s' HQ s Hr. apply H. exists s'. auto.
  - intros H s [s' [Hr HQ]]. exact (H s' HQ s Hr).
Qed.

(** ** Exactness from two-sided validity

    A forward triple is exact (its post is the strongest postcondition)
    iff it is valid at both the [Over] and the [Under] node, and dually a
    backward triple's pre is the wlp iff it is HL-valid and [dual_valid].
    So the exactness of a rule follows from its soundness at both nodes. *)

Definition fexact (t : triple L) : Prop :=
  aequiv (post t) (img (cmd t) (pre t)).

Lemma fexact_iff : forall t,
    fexact t <-> cube_valid Forward Over t /\ cube_valid Forward Under t.
Proof.
  intros [P c Q]. simpl. unfold fexact, aequiv, aimpl. simpl. split.
  - intros H. split; intros s; apply H.
  - intros [H1 H2] s. split; [apply H2 | apply H1].
Qed.

Lemma fexact_equiv : forall P c Q,
    fexact (mkTriple P c Q) ->
    triple_equiv (mkTriple P c Q) (mkTriple P c (img c P)).
Proof. intros P c Q H. repeat split; auto; apply H. Qed.

Lemma fexact_img : forall P c, fexact (mkTriple P c (img c P)).
Proof. intros P c s. split; auto. Qed.

(** A triple is pre-exact (its pre is the wlp of its post) iff it is
    valid at [post ⊆] (HL) and at [p̃re ⊆] ([dual_valid]). *)
Definition pexact (t : triple L) : Prop :=
  aequiv (pre t) (wlp (cmd t) (post t)).

Lemma pexact_iff : forall t,
    pexact t <-> cube_valid Forward Over t /\ dual_valid t.
Proof.
  intros [P c Q]. simpl. unfold pexact, dual_valid, aequiv, aimpl, img, wlp.
  simpl. split.
  - intros H. split.
    + intros s' [s [HP Hr]]. exact (proj1 (H s) HP s' Hr).
    + intros s Hw. apply H, Hw.
  - intros [H1 H2] s. split.
    + intros HP s' Hr. apply H1. exists s. auto.
    + apply H2.
Qed.

Lemma pexact_equiv : forall P c Q,
    pexact (mkTriple P c Q) ->
    triple_equiv (mkTriple P c Q) (mkTriple (wlp c Q) c Q).
Proof. intros P c Q H. repeat split; auto; apply H. Qed.

Lemma pexact_wlp : forall c Q, pexact (mkTriple (wlp c Q) c Q).
Proof. intros c Q s. split; auto. Qed.

Lemma cvalid_sem_ext_1 : forall d p a (c1 c2 : prog L) P Q,
    (forall s s', sem L c1 s s' <-> sem L c2 s s') ->
    cvalid d p a (mkTriple P c1 Q) -> cvalid d p a (mkTriple P c2 Q).
Proof.
  intros d [|] a c1 c2 P Q H; destruct d, a; simpl;
    unfold aimpl, img, preimg, dimg, wlp.
  - intros V s' [s [HP Hr]]. apply V. exists s. split; [| apply H]; auto.
  - intros V s' HQ. destruct (V s' HQ) as [s [HP Hr]].
    exists s. split; [| apply H]; auto.
  - intros V s [s' [Hr HQ]]. apply V. exists s'. split; [apply H |]; auto.
  - intros V s HP. destruct (V s HP) as [s' [Hr HQ]].
    exists s'. split; [apply H |]; auto.
  - intros V s' Hall. apply V. intros s Hr. apply Hall, H, Hr.
  - intros V s' HQ s Hr. apply (V s' HQ s), H, Hr.
  - intros V s Hall. apply V. intros s' Hr. apply Hall, H, Hr.
  - intros V s HP s' Hr. apply (V s HP s'), H, Hr.
Qed.

Lemma cvalid_sem_ext : forall d p a (c1 c2 : prog L) P Q,
    (forall s s', sem L c1 s s' <-> sem L c2 s s') ->
    cvalid d p a (mkTriple P c1 Q) <-> cvalid d p a (mkTriple P c2 Q).
Proof.
  intros d p a c1 c2 P Q H. split; apply cvalid_sem_ext_1; [exact H |].
  intros s s'. split; apply H.
Qed.

End Cube.
