(** * Fixpoint induction and its order dual

    Over predicates on a type, ordered by inclusion:

    - [park_lfp] (Park, Cousot POPL'24 Thm. II.3.1): [lfp F ⊆ p] iff some
      invariant [i] has [F i ⊆ i] and [i ⊆ p]. This is the principle behind
      the Hoare invariant rule.
    - [park_gfp]: its order dual is about the greatest fixpoint:
      [p ⊆ gfp F] iff some coinvariant [i] has [i ⊆ F i] and [p ⊆ i].
    - [flipped_park_not_lfp]: the order-flipped Park condition does not
      under-approximate the least fixpoint.

    Loop semantics is a least fixpoint ([Obstructions.sp_while_lfp]), so
    flipping the invariant rule gives a principle for the wrong fixpoint.
    Everything here is constructive. *)

Section Fixpoints.

Context {A : Type}.

Definition pset := A -> Prop.

Definition sub (X Y : pset) : Prop := forall a, X a -> Y a.

Definition monotone (F : pset -> pset) : Prop :=
  forall X Y, sub X Y -> sub (F X) (F Y).

Definition lfp (F : pset -> pset) : pset :=
  fun a => forall X, sub (F X) X -> X a.

Definition gfp (F : pset -> pset) : pset :=
  fun a => exists X, sub X (F X) /\ X a.

Lemma lfp_least : forall F X, sub (F X) X -> sub (lfp F) X.
Proof. intros F X H a Ha. exact (Ha X H). Qed.

Lemma lfp_prefix : forall F, monotone F -> sub (F (lfp F)) (lfp F).
Proof.
  intros F HF a Ha X HX. apply HX.
  apply (HF (lfp F) X); [apply lfp_least, HX | exact Ha].
Qed.

Lemma gfp_greatest : forall F X, sub X (F X) -> sub X (gfp F).
Proof. intros F X H a Ha. exists X. auto. Qed.

Lemma gfp_postfix : forall F, monotone F -> sub (gfp F) (F (gfp F)).
Proof.
  intros F HF a [X [HX Ha]].
  apply (HF X (gfp F)); [apply gfp_greatest, HX | apply HX, Ha].
Qed.

Theorem park_lfp : forall F, monotone F -> forall p,
    sub (lfp F) p <-> exists i, sub (F i) i /\ sub i p.
Proof.
  intros F HF p. split.
  - intros H. exists (lfp F). split; [apply lfp_prefix, HF | exact H].
  - intros [i [Hi Hip]] a Ha. apply Hip, (lfp_least F i Hi), Ha.
Qed.

Theorem park_gfp : forall F, monotone F -> forall p,
    sub p (gfp F) <-> exists i, sub i (F i) /\ sub p i.
Proof.
  intros F HF p. split.
  - intros H. exists (gfp F). split; [apply gfp_postfix, HF | exact H].
  - intros [i [Hi Hpi]] a Ha. apply (gfp_greatest F i Hi), Hpi, Ha.
Qed.

End Fixpoints.

(** The order-flipped Park condition does not imply under-approximation
    of the least fixpoint: for [F = id], everything is a coinvariant but
    [lfp id] is empty. *)
Theorem flipped_park_not_lfp :
  ~ (forall (A : Type) (F : @pset A -> @pset A), monotone F ->
       forall p i, sub i (F i) -> sub p i -> sub p (lfp F)).
Proof.
  intros H.
  assert (Hm : monotone (fun X : @pset unit => X))
    by (intros X Y HXY; exact HXY).
  specialize (H unit (fun X => X) Hm (fun _ => True) (fun _ => True)
                (fun a Ha => Ha) (fun a Ha => Ha) tt I).
  exact (H (fun _ => False) (fun a Ha => Ha)).
Qed.
