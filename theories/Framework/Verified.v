(** * Verified logics as records, and transformers between them

    A [VLogic L d p a] is a program logic for language [L] packaged with
    its proofs:

    - [vl_valid]: its validity is the cube node [(d, p, a)];
    - [vl_sound]: it is locally sound;
    - [vl_complete]: it is complete.

    Transformers are functions between these records, so applying one
    gives a new record whose proofs are fields: [vl_derive] turns a valid
    triple into a derivation, and [vl_valid_of] goes the other way.

    Generic transformers (any language):

    - [vcomplement]: node [(d, p, a)] to [(d, p̃, ā)] (classical);
    - [vgalois_hl], [vgalois_wlp_hl], [vgalois_nc], [vgalois_dimg_nc]:
      the Galois identifications (constructive);
    - [vinvert]: node [(d, p, a)] over [L] to [(flip d, p, a)] over
      [inv L] (constructive). *)

From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Transformer.
From LogicTransformers.Transformers Require Import Complement Galois Invert.

Record VLogic (L : Language) (d : direction) (p : polarity)
    (a : approximation) := mkVLogic {
  vl_logic : ProgramLogic L;
  vl_valid : forall t, valid vl_logic t <-> cvalid d p a t;
  vl_sound : locally_sound vl_logic;
  vl_complete : complete vl_logic
}.

Arguments mkVLogic {L d p a}.
Arguments vl_logic {L d p a}.
Arguments vl_valid {L d p a}.
Arguments vl_sound {L d p a}.
Arguments vl_complete {L d p a}.

Section Verified.

Context {L : Language}.

(** ** Pulling from a record *)

Lemma vl_derive : forall {d p a} (V : VLogic L d p a) t,
    cvalid d p a t -> derivable (rules (vl_logic V)) t.
Proof. intros d p a V t H. apply (vl_complete V), (vl_valid V), H. Qed.

Lemma vl_valid_of : forall {d p a} (V : VLogic L d p a) t,
    derivable (rules (vl_logic V)) t -> cvalid d p a t.
Proof.
  intros d p a V t D. apply (vl_valid V).
  exact (locally_sound_sound _ (vl_sound V) t D).
Qed.

Theorem vl_theory : forall {d p a} (V : VLogic L d p a) t,
    derivable (rules (vl_logic V)) t <-> cvalid d p a t.
Proof. intros. split; [apply vl_valid_of | apply vl_derive]. Qed.

(** ** Transport between records

    Prove a triple in one record by proving a related triple in another:
    the complemented triple at the complement node, or the same triple at
    a node with the same validity (a Galois partner). *)

Lemma vl_transport_compl : forall {d p a}
    (V1 : VLogic L d p a) (V2 : VLogic L d (flip_pol p) (flip_approx a)) t,
    derivable (rules (vl_logic V1)) t <->
    derivable (rules (vl_logic V2)) (complement t).
Proof.
  intros d p a V1 V2 t. rewrite (vl_theory V1), (vl_theory V2).
  apply complement_duality.
Qed.

Lemma vl_transport_same : forall {d p a d' p' a'}
    (V1 : VLogic L d p a) (V2 : VLogic L d' p' a'),
    (forall t, @cvalid L d p a t <-> cvalid d' p' a' t) ->
    forall t,
    derivable (rules (vl_logic V1)) t <-> derivable (rules (vl_logic V2)) t.
Proof.
  intros d p a d' p' a' V1 V2 H t. rewrite (vl_theory V1), (vl_theory V2).
  apply H.
Qed.

(** ** Running an edge on a record *)

Definition vedge {d p a d' p' a'}
    (E : Edge (@cvalid L d p a) (@cvalid L d' p' a'))
    (V : VLogic L d p a) : VLogic L d' p' a' :=
  mkVLogic (run_edge E (vl_logic V))
    (fun t => iff_refl _)
    (run_edge_locally_sound E (vl_logic V) (vl_valid V) (vl_sound V))
    (run_edge_complete E (vl_logic V) (vl_valid V) (vl_complete V)).

Definition vcomplement {d p a} (V : VLogic L d p a)
  : VLogic L d (flip_pol p) (flip_approx a) :=
  vedge (complement_edge d p a) V.

Definition vgalois_hl (V : VLogic L Forward Plain Over)
  : VLogic L Backward Dual Under := vedge galois_hl_wlp V.
Definition vgalois_wlp_hl (V : VLogic L Backward Dual Under)
  : VLogic L Forward Plain Over := vedge galois_wlp_hl V.
Definition vgalois_nc (V : VLogic L Backward Plain Over)
  : VLogic L Forward Dual Under := vedge galois_nc_dimg V.
Definition vgalois_dimg_nc (V : VLogic L Forward Dual Under)
  : VLogic L Backward Plain Over := vedge galois_dimg_nc V.

(** Convenience: [vcomplement] lands on [(d, flip p, flip a)]; these fix
    the indices for the common cases. *)
Definition vcomplement_FPU (V : VLogic L Forward Plain Under)
  : VLogic L Forward Dual Over := vcomplement V.
Definition vcomplement_FDO (V : VLogic L Forward Dual Over)
  : VLogic L Forward Plain Under.
Proof.
  refine (mkVLogic (vl_logic (vcomplement V)) _ (vl_sound (vcomplement V))
            (vl_complete (vcomplement V))).
  exact (vl_valid (vcomplement V)).
Defined.
Definition vcomplement_BPU (V : VLogic L Backward Plain Under)
  : VLogic L Backward Dual Over := vcomplement V.
Definition vcomplement_BDO (V : VLogic L Backward Dual Over)
  : VLogic L Backward Plain Under.
Proof.
  refine (mkVLogic (vl_logic (vcomplement V)) _ (vl_sound (vcomplement V))
            (vl_complete (vcomplement V))).
  exact (vl_valid (vcomplement V)).
Defined.
Definition vcomplement_FPO (V : VLogic L Forward Plain Over)
  : VLogic L Forward Dual Under := vcomplement V.
Definition vcomplement_BDU (V : VLogic L Backward Dual Under)
  : VLogic L Backward Plain Over.
Proof.
  refine (mkVLogic (vl_logic (vcomplement V)) _ (vl_sound (vcomplement V))
            (vl_complete (vcomplement V))).
  exact (vl_valid (vcomplement V)).
Defined.

(** ** Inversion *)

Lemma swap_cvalid : forall d p a (t : triple L),
    cvalid d p a t <-> cvalid (flip_dir d) p a (swap t).
Proof.
  intros d [|] a t; [apply swap_valid |].
  destruct t as [P c Q]. destruct d, a; simpl;
    unfold aimpl, dimg, wlp; simpl; split; auto.
Qed.

Definition vinvert {d p a} (V : VLogic L d p a)
  : VLogic (inv L) (flip_dir d) p a.
Proof.
  refine (mkVLogic
            (mkLogic (cvalid (flip_dir d) p a) (cvalid_proper _ _ _)
               (map_rules swap (rules (vl_logic V))))
            (fun t => iff_refl _) _ _).
  - intros ps c [ps0 [c0 [HR [-> Hps]]]] Hprem. simpl in *.
    apply swap_cvalid, (vl_valid V), (vl_sound V ps0 c0 HR).
    intros t Ht. apply (vl_valid V), swap_cvalid, Hprem, Hps.
    exists t. auto.
  - intros [P c Q] Vt. simpl in Vt.
    apply (derivable_map swap _ swap_proper (@mkTriple L Q c P)).
    apply (vl_complete V), (vl_valid V), swap_cvalid. exact Vt.
Defined.

End Verified.
