(** * The complement edge: Hoare logic <-> necessary-condition logic

    Complementing both assertions swaps the over-approximate forward
    vertex with the over-approximate backward vertex:

<<
      img c P ⊆ Q    <->    preimg c (¬Q) ⊆ ¬P
>>

    Read as triples, [{P} c {Q}] is HL-valid iff [(¬P, c, ¬Q)] is NC-valid.
    The edge works for every language. It needs classical logic: the
    direction NC → HL is a contrapositive, and [¬¬P ≡ P] is used to show
    that the map is onto. *)

From Stdlib Require Import Classical.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube CubeLogic Transformer.

Section Complement.

Context {L : Language}.

Definition compl (P : assertion L) : assertion L := fun s => ~ P s.

Definition complement (t : triple L) : triple L :=
  mkTriple (compl (pre t)) (cmd t) (compl (post t)).

Lemma compl_aequiv : forall P Q, aequiv P Q -> aequiv (compl P) (compl Q).
Proof. unfold aequiv, compl. intros P Q H s. rewrite H. reflexivity. Qed.

Lemma compl_compl : forall P, aequiv (compl (compl P)) P.
Proof. unfold aequiv, compl. intros P s. split; [apply NNPP | auto]. Qed.

Lemma complement_proper : respects_equiv complement.
Proof.
  intros [P c Q] [P' c' Q'] [HP [Hc HQ]].
  split; [apply compl_aequiv, HP | split; [exact Hc | apply compl_aequiv, HQ]].
Qed.

Lemma complement_involutive : forall t,
    triple_equiv (complement (complement t)) t.
Proof. intros [P c Q]. repeat split; apply compl_compl. Qed.

Theorem hl_nc_duality : forall t,
    cube_valid Forward Over t <-> cube_valid Backward Over (complement t).
Proof.
  intros t. rewrite hl_valid_iff, nc_valid_iff.
  destruct t as [P c Q]; simpl; unfold compl.
  split.
  - intros H s s' Hr HQ HP. apply HQ. eapply H; eauto.
  - intros H s s' HP Hr. apply NNPP. intros HQ. eapply H; eauto.
Qed.

Theorem nc_hl_duality : forall t,
    cube_valid Backward Over t <-> cube_valid Forward Over (complement t).
Proof.
  intros t. rewrite hl_nc_duality.
  split; apply cube_valid_proper;
    [apply triple_equiv_sym |]; apply complement_involutive.
Qed.

(** HL ⟶ NC *)
Definition hl_to_nc : Edge (@cube_valid L Forward Over)
                           (@cube_valid L Backward Over).
Proof.
  refine (mkEdge _ _ complement complement_proper
            (cube_valid_proper _ _) hl_nc_duality _).
  intros t' Ht'. exists (complement t'). split.
  - apply nc_hl_duality, Ht'.
  - apply complement_involutive.
Defined.

(** NC ⟶ HL *)
Definition nc_to_hl : Edge (@cube_valid L Backward Over)
                           (@cube_valid L Forward Over).
Proof.
  refine (mkEdge _ _ complement complement_proper
            (cube_valid_proper _ _) nc_hl_duality _).
  intros t' Ht'. exists (complement t'). split.
  - apply hl_nc_duality, Ht'.
  - apply complement_involutive.
Defined.

(** ** Complement on cube logics

    Maps every pool rule through [complement] and swaps direction. The
    consequence rule is regenerated for the new vertex. *)

Definition complement_cl (C : CubeLogic L) : CubeLogic L :=
  mkCubeLogic (flip_dir (cl_dir C)) (cl_approx C) (cl_rule C)
    (fun r => map_rules complement (cl_pool C r)) (cl_keep C).

Theorem complement_cl_base_sound : forall C,
    cl_dir C = Forward -> cl_approx C = Over ->
    base_sound C -> base_sound (complement_cl C).
Proof.
  intros [d a N pool keep] Hd Ha HB. simpl in *. subst.
  intros ps c [r [Hk [ps0 [c0 [HR [-> Hps]]]]]] Hprem. simpl in *.
  apply hl_nc_duality. apply (HB ps0 c0); [exists r; auto |].
  intros t Ht. apply hl_nc_duality, Hprem, Hps. exists t. auto.
Qed.

(** ** Under complement, SIL is the wlp-dual *)

Theorem dual_sil_duality : forall t,
    dual_valid t <-> cube_valid Backward Under (complement t).
Proof.
  intros [P c Q]. rewrite sil_valid_iff.
  unfold dual_valid, aimpl, wlp, compl; simpl. split.
  - intros H s HnP. apply NNPP. intros Hn. apply HnP, H.
    intros s' Hr. apply NNPP. intros HnQ. apply Hn. exists s'. auto.
  - intros H s Hw. apply NNPP. intros HnP.
    destruct (H s HnP) as [s' [Hr HnQ]]. exact (HnQ (Hw s' Hr)).
Qed.

Lemma compl_wlp_compl : forall c Q,
    aequiv (compl (wlp c (compl Q))) (preimg c Q).
Proof.
  unfold aequiv, compl, wlp, preimg. intros c Q s. split.
  - intros H. apply NNPP. intros Hn. apply H.
    intros s' Hr HQ. apply Hn. exists s'. auto.
  - intros [s' [Hr HQ]] H. exact (H s' Hr HQ).
Qed.

(** Rules that derive exact wlp triples become, under complement, rules
    that derive exact backward (preimage) triples. *)
Theorem complement_wlp_exact : forall (R : ruleset L),
    (forall c Q, derivable R (mkTriple (wlp c Q) c Q)) ->
    exact Backward (map_rules complement R).
Proof.
  intros R H Q c. simpl.
  eapply D_Equiv;
    [apply derivable_map; [apply complement_proper | apply (H c (compl Q))]
    |].
  split; [apply compl_wlp_compl | split; [reflexivity | apply compl_compl]].
Qed.

(** ** Complement-duality on the whole face

    In Cousot's coordinates, complementing both assertions swaps the
    transformer with its complement dual and flips the inclusion:
    [(d, p, a)] corresponds to [(d, p̃, ā)]. For example HL [post ⊆]
    corresponds to [p̃ost ⊇], and IL [post ⊇] to [p̃ost ⊆]. *)

Lemma complement_duality_plain : forall d a t,
    cvalid d Plain a t <-> cvalid d Dual (flip_approx a) (complement t).
Proof.
  intros d a [P c Q].
  destruct d, a; simpl; unfold aimpl, img, preimg, dimg, wlp, compl; split.
  - intros H s' HnQ s Hr HP. apply HnQ, H. exists s. auto.
  - intros H s' [s [HP Hr]]. apply NNPP. intros HnQ. exact (H s' HnQ s Hr HP).
  - intros H s' Hall HQ. destruct (H s' HQ) as [s [HP Hr]].
    exact (Hall s Hr HP).
  - intros H s' HQ. apply NNPP. intros Hn. apply (H s'); [| exact HQ].
    intros s Hr HP. apply Hn. exists s. auto.
  - intros H s HnP s' Hr HQ. apply HnP, H. exists s'. auto.
  - intros H s [s' [Hr HQ]]. apply NNPP. intros HnP. exact (H s HnP s' Hr HQ).
  - intros H s Hall HP. destruct (H s HP) as [s' [Hr HQ]].
    exact (Hall s' Hr HQ).
  - intros H s HP. apply NNPP. intros Hn. apply (H s); [| exact HP].
    intros s' Hr HQ. apply Hn. exists s'. auto.
Qed.

Theorem complement_duality : forall d p a t,
    cvalid d p a t <-> cvalid d (flip_pol p) (flip_approx a) (complement t).
Proof.
  intros d [|] a t; [apply complement_duality_plain |].
  simpl flip_pol.
  rewrite (complement_duality_plain d (flip_approx a) (complement t)).
  replace (flip_approx (flip_approx a)) with a by (destruct a; reflexivity).
  split; apply cvalid_proper;
    [apply triple_equiv_sym |]; apply complement_involutive.
Qed.

(** The complement edge out of any node. *)
Definition complement_edge (d : direction) (p : polarity)
    (a : approximation)
  : Edge (@cvalid L d p a) (@cvalid L d (flip_pol p) (flip_approx a)).
Proof.
  refine (mkEdge _ _ complement complement_proper (cvalid_proper _ _ _)
            (complement_duality d p a) _).
  intros t' Ht'. exists (complement t'). split.
  - apply complement_duality.
    eapply cvalid_proper; [apply triple_equiv_sym, complement_involutive |].
    replace (flip_pol (flip_pol p)) with p in * by (destruct p; reflexivity).
    replace (flip_approx (flip_approx a)) with a in *
      by (destruct a; reflexivity).
    exact Ht'.
  - apply complement_involutive.
Defined.

End Complement.
