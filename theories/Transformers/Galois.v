(** * Galois edges: the same theory at two nodes

    Cousot's cube has two Galois connections per face that collapse pairs
    of nodes ("different logics to prove the same property"):

<<
      post P ⊆ Q   <->   P ⊆ p̃re Q        (HL  =  subgoal induction / wlp)
      pre Q ⊆ P    <->   Q ⊆ p̃ost P       (NC  =  p̃ost ⊇)
>>

    As edges these map each triple to itself. They are constructive. *)

From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Transformer.

Section Galois.

Context {L : Language}.

Definition id_edge (V1 V2 : triple L -> Prop)
    (HV2 : proper_validity V2) (H : forall t, V1 t <-> V2 t)
  : Edge V1 V2.
Proof.
  refine (mkEdge _ _ (fun t => t) _ HV2 H _).
  - intros t t' He. exact He.
  - intros t' Ht'. exists t'. split; [apply H, Ht' | apply triple_equiv_refl].
Defined.

Definition galois_hl_wlp : Edge (@cvalid L Forward Plain Over)
                                (@cvalid L Backward Dual Under) :=
  id_edge _ _ (cvalid_proper _ _ _) galois_post_wlp.

Definition galois_nc_dimg : Edge (@cvalid L Backward Plain Over)
                                 (@cvalid L Forward Dual Under) :=
  id_edge _ _ (cvalid_proper _ _ _) galois_pre_dimg.

Definition galois_wlp_hl : Edge (@cvalid L Backward Dual Under)
                               (@cvalid L Forward Plain Over).
Proof.
  apply (id_edge _ _ (cvalid_proper _ _ _)).
  intros t. split; apply galois_post_wlp.
Defined.

Definition galois_dimg_nc : Edge (@cvalid L Forward Dual Under)
                                 (@cvalid L Backward Plain Over).
Proof.
  apply (id_edge _ _ (cvalid_proper _ _ _)).
  intros t. split; apply galois_pre_dimg.
Defined.

End Galois.
