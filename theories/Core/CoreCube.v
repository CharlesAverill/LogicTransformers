(** * Cube logics generated for the core language

    From the generated pools (forward and backward rules, built from an
    atom relation [rel]):

    - [GHL rel]: HL with both pools;
    - [GIL rel]: flip of the forward pool;
    - [GSIL rel]: complement, then flip of the backward pool.

    When [rel] agrees with the semantics, all three are sound and complete,
    for any states and atomic actions. The other top-face nodes follow by
    the generic complement and Galois edges, as for Imp. *)

From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube CubeLogic Transformer.
From LogicTransformers.Transformers Require Import Flip Complement.
From LogicTransformers.Core Require Import Kernel Generate.

Section CoreCube.

Context {Σ Act : Type} (act_sem : Act -> Σ -> Σ -> Prop).

Notation L := (KLang act_sem).

Definition cname : Type := (gname + gname)%type.

Definition gpool (rel : Act -> Σ -> Σ -> Prop) (r : cname) : ruleset L :=
  match r with
  | inl g => @fwd_rule Σ Act act_sem rel g
  | inr g => @bwd_rule Σ Act act_sem rel g
  end.

Definition is_fwd (r : cname) : Prop :=
  match r with inl _ => True | inr _ => False end.
Definition is_bwd (r : cname) : Prop :=
  match r with inl _ => False | inr _ => True end.

Definition GHL rel : CubeLogic L :=
  mkCubeLogic Forward Over cname (gpool rel) (fun _ => True).
Definition GIL rel : CubeLogic L := flip (restrict (GHL rel) is_fwd).
Definition GSIL rel : CubeLogic L :=
  flip (restrict (complement_cl (GHL rel)) is_bwd).

Section WithRel.

Variable rel : Act -> Σ -> Σ -> Prop.
Hypothesis Hrel : forall a s s', rel a s s' <-> act_sem a s s'.

Theorem GHL_base_sound : base_sound (GHL rel).
Proof.
  intros ps c [[g|g] [_ HR]] Hprem.
  - exact (fwd_over_sound act_sem rel Hrel g ps c HR Hprem).
  - exact (bwd_over_sound act_sem rel Hrel g ps c HR Hprem).
Qed.

Lemma GHL_fwd_exact : exact Forward (cl_base (restrict (GHL rel) is_fwd)).
Proof.
  intros P c. eapply derivable_mono; [| apply (fwd_exact act_sem rel Hrel)].
  intros ps c' [g HR]. exists (inl g). split; [split; exact I | exact HR].
Qed.

Theorem GHL_complete : complete (to_logic (GHL rel)).
Proof.
  apply exact_complete. eapply exact_mono; [| apply GHL_fwd_exact].
  intros ps c [r [_ HR]]. exists r. split; [exact I | exact HR].
Qed.

Theorem GIL_base_sound : base_sound (GIL rel).
Proof.
  intros ps c [[g|g] [[_ Hk] HR]] Hprem; [| contradiction].
  exact (fwd_under_sound act_sem rel Hrel g ps c HR Hprem).
Qed.

Theorem GIL_complete : complete (to_logic (GIL rel)).
Proof. apply (flip_complete (restrict (GHL rel) is_fwd)), GHL_fwd_exact. Qed.

Theorem GSIL_base_sound : base_sound (GSIL rel).
Proof.
  intros ps c [[g|g] [[_ Hk] [ps0 [c0 [HR [-> Hps]]]]]] Hprem;
    [contradiction |].
  change (cube_valid Backward Under (complement c0)).
  apply dual_sil_duality, (bwd_dual_sound act_sem rel Hrel g ps0 c0 HR).
  intros t Ht. apply dual_sil_duality, Hprem, Hps. exists t. auto.
Qed.

Theorem GSIL_complete : complete (to_logic (GSIL rel)).
Proof.
  apply exact_complete.
  change (exact Backward (cl_base (GSIL rel))).
  eapply exact_mono;
    [| apply (complement_wlp_exact _ (bwd_exact act_sem rel Hrel))].
  intros ps c [ps0 [c0 [[g HR] [-> Hps]]]].
  exists (inr g). split; [split; exact I |]. exists ps0, c0. auto.
Qed.

End WithRel.

End CoreCube.
