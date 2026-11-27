(** * Hoare incorrectness logic: logic 23 of Cousot's figure

    Cousot's cube figure has a seventeenth logic, off the cube, reached
    from Hoare logic by negation (α¬): Hoare incorrectness logic, whose
    triples assert that a Hoare triple fails, [¬{P} c {Q}]: some run from
    [P] ends outside [Q] ([hiv]).

    Cousot observes that incorrectness logic is sufficient but not
    necessary for it: [[P] c [¬Q]] can fail when [¬{P} c {Q}] holds
    ([ImpCube.Negation]). It becomes necessary as well once the
    incorrectness postcondition is only required to be a *nonempty part*
    of [¬Q]:

    - [hil V]: for any language and any incorrectness-logic record [V],
      a Hoare incorrectness triple is derived from one derivation in [V]
      of [[P] c [R]] and a witness state in [R] outside [Q]
      ([HI_Witness]). It is a transformer from the incorrectness corner
      to logic 23.
    - [hil_sound], [hil_complete]: sound and complete for [hiv];
      completeness uses the singleton postcondition of the failing run.
    - [hiv_not_hl], [not_hl_hiv]: [hiv] is exactly the negation of Hoare
      validity (the second direction is classical).

    Validity [hiv] is existential, not an inclusion, so logic 23 is not
    one of the cube's corners; it is reached by this transformer. *)

From Stdlib Require Import Classical.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Relational Verified.

Section HoareIncorrectness.

Context {L : Language}.

Definition hiv (P : lstate L -> Prop) (c : prog L) (Q : lstate L -> Prop)
  : Prop :=
  exists s s', P s /\ sem L c s s' /\ ~ Q s'.

Theorem hiv_not_hl : forall P c Q,
    hiv P c Q -> ~ cvalid Forward Plain Over (@mkTriple L P c Q).
Proof.
  intros P c Q [s [s' [HP [Hc HQ]]]] H. rewrite cvalid_cvr in H.
  simpl in H. exact (HQ (H s s' HP Hc)).
Qed.

Theorem not_hl_hiv : forall P c Q,
    ~ cvalid Forward Plain Over (@mkTriple L P c Q) -> hiv P c Q.
Proof.
  intros P c Q H. rewrite cvalid_cvr in H. simpl in H.
  apply NNPP. intros N. apply H. intros s s' HP Hc.
  apply NNPP. intros HQ. apply N. exists s, s'. auto.
Qed.

Variable V : VLogic L Forward Plain Under.

Inductive hil : (lstate L -> Prop) -> prog L -> (lstate L -> Prop) -> Prop :=
  | HI_Witness : forall P c R Q s',
      derivable (rules (vl_logic V)) (@mkTriple L P c R) ->
      R s' -> ~ Q s' -> hil P c Q.

Theorem hil_sound : forall P c Q, hil P c Q -> hiv P c Q.
Proof.
  intros P c Q [P0 c0 R Q0 s' D HR HQ].
  apply vl_valid_of in D. rewrite cvalid_cvr in D. simpl in D.
  destruct (D s' HR) as [s [HP Hc]]. exists s, s'. auto.
Qed.

Theorem hil_complete : forall P c Q, hiv P c Q -> hil P c Q.
Proof.
  intros P c Q [s [s' [HP [Hc HQ]]]].
  apply (HI_Witness P c (fun x => x = s') Q s'); [| reflexivity | exact HQ].
  apply vl_derive. rewrite cvalid_cvr. simpl. intros x ->.
  exists s. auto.
Qed.

(** Logic 23 is the negation of Hoare logic. *)
Corollary hil_iff_not_hl : forall P c Q,
    hil P c Q <-> ~ cvalid Forward Plain Over (@mkTriple L P c Q).
Proof.
  intros P c Q. split.
  - intros H. apply hiv_not_hl, hil_sound, H.
  - intros H. apply hil_complete, not_hl_hiv, H.
Qed.

End HoareIncorrectness.
