(** * Outcome logic: a corner over sets of outcomes

    Outcome logic (Zilberstein, Dreyer and Silva) asserts properties of
    the *set* of a program's outcomes, such as "both an error and a
    success are reachable". For nondeterminism, a triple
    [<φ> c <ψ>] says: whenever a set of start states satisfies [φ], the
    set of its outcomes satisfies [ψ] ([ol_valid]).

    It sits on the other side of the boundary from games
    ([Adversarial.Game]):

    - [ol_relational]: it is a function of the program's relation, as
      every corner is;
    - [ol_is_hoare]: it is exactly Hoare validity of the *lifted*
      language, whose states are sets of states and whose programs map
      a set to its image ([Lift]), for outcome assertions that respect
      equivalence of sets. So outcome logic is a corner of the cube,
      over different states, and the language-independent transformers
      (complement, Galois, inversion) apply to it.

    Generation from the semantics needs the lifted language to be an
    instance of the core, and lifted choice (the union of two images) is
    not the core's choice (a choice between runs), so generating its
    rules is left open. Axiom-free. *)

From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Relational.

Section Outcome.

Variable L : Language.

Notation St := (lstate L).
Notation oset := (St -> Prop).

(** The outcomes of a set of start states. *)
Definition outcomes (c : prog L) (S : oset) : oset :=
  fun s' => exists s, S s /\ sem L c s s'.

Definition ol_valid (phi : oset -> Prop) (c : prog L) (psi : oset -> Prop)
  : Prop :=
  forall S, phi S -> psi (outcomes c S).

(** Programs map a set of states to its image. *)
Definition Lift : Language :=
  mkLanguage (prog L) oset
    (fun c S S' => forall s', S' s' <-> outcomes c S s').

(** An outcome assertion that cannot tell equivalent sets apart. *)
Definition respects (psi : oset -> Prop) : Prop :=
  forall S S', (forall s, S s <-> S' s) -> psi S -> psi S'.

Theorem ol_is_hoare : forall phi c psi, respects psi ->
    ol_valid phi c psi <->
    cvalid Forward Plain Over (@mkTriple Lift phi c psi).
Proof.
  intros phi c psi Hr. rewrite cvalid_cvr. simpl. split.
  - intros V S S' HS E. apply (Hr (outcomes c S)); [| exact (V S HS)].
    intros s. symmetry. apply E.
  - intros V S HS. apply (V S (outcomes c S) HS). intros s'. reflexivity.
Qed.

Theorem ol_relational : forall (c1 c2 : prog L),
    (forall s s', sem L c1 s s' <-> sem L c2 s s') ->
    forall phi psi, respects psi ->
    ol_valid phi c1 psi -> ol_valid phi c2 psi.
Proof.
  intros c1 c2 E phi psi Hr V S HS. apply (Hr (outcomes c1 S)).
  - intros s'. split; intros [s [Hs Hc]]; exists s; split; auto; apply E, Hc.
  - exact (V S HS).
Qed.

End Outcome.
