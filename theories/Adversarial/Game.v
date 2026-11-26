(** * Games are not corners of the cube

    Adversarial logic resolves every choice existentially, the victim's
    as well as the adversary's, which is why it is incorrectness logic
    ([Adversarial.AL]). A *game* validity distinguishes them: the
    adversary wins from [s] if it has a strategy that reaches [Q]
    whatever the victim chooses ([win]).

    [game_not_relational]: game validity is not a function of a
    program's relation between states. Two programs with the same runs,
    a choice between [x := 0] and [x := 1] made by the adversary or by
    the victim, differ in who wins.

    [game_not_a_corner]: so no corner of the cube expresses it, under
    any way of building the pre- and postcondition from the start state
    and the goal: cube validity depends on the program only through its
    relation. A game is a corner only over a different state space, for
    example sets of outcomes the adversary can force. Axiom-free. *)

From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Relational.

(** ** Two-player programs *)

Inductive gcom : Type :=
  | GSkip
  | GSet (n : nat)
  | GSeq (c1 c2 : gcom)
  | GAng (c1 c2 : gcom)     (* the adversary chooses *)
  | GDem (c1 c2 : gcom).    (* the victim chooses *)

(** Runs: both kinds of choice are union. *)
Inductive grun : gcom -> nat -> nat -> Prop :=
  | GR_Skip : forall s, grun GSkip s s
  | GR_Set : forall n s, grun (GSet n) s n
  | GR_Seq : forall c1 c2 s s1 s2,
      grun c1 s s1 -> grun c2 s1 s2 -> grun (GSeq c1 c2) s s2
  | GR_AngL : forall c1 c2 s s', grun c1 s s' -> grun (GAng c1 c2) s s'
  | GR_AngR : forall c1 c2 s s', grun c2 s s' -> grun (GAng c1 c2) s s'
  | GR_DemL : forall c1 c2 s s', grun c1 s s' -> grun (GDem c1 c2) s s'
  | GR_DemR : forall c1 c2 s s', grun c2 s s' -> grun (GDem c1 c2) s s'.

Definition GLang : Language := mkLanguage gcom nat grun.

(** The adversary can force [Q] from [s]. *)
Fixpoint win (c : gcom) (s : nat) (Q : nat -> Prop) : Prop :=
  match c with
  | GSkip => Q s
  | GSet n => Q n
  | GSeq c1 c2 => win c1 s (fun s1 => win c2 s1 Q)
  | GAng c1 c2 => win c1 s Q \/ win c2 s Q
  | GDem c1 c2 => win c1 s Q /\ win c2 s Q
  end.

(** ** Not a function of the relation *)

Definition angelic : gcom := GAng (GSet 0) (GSet 1).
Definition demonic : gcom := GDem (GSet 0) (GSet 1).

Lemma same_runs : forall s s', grun angelic s s' <-> grun demonic s s'.
Proof.
  intros s s'. split; intros H; inversion H; subst;
    match goal with H' : grun (GSet _) _ _ |- _ => inversion H'; subst end;
    first [ apply GR_AngL; constructor | apply GR_AngR; constructor
          | apply GR_DemL; constructor | apply GR_DemR; constructor ].
Qed.

Theorem game_not_relational :
  exists c1 c2, (forall s s', grun c1 s s' <-> grun c2 s s') /\
    exists s Q, win c1 s Q /\ ~ win c2 s Q.
Proof.
  exists angelic, demonic. split; [exact same_runs |].
  exists 0, (fun n => n = 0). simpl. split; [left; reflexivity |].
  intros [_ H]. discriminate.
Qed.

(** ** Not a corner *)

Lemma cvr_same_rel : forall {S : Type} (P Q : S -> Prop) d p a
    (R1 R2 : S -> S -> Prop),
    (forall s s', R1 s s' <-> R2 s s') ->
    cvr P Q d p a R1 -> cvr P Q d p a R2.
Proof.
  intros S P Q d p a R1 R2 E H. destruct p, d, a; simpl in *.
  - intros s s' HP HR. apply (H s s' HP), E, HR.
  - intros s' HQ. destruct (H s' HQ) as [s [HP HR]].
    exists s. split; [exact HP | apply E, HR].
  - intros s s' HR HQ. apply (H s s'); [apply E, HR | exact HQ].
  - intros s HP. destruct (H s HP) as [s' [HR HQ]].
    exists s'. split; [apply E, HR | exact HQ].
  - intros s' K. apply H. intros s HR. apply K, E, HR.
  - intros s' HQ s HR. apply (H s' HQ s), E, HR.
  - intros s K. apply H. intros s' HR. apply K, E, HR.
  - intros s HP s' HR. apply (H s HP s'), E, HR.
Qed.

(** Whatever corner, and whatever pre- and postcondition are built from
    the start state and the goal, cube validity does not agree with
    game validity. *)
Theorem game_not_a_corner : forall d p a
    (pre post : nat -> (nat -> Prop) -> nat -> Prop),
    ~ (forall c s Q,
         win c s Q <-> cvalid d p a (@mkTriple GLang (pre s Q) c (post s Q))).
Proof.
  intros d p a pre post H.
  destruct game_not_relational as [c1 [c2 [E [s [Q [W1 W2]]]]]].
  apply W2. apply H. apply (proj1 (H c1 s Q)) in W1.
  rewrite cvalid_cvr in W1 |- *. simpl in *.
  exact (cvr_same_rel _ _ d p a _ _ E W1).
Qed.
