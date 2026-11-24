(** * Imp: syntax, states, and expression evaluation *)

From Stdlib Require Import String Bool Arith.

Notation var := string.

(** Program states are total maps from variables to naturals. *)
Definition state := var -> nat.

Definition empty_state : state := fun _ => 0.

Definition update (st : state) (x : var) (v : nat) : state :=
  fun y => if String.eqb x y then v else st y.

Lemma update_eq : forall st x v, update st x v x = v.
Proof. intros. unfold update. now rewrite String.eqb_refl. Qed.

Lemma update_neq : forall st x y v, x <> y -> update st x v y = st y.
Proof.
  intros st x y v Hneq. unfold update.
  destruct (String.eqb_spec x y); [contradiction | reflexivity].
Qed.

(** ** Syntax *)

Inductive aexp : Type :=
  | ANum (n : nat)
  | AVar (x : var)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Inductive com : Type :=
  | CSkip
  | CAsgn (x : var) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
  | CChoice (c1 c2 : com)   (* nondeterministic choice  c1 (+) c2 *)
  | CHavoc (x : var).       (* nondeterministic assignment  x := * *)

(** ** Expression evaluation

    Expressions are pure and total, so both command semantics share these
    evaluation functions; the small-/big-step distinction is at the level
    of commands. *)

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AVar x => st x
  | APlus a1 a2 => aeval st a1 + aeval st a2
  | AMinus a1 a2 => aeval st a1 - aeval st a2
  | AMult a1 a2 => aeval st a1 * aeval st a2
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => Nat.eqb (aeval st a1) (aeval st a2)
  | BLe a1 a2 => Nat.leb (aeval st a1) (aeval st a2)
  | BNot b1 => negb (beval st b1)
  | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  end.

(** ** Concrete syntax: [<{ ... }>]

    Inside [<{ }>]: string literals and naturals are variables and
    constants; [+ - *] arithmetic; [= <= >] comparisons, [~] and [&&];
    [skip], [x := a], [c1 ; c2], [if b then c1 else c2 end],
    [while b do c end], [c1 ⊕ c2] (choice) and [havoc x]. *)

Arguments AVar _%_string_scope.
Arguments CAsgn _%_string_scope _.
Arguments CHavoc _%_string_scope.

Coercion AVar : string >-> aexp.
Coercion ANum : nat >-> aexp.

Declare Custom Entry com.
Declare Scope com_scope.

Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "x + y" := (APlus x y)
  (in custom com at level 50, left associativity) : com_scope.
Notation "x - y" := (AMinus x y)
  (in custom com at level 50, left associativity) : com_scope.
Notation "x * y" := (AMult x y)
  (in custom com at level 40, left associativity) : com_scope.
Notation "'true'" := BTrue (in custom com at level 0) : com_scope.
Notation "'false'" := BFalse (in custom com at level 0) : com_scope.
Notation "x <= y" := (BLe x y)
  (in custom com at level 70, no associativity) : com_scope.
Notation "x = y" := (BEq x y)
  (in custom com at level 70, no associativity) : com_scope.
Notation "x > y" := (BNot (BLe x y))
  (in custom com at level 70, no associativity) : com_scope.
Notation "x && y" := (BAnd x y)
  (in custom com at level 80, left associativity) : com_scope.
Notation "'~' b" := (BNot b)
  (in custom com at level 75, right associativity) : com_scope.
Notation "'skip'" := CSkip (in custom com at level 0) : com_scope.
Notation "x := y" := (CAsgn x y)
  (in custom com at level 0, x constr at level 0, y at level 85,
   no associativity) : com_scope.
Notation "'havoc' x" := (CHavoc x)
  (in custom com at level 0, x constr at level 0) : com_scope.
Notation "x ; y" := (CSeq x y)
  (in custom com at level 90, right associativity) : com_scope.
Notation "x ⊕ y" := (CChoice x y)
  (in custom com at level 88, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" := (CIf x y z)
  (in custom com at level 89, x at level 99, y at level 99, z at level 99)
  : com_scope.
Notation "'while' x 'do' y 'end'" := (CWhile x y)
  (in custom com at level 89, x at level 99, y at level 99) : com_scope.
