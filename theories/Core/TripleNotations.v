(** * Notations for triples in a record

    For a record [V] (a verified logic, see [Framework.Verified]) over a
    core language:

<<
      V ⊢ {{ P }} c {{ Q }}      HL     (top face)
      V ⊢ ⟦ P ⟧ c ⟦ Q ⟧          IL     (top face)
      V ⊢⊥ {{ P }} c {{ Q }}     HL⊥    (bottom face)
      V ⊢⊥ ⟦ P ⟧ c ⟦ Q ⟧         IL⊥    (bottom face)
>>

    Assertions are predicates, e.g. [{{ fun s => fst s <= 5 }}]. The
    notations only apply to records at the matching node, so goals in
    proofs print with them. IL uses [⟦ ⟧] rather than [[[ ]]], which
    would clash with nested intro patterns. *)

From LogicTransformers.Framework Require Import Cube Verified.
From LogicTransformers.Core Require Import Rules RulesBot.

Declare Scope triple_scope.

Notation "V ⊢ {{ P }} c {{ Q }}" :=
  (@prov _ _ _ Forward Plain Over V P c Q)
  (at level 70, P at level 99, c at level 99, Q at level 99,
   format "V  ⊢  {{  P  }}  c  {{  Q  }}") : triple_scope.

Notation "V ⊢ ⟦ P ⟧ c ⟦ Q ⟧" :=
  (@prov _ _ _ Forward Plain Under V P c Q)
  (at level 70, P at level 99, c at level 99, Q at level 99,
   format "V  ⊢  ⟦  P  ⟧  c  ⟦  Q  ⟧") : triple_scope.

Notation "V ⊢⊥ {{ P }} c {{ Q }}" :=
  (@provb _ _ _ Forward Plain Over V P c Q)
  (at level 70, P at level 99, c at level 99, Q at level 99,
   format "V  ⊢⊥  {{  P  }}  c  {{  Q  }}") : triple_scope.

Notation "V ⊢⊥ ⟦ P ⟧ c ⟦ Q ⟧" :=
  (@provb _ _ _ Forward Plain Under V P c Q)
  (at level 70, P at level 99, c at level 99, Q at level 99,
   format "V  ⊢⊥  ⟦  P  ⟧  c  ⟦  Q  ⟧") : triple_scope.

