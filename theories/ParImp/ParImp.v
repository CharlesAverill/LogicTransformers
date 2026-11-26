(** * Concurrent Imp

    Imp with parallel composition [p1 ∥ p2], under an interleaving
    small-step semantics: each assignment, test and loop unfolding is one
    atomic step, as is an atomic multiple assignment [PMulti] (used for
    auxiliary variables), and a parallel composition steps either side. The
    scheduler is unfair, so a thread can be starved forever.

    The language is an instance of [Core.SmallStepCore]: [ParImp] (top
    face), [ParImpB] (bottom face), and the encoding [penc] into the core,
    with every cube validity transferring between a program and its
    encoding ([penc_cvalid], [penc_cvalid_bot]).

    Concrete syntax: inside [<{ }>] with [pcom_scope] open, the Imp
    notations ([Imp.Syntax]) build concurrent programs, plus [p1 ∥ p2].
    [∥] binds looser than [;], so [a ; b ∥ c ; d] runs two threads. *)

From Stdlib Require Import String.
From LogicTransformers.Imp Require Import Syntax.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Relational.
From LogicTransformers.Core Require Import Kernel KernelBot SmallStepCore.

Inductive pcom : Type :=
  | PSkip
  | PAsgn (x : var) (a : aexp)
  | PSeq (p1 p2 : pcom)
  | PIf (b : bexp) (p1 p2 : pcom)
  | PWhile (b : bexp) (p : pcom)
  | PPar (p1 p2 : pcom)
  | PMulti (l : list (var * aexp)).  (* atomic multiple assignment *)

Arguments PAsgn _%_string_scope _.

Notation pcfg := (pcom * state)%type.

(** An atomic multiple assignment runs its assignments in order, as one
    step: it is how auxiliary variables are updated together with real
    ones. *)
Fixpoint massign (l : list (var * aexp)) (s : state) : state :=
  match l with
  | nil => s
  | cons (x, a) l => massign l (update s x (aeval s a))
  end.

Inductive pstep : pcfg -> pcfg -> Prop :=
  | PS_Asgn : forall x a s, pstep (PAsgn x a, s) (PSkip, update s x (aeval s a))
  | PS_SeqSkip : forall p s, pstep (PSeq PSkip p, s) (p, s)
  | PS_Seq : forall p1 p1' p2 s s',
      pstep (p1, s) (p1', s') -> pstep (PSeq p1 p2, s) (PSeq p1' p2, s')
  | PS_IfT : forall b p1 p2 s,
      beval s b = true -> pstep (PIf b p1 p2, s) (p1, s)
  | PS_IfF : forall b p1 p2 s,
      beval s b = false -> pstep (PIf b p1 p2, s) (p2, s)
  | PS_While : forall b p s,
      pstep (PWhile b p, s) (PIf b (PSeq p (PWhile b p)) PSkip, s)
  | PS_ParL : forall p1 p1' p2 s s',
      pstep (p1, s) (p1', s') -> pstep (PPar p1 p2, s) (PPar p1' p2, s')
  | PS_ParR : forall p1 p2 p2' s s',
      pstep (p2, s) (p2', s') -> pstep (PPar p1 p2, s) (PPar p1 p2', s')
  | PS_ParDone : forall s, pstep (PPar PSkip PSkip, s) (PSkip, s)
  | PS_Multi : forall l s, pstep (PMulti l, s) (PSkip, massign l s).

Lemma pskip_stuck : forall s k', ~ pstep (PSkip, s) k'.
Proof. intros s k' H. inversion H. Qed.

Lemma pskip_dec : forall p, p = PSkip \/ p <> PSkip.
Proof. intros []; (left; reflexivity) || (right; discriminate). Qed.

(** ** The language and its encoding *)

Definition ParImp : Language := SLang pstep PSkip.
Definition ParImpB : Language := SLangB pstep PSkip.

Notation pact := (sact pcom).
Definition pact_sem : pact -> pcfg -> pcfg -> Prop := sact_sem pstep.
Definition penc : pcom -> kcom pcfg pact := senc PSkip.
Notation prunning := (@running pcom state PSkip).
Notation pfin := (@fin pcom state PSkip).
Notation pfinB := (@finB pcom state PSkip).

Theorem penc_cvalid : forall d p a (P Q : state -> Prop) c,
    cvalid d p a (@mkTriple ParImp P c Q) <->
    cvalid d p a (@mkTriple (KLang pact_sem) (fun k => P (snd k)) (penc c)
                    (liftG snd pfin d p a Q)).
Proof.
  intros. apply senc_cvalid; [exact pskip_stuck | exact pskip_dec].
Qed.

Theorem penc_cvalid_bot : forall d p a (P Q : option state -> Prop) c,
    cvalid d p a (@mkTriple ParImpB P c Q) <->
    cvalid d p a (@mkTriple (KLangB pact_sem)
                    (fun o => P (option_map snd o)) (penc c)
                    (liftG (option_map snd) pfinB d p a Q)).
Proof.
  intros. apply senc_cvalid_bot; [exact pskip_stuck | exact pskip_dec].
Qed.

(** ** Concrete syntax *)

Declare Scope pcom_scope.

Notation "'skip'" := PSkip (in custom com at level 0) : pcom_scope.
Notation "x := y" := (PAsgn x y)
  (in custom com at level 0, x constr at level 0, y at level 85,
   no associativity) : pcom_scope.
Notation "x ; y" := (PSeq x y)
  (in custom com at level 90, right associativity) : pcom_scope.
Notation "'if' x 'then' y 'else' z 'end'" := (PIf x y z)
  (in custom com at level 89, x at level 99, y at level 99, z at level 99)
  : pcom_scope.
Notation "'while' x 'do' y 'end'" := (PWhile x y)
  (in custom com at level 89, x at level 99, y at level 99) : pcom_scope.
Notation "x ∥ y" := (PPar x y)
  (in custom com at level 92, right associativity) : pcom_scope.
