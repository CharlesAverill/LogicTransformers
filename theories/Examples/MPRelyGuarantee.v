(** * Message passing, thread by thread

    The program of [Examples.ParExample]:

<<
      mp  =  while f = 0 do skip end ; y := x     (reader)
          ∥  x := 42 ; f := 1                      (writer)
>>

    [ParExample.mp_HL] proves [{f = 0} mp {y = 42}] with one global
    invariant over both threads' positions. Here the same result is
    proved thread-modularly, with rely/guarantee ([ParImp.RelyGuarantee]),
    and each thread is verified on its own:

    - the writer guarantees [Gw]: it never changes [y]; once [f ≠ 0] it
      changes neither [f] nor [x]; and whenever it makes [f ≠ 0], [x] is
      already 42;
    - the reader guarantees [Gr]: it only writes [y];
    - each thread relies on the other's guarantee.

    The reader's loop invariant is [f ≠ 0 → x = 42], stable under [Gw].
    The parallel rule combines the two proofs, and [rg_closed_hl] turns
    the result into the cube's Hoare validity for [mp]
    ([mp_correct_rg]); [rg_derive_HL] gives a derivation in the HL
    record. Axiom-free. *)

From Stdlib Require Import String Arith.
From LogicTransformers.Imp Require Import Syntax.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Relational Verified.
From LogicTransformers.Core Require Import Kernel SmallStepCore.
From LogicTransformers.ParImp Require Import ParImp RelyGuarantee.
From LogicTransformers.Examples Require Import Common ParExample.

Local Open Scope string_scope.
Local Notation X := "x".
Local Notation Y := "y".
Local Notation F := "f".

(** ** The two guarantees *)

Definition Gw (s s' : state) : Prop :=
  s' = s \/
  (s' Y = s Y /\
   (s F <> 0 -> s' F = s F /\ s' X = s X) /\
   (s' F <> 0 -> s' X = 42)).

Definition Gr (s s' : state) : Prop := forall z, z <> Y -> s' z = s z.

Lemma Gw_refl : forall s, Gw s s.
Proof. intros s. left. reflexivity. Qed.

Lemma Gr_refl : forall s, Gr s s.
Proof. intros s z _. reflexivity. Qed.

Local Notation g := (BEq (AVar F) (ANum 0)).

Lemma g_false : forall s, beval s g = false <-> s F <> 0.
Proof. intros s. simpl. apply Nat.eqb_neq. Qed.

(** ** The reader, relying on the writer's guarantee *)

Definition Inv (s : state) : Prop := s F <> 0 -> s X = 42.

Lemma Inv_stable : stable Gw Inv.
Proof.
  intros s s' Hi [-> | [_ [_ H3]]]; [exact Hi |]. exact H3.
Qed.

Lemma Exit_stable : stable Gw (fun s => Inv s /\ beval s g = false).
Proof.
  intros s s' [Hi Hf] [-> | [_ [H2 _]]]; [auto |].
  apply g_false in Hf. destruct (H2 Hf) as [Ef Ex].
  split; [intros _; rewrite Ex; apply Hi, Hf |].
  apply g_false. rewrite Ef. exact Hf.
Qed.

Lemma Done_stable : stable Gw (fun s => s Y = 42).
Proof. intros s s' H [-> | [Hy _]]; [exact H | rewrite Hy; exact H]. Qed.

Theorem reader_rg : rg Gw Gr (fun s => s F = 0) reader (fun s => s Y = 42).
Proof.
  apply (RG_Seq _ _ _ (fun s => Inv s /\ beval s g = false));
    [apply Gr_refl | |].
  - apply (RG_Cons _ Gw _ Gr _ Inv _ (fun s => Inv s /\ beval s g = false));
      [intros s H Hf; contradiction | auto | auto | auto |].
    apply RG_While; [apply Gr_refl | exact Inv_stable | exact Exit_stable |].
    apply (RG_Cons _ Gw _ Gr _ Inv _ Inv);
      [intros s [H _]; exact H | auto | auto | auto |].
    apply RG_Skip. exact Inv_stable.
  - apply RG_Asgn; [exact Exit_stable | exact Done_stable |].
    intros s [Hi Hf]. apply g_false in Hf. split.
    + rewrite update_eq. simpl. exact (Hi Hf).
    + intros z Hz. apply update_neq. intros E. apply Hz. symmetry. exact E.
Qed.

(** ** The writer, relying on the reader's guarantee *)

Lemma Gr_keeps : forall s s' z, Gr s s' -> z <> Y -> s' z = s z.
Proof. intros s s' z H Hz. exact (H z Hz). Qed.

Theorem writer_rg : rg Gr Gw (fun s => s F = 0) writer (fun _ => True).
Proof.
  apply (RG_Seq _ _ _ (fun s => s F = 0 /\ s X = 42)); [apply Gw_refl | |].
  - apply RG_Asgn.
    + intros s s' H HG. rewrite (Gr_keeps s s' F HG); [exact H | discriminate].
    + intros s s' [H1 H2] HG.
      rewrite (Gr_keeps s s' F HG), (Gr_keeps s s' X HG); auto; discriminate.
    + intros s Hf. split.
      * split; [rewrite update_neq; [exact Hf | discriminate] |].
        apply update_eq.
      * right. split; [apply update_neq; discriminate |]. split.
        -- intros Hn. contradiction.
        -- intros Hn. rewrite update_neq in Hn by discriminate. contradiction.
  - apply RG_Asgn.
    + intros s s' [H1 H2] HG.
      rewrite (Gr_keeps s s' F HG), (Gr_keeps s s' X HG); auto; discriminate.
    + intros s s' _ _. exact I.
    + intros s [Hf Hx]. split; [exact I |].
      right. split; [apply update_neq; discriminate |]. split.
      * intros Hn. contradiction.
      * intros _. rewrite update_neq by discriminate. exact Hx.
Qed.

(** ** Composed *)

Theorem mp_rg : rg (fun _ _ => False) (fun _ _ => True)
                   (fun s => s F = 0) mp (fun s => s Y = 42).
Proof.
  apply (RG_Cons _ (fun _ _ => False) _ (fun _ _ => True)
           _ (fun s => s F = 0 /\ s F = 0) _ (fun s => s Y = 42 /\ True));
    [auto | auto | auto | intros s [H _]; exact H |].
  apply (RG_Par _ _ Gw Gr Gr Gw);
    [intros; exact I | intros s s' [[] | H]; exact H
    | intros s s' [[] | H]; exact H | intros; exact I
    | exact reader_rg | exact writer_rg].
Qed.

(** The thread-modular proof gives the cube's Hoare validity for [mp]. *)
Corollary mp_correct_rg :
  cvalid Forward Plain Over
    (@mkTriple ParImp (fun s => s F = 0) mp (fun s => s Y = 42)).
Proof. exact (rg_closed_hl _ _ _ _ (rg_sound _ _ _ _ _ mp_rg)). Qed.

(** And a derivation in the Hoare-logic record of [Examples.Common]. *)
Corollary mp_HL_from_rg :
  derivable (rules (vl_logic (HLv pact_sem)))
    (@mkTriple (KLang pact_sem) (fun k => snd k F = 0) (penc mp)
       (liftG snd pfin Forward Plain Over (fun s => s Y = 42))).
Proof. exact (rg_derive_HL (HLv pact_sem) _ _ _ _ mp_rg). Qed.
