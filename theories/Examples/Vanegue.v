(** * Vanegue's adversarial-logic examples

    The three worked examples of Vanegue's adversarial logic (SAS 2022),
    stated and proved in the generated logic of [Adversarial.Interleaving].
    Each is an [attack]: an adversarial-logic triple, about the victim
    against the adversary run to completion, whose postcondition is a
    reachable state in which the adversary's assertion holds. The
    programs follow ILAL's encodings of the same examples.

    - Example 1, "trivial case" ([example1_attack]): the adversary sends
      a value above 10M and the victim replies [win = 1].
    - Example 2, "oscillating bit protocol" ([obt_round_success]): one
      round of the adversary's binary search on the victim's secret; once
      the guess equals the secret, the oracle answers [0].
    - Example 3, "equivalence testing" ([eqtest_attack]): two pricing
      services answer the same large order identically.

    As in ILAL, the programs are flat (no [local]: [local] leaves its
    variable arbitrary on exit, which would hide [res] from the final
    assertion), Example 2 is one round of the search with convergence
    assumed (as Vanegue's own derivation assumes), and Example 3 runs the
    two services one after the other. Values are naturals ([N]).

    Every proof applies only rules that hold for every language, as
    derivations in the generated logics:
    - each thread's part is a derivation in [ALv] with the rules of
      [Core.Rules]: [il_seq], [il_choice_l], [il_choice_r], [il_skip],
      and from a single state [il_act_pt] (one step of an atom) and
      [il_assume_pt] (a guard that holds);
    - the attack is a derivation in [AILv] with the segment rules of
      [Core.StepCore], which hold for every step relation:
      [sprov_trans] chains the phases, [sprov_embed] brings in a
      thread's derivation, [sprov_step] takes a transfer, and
      [sprov_from] starts from a state satisfying the precondition.
    The language contributes only facts about its semantics, as the
    rules' side conditions: what each atom does ([asem_read],
    [asem_assign], ...), that a thread's run is a run of the
    interleaving ([thread_l], [prefix_r], ...), and what a transfer does
    ([com_va], [com_av]). [norm] computes the state for them.

    The state updates use [functional_extensionality]; the generated
    logic uses [classic]. *)

From Stdlib Require Import String List NArith Lia.
From LogicTransformers.Core Require Import Rules StepCore.
From LogicTransformers.Adversarial Require Import AL Interleaving.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope N_scope.

(** ** Tactics for side conditions

    The one-state rules leave side conditions about the current state: a
    channel's head, a branch's guard, a computed value. [norm] computes
    the fields they mention, using the entry hypotheses for the initial
    state's fields. *)

Ltac hyps :=
  repeat match goal with
         | H : vch ?σ ?c = _ |- context [vch ?σ ?c] => rewrite H
         | H : ach ?σ ?c = _ |- context [ach ?σ ?c] => rewrite H
         | H : vs ?σ ?x = _ |- context [vs ?σ ?x] => rewrite H
         | H : avs ?σ ?x = _ |- context [avs ?σ ?x] => rewrite H
         end.
Ltac norm :=
  try unfold massume, only;
  cbn [mchan mstore mupd mchupd supd cupd vs vch avs ach
       String.eqb Ascii.eqb Bool.eqb app];
  hyps; cbn; hyps; cbn.

(** Applying the generic rules. Each tactic applies one generated rule
    and closes its side condition with a fact about the semantics. *)

(* [il_act_pt]: one step of an atom *)
Ltac atom :=
  apply il_act_pt;
  first [ eapply asem_read; norm; reflexivity
        | eapply asem_write; norm; reflexivity
        | eapply asem_assign; norm; reflexivity
        | apply asem_adv ].

(* [il_assume_pt]: the state passes the guard *)
Ltac branch := apply il_assume_pt; norm; try reflexivity; lia.

(* [sprov_embed]: a thread's derivation, the other side waiting *)
Ltac victim f :=
  eapply (sprov_embed istep AILv (asem Victim) (ALv Victim));
  [intros ? ? Hk; apply f; exact Hk | cbn [tenc]].
Ltac adversary f :=
  eapply (sprov_embed istep AILv (asem Adversary) (ALv Adversary));
  [intros ? ? Hk; apply f; exact Hk | cbn [tenc]].

(* [sprov_step]: one transfer *)
Ltac xfer c :=
  apply sprov_step;
  first [ eapply (com_av _ _ c); norm; reflexivity
        | eapply (com_va _ _ c); norm; reflexivity ].

(** ** Example 1: the trivial case

<<
      Victim:                         Adversary:
        read(s, n);                     val := alpha;
        if (n > 10M) win := 1           write(s, val);
        else win := 0;                  read(s, res);
        write(s, win)                   adv_assert(res == 1)
>> *)

Definition TEN_M : N := 10000000.

Definition prog1 : tcom :=
  TSeq (TAtom (ARead "s" "n"))
  (TSeq
    (TChoice
      (TSeq (TAssume (fun st => st "n" > TEN_M))
            (TAtom (AAsgn "win" (fun _ => 1))))
      (TSeq (TAssume (fun st => st "n" <= TEN_M))
            (TAtom (AAsgn "win" (fun _ => 0)))))
    (TAtom (AWrite "s" "win"))).

Definition adv1 (alpha : N) : tcom :=
  TSeq (TAtom (AAsgn "val" (fun _ => alpha)))
  (TSeq (TAtom (AWrite "s" "val"))
  (TSeq (TAtom (ARead "s" "res"))
        (TAtom (AAdvAssert (fun st => st "res" = 1))))).

Definition init : estate :=
  mkE (fun _ => 0) (fun _ => []) (fun _ => 0) (fun _ => []).

Theorem example1_attack : forall alpha, alpha > TEN_M ->
    attack (only init) (prog1, adv1 alpha) (fun σ => avs σ "res" = 1).
Proof.
  intros alpha Hbig. eapply attack_intro.
  (* the adversary sets [val] and sends it *)
  eapply sprov_trans; [adversary prefix_r; atom |].
  eapply sprov_trans; [adversary prefix_r; atom |].
  eapply sprov_trans; [xfer "s" |].
  (* the victim reads it, takes the [n > 10M] branch, and replies *)
  eapply sprov_trans; [victim thread_l |].
  { eapply il_seq; [atom |]. eapply il_seq; [| atom].
    apply il_choice_l. eapply il_seq; [branch | atom]. }
  eapply sprov_trans; [xfer "s" |].
  (* the adversary reads [win = 1] and asserts *)
  adversary thread_r. eapply il_seq; atom.
  (* the final state satisfies the adversary's goal *)
  norm. reflexivity.
Qed.

(** ** Example 2: the oscillating bit protocol

<<
      Victim (one round):             Adversary (one round):
        read(sock, cred);               write(sock, guess);
        if secret == cred then          read(sock, ret);
          err := 0                      if ret == 1 then guess -= step
        else if secret < cred then      else if ret == 2 then guess += step;
          err := 1                      step := step/2 + 1;
        else err := 2;                  adv_assert(ret == 0)
        write(sock, err)
>>

    The adversary binary-searches the victim's secret through the
    three-valued oracle [err]. We prove the round in which the guess has
    reached the secret: the oracle answers [0] and the assertion holds.
    Convergence of the search is assumed, as in Vanegue's derivation. *)

Definition err_branch : tcom :=
  TChoice
    (TSeq (TAssume (fun st => st "secret" = st "cred"))
          (TAtom (AAsgn "err" (fun _ => 0))))
  (TChoice
    (TSeq (TAssume (fun st => st "secret" < st "cred"))
          (TAtom (AAsgn "err" (fun _ => 1))))
    (TSeq (TAssume (fun st => st "secret" > st "cred"))
          (TAtom (AAsgn "err" (fun _ => 2))))).

Definition prog2 : tcom :=
  TSeq (TAtom (ARead "sock" "cred"))
  (TSeq err_branch (TAtom (AWrite "sock" "err"))).

Definition guess_branch : tcom :=
  TChoice
    (TSeq (TAssume (fun st => st "ret" = 1))
          (TAtom (AAsgn "guess" (fun st => st "guess" - st "step"))))
  (TChoice
    (TSeq (TAssume (fun st => st "ret" = 2))
          (TAtom (AAsgn "guess" (fun st => st "guess" + st "step"))))
    (TSeq (TAssume (fun st => st "ret" <> 1 /\ st "ret" <> 2)) TSkip)).

Definition adv2 : tcom :=
  TSeq (TAtom (AWrite "sock" "guess"))
  (TSeq (TAtom (ARead "sock" "ret"))
  (TSeq guess_branch
  (TSeq (TAtom (AAsgn "step" (fun st => st "step" / 2 + 1)))
        (TAtom (AAdvAssert (fun st => st "ret" = 0)))))).

(** At the round's start the guess equals the secret and the channel is
    empty on both sides. *)
Definition round_entry (v : N) (σ : estate) : Prop :=
  vs σ "secret" = v /\ avs σ "guess" = v /\
  vch σ "sock" = [] /\ ach σ "sock" = [].

Theorem obt_round_success : forall v σ0, round_entry v σ0 ->
    attack (round_entry v) (prog2, adv2) (fun σ => avs σ "ret" = 0).
Proof.
  intros v σ0 Hentry. pose proof Hentry as [Hs [Hg [Hv Ha]]].
  eapply attack_intro;
    [apply (sprov_from istep AILv _ _ σ0); [exact Hentry |] |].
  (* the adversary sends its guess *)
  eapply sprov_trans; [adversary prefix_r; atom |].
  eapply sprov_trans; [xfer "sock" |].
  (* the victim compares it with the secret: equal, so [err = 0] *)
  eapply sprov_trans; [victim thread_l |].
  { eapply il_seq; [atom |]. eapply il_seq; [| atom].
    apply il_choice_l. eapply il_seq; [branch | atom]. }
  eapply sprov_trans; [xfer "sock" |].
  (* the adversary reads [0], keeps its guess, and asserts *)
  adversary thread_r. eapply il_seq; [atom |].
  eapply il_seq.
  { apply il_choice_r, il_choice_r. eapply il_seq; [branch | apply il_skip]. }
  eapply il_seq; atom.
  (* the final state satisfies the adversary's goal *)
  norm. reflexivity.
Qed.

(** ** Example 3: equivalence testing

<<
      Victim (two services):                Adversary:
        read(s1, ord);                        write(s1, num);
        dec := ord / 10M;                     read(s1, guess1);
        if ord <= 9M then                     write(s2, num);
          curp := initp * (1 - dec)           read(s2, guess2);
        else curp := initp / 10;              adv_assert(guess1 == guess2)
        write(s1, curp);
        (the same on s2, with 20M and 18M)
>>

    The adversary sends the same large order to both services and
    asserts that they quote the same price. Both take their large-order
    branch and answer [initp / 10]. *)

Local Notation V9M := 9000000.
Local Notation V10M := 10000000.
Local Notation V18M := 18000000.
Local Notation V20M := 20000000.

Definition getprice : tcom :=
  TSeq (TAtom (ARead "s1" "ord"))
  (TSeq (TAtom (AAsgn "dec" (fun st => st "ord" / V10M)))
  (TSeq (TChoice
          (TSeq (TAssume (fun st => st "ord" <= V9M))
                (TAtom (AAsgn "curp" (fun st => st "initp" * (1 - st "dec")))))
          (TSeq (TAssume (fun st => st "ord" > V9M))
                (TAtom (AAsgn "curp" (fun st => st "initp" / 10)))))
        (TAtom (AWrite "s1" "curp")))).

Definition getprice2 : tcom :=
  TSeq (TAtom (ARead "s2" "ord2"))
  (TSeq (TAtom (AAsgn "dec2" (fun st => st "ord2" / V20M)))
  (TSeq (TChoice
          (TSeq (TAssume (fun st => st "ord2" <= V18M))
                (TAtom (AAsgn "curp2"
                          (fun st => st "initp" * (1 - st "dec2")))))
          (TSeq (TAssume (fun st => st "ord2" > V18M))
                (TAtom (AAsgn "curp2" (fun st => st "initp" / 10)))))
        (TAtom (AWrite "s2" "curp2")))).

Definition prog3 : tcom := TSeq getprice getprice2.

Definition adv3 : tcom :=
  TSeq (TAtom (AWrite "s1" "num"))
  (TSeq (TAtom (ARead "s1" "guess1"))
  (TSeq (TAtom (AWrite "s2" "num"))
  (TSeq (TAtom (ARead "s2" "guess2"))
        (TAtom (AAdvAssert (fun st => st "guess1" = st "guess2")))))).

Definition eqtest_entry (num : N) (σ : estate) : Prop :=
  avs σ "num" = num /\ num > V18M /\
  vch σ "s1" = [] /\ ach σ "s1" = [] /\
  vch σ "s2" = [] /\ ach σ "s2" = [].

Theorem eqtest_attack : forall num σ0, eqtest_entry num σ0 ->
    attack (eqtest_entry num) (prog3, adv3)
           (fun σ => avs σ "guess1" = avs σ "guess2").
Proof.
  intros num σ0 Hentry.
  pose proof Hentry as [Hn [Hbig [Hv1 [Ha1 [Hv2 Ha2]]]]].
  eapply attack_intro;
    [apply (sprov_from istep AILv _ _ σ0); [exact Hentry |] |].
  (* the order goes to service 1, which quotes [initp / 10] *)
  eapply sprov_trans; [adversary prefix_r; atom |].
  eapply sprov_trans; [xfer "s1" |].
  eapply sprov_trans; [victim prefix_l |].
  { eapply il_seq; [atom |]. eapply il_seq; [atom |].
    eapply il_seq; [| atom].
    apply il_choice_r. eapply il_seq; [branch | atom]. }
  eapply sprov_trans; [xfer "s1" |].
  eapply sprov_trans; [adversary prefix_r; atom |].
  (* the same order goes to service 2, which quotes the same *)
  eapply sprov_trans; [adversary prefix_r; atom |].
  eapply sprov_trans; [xfer "s2" |].
  eapply sprov_trans; [victim thread_l |].
  { eapply il_seq; [atom |]. eapply il_seq; [atom |].
    eapply il_seq; [| atom].
    apply il_choice_r. eapply il_seq; [branch | atom]. }
  eapply sprov_trans; [xfer "s2" |].
  (* the adversary reads the second quote and asserts *)
  adversary thread_r. eapply il_seq; atom.
  (* the final state satisfies the adversary's goal *)
  norm. reflexivity.
Qed.
