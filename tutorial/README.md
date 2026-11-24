# Instantiating LogicTransformers: a conceptual overview

See [`theories/Tutorial/ImpTutorial.v`](../theories/Tutorial/ImpTutorial.v)

This tutorial is for someone who knows Rocq and has seen Hoare logic, but
has never looked at this project. By the end you'll know how to take a
programming language you have defined in Rocq, get sixteen program logics
for it, prove things about programs in those logics, and end up with
ordinary Rocq theorems about your programs. Our running example is Imp,
the small imperative language from *Software Foundations*, extended with
nondeterministic choice. Everything shown here is in the file linked
above, and the build checks it.

## What you get

You know Hoare triples: `{P} c {Q}` says that if `c` starts in a state
satisfying `P` and finishes, it finishes in a state satisfying `Q`. Hoare
logic is a set of rules for proving such triples.

Hoare logic is one of a family. Patrick Cousot (POPL 2024) organized
sixteen related logics in a diagram now called Cousot's cube. Each one
reads the same triple `{P} c {Q}` in a different way. The four you are
most likely to meet are:

| Logic | `{P} c {Q}` means | Typical use |
|---|---|---|
| Hoare logic (HL) | every run from a `P` state ends in a `Q` state | proving correctness |
| Incorrectness logic (IL) | every `Q` state is the end of some run from a `P` state | proving a bug is really reachable |
| Necessary conditions (NC) | every run that ends in a `Q` state started in a `P` state | finding what a bad outcome requires |
| Sufficient incorrectness (SIL) | every `P` state has some run ending in a `Q` state | proving a bad outcome can't be avoided |

Here a *run* is one possible execution. A program can have several runs
from the same state if it makes nondeterministic choices. The cube has
four more logics, which read the triple with "all" and "some" swapped
around. You rarely prove those directly, as we'll see.

That makes eight. Each of the eight also comes in a version that sees
nontermination. In the ordinary version, a run that loops forever never
ends, so it says nothing about `Q`. In the nontermination-aware version,
a run that loops forever is treated as ending in a special outcome ⊥
("bottom"), so a postcondition can mention it. For example, "this program
can loop forever from `P`" is an IL triple whose postcondition is ⊥. We
write the nontermination-aware versions with a ⊥, as in HL⊥. Eight
logics, two versions each: sixteen.

This project gives you all sixteen for your language. For each one you
get proof rules, a proof that the rules are sound (they only prove true
triples), and a proof that they are complete (they can prove every true
triple). You don't write any of the rules yourself.

## How it works

Building a program logic means writing rules for every construct of a
language and proving them sound and complete. Doing that sixteen times
for every new language would be a lot of work, so the project does it
once, for one small built-in language that we'll call the *core
language*. To use the logics for your language, you *translate* each of
your programs into a core program that behaves exactly the same way. The
project proves that a triple holds for your program exactly when the
corresponding triple holds for its translation. So you prove things about
the translation, using the core language's rules, and then carry the
results back to your program.

Three things are needed, and the rest of the tutorial goes through them:
1. the core language, and the logics for it, which the project provides;
2. a translation of your language into the core, with a proof that it
   behaves the same, which the project builds for you once you give a
   step relation for your language;
3. a way to move triples between your program and its translation, which
   the project also provides.

## The core language

The core language is deliberately tiny, so that its logics are easy to
build. It has no variables, assignments or expressions of its own.
Instead it is generic in two types:
- `Σ`, the type of states;
- `Act`, a type of *atomic actions*: the basic operations, like "assign
  this variable". You choose what they are, and you give their meaning
  as a relation `act_sem : Act -> Σ -> Σ -> Prop`, where `act_sem a s s'`
  means "action `a` can take state `s` to `s'`". An action can be
  nondeterministic, so there may be several such `s'`.

Programs are then built from actions with a few fixed constructs:
- `KSkip` does nothing;
- `KAct a` performs action `a`;
- `KAssume B` continues only from states satisfying `B`, and otherwise
  has no run at all;
- `KSeq c1 c2` runs `c1`, then `c2`;
- `KChoice c1 c2` runs either `c1` or `c2`, chosen nondeterministically;
- `KStar c` runs `c` any number of times, including zero.

In Rocq (`Core/Kernel.v`):

```coq
Inductive kcom : Type :=
  | KSkip
  | KAct (a : Act)
  | KAssume (B : Σ -> Prop)
  | KSeq (c1 c2 : kcom)
  | KChoice (c1 c2 : kcom)
  | KStar (c : kcom).
```

A `while` loop isn't built in, because it can be expressed with the other
constructs: "while `B`, run `c`" is "repeat (check `B`, then run `c`) any
number of times, then check that `B` is false". The checks use `KAssume`,
so runs that check `B` at the wrong moment simply don't exist:

```coq
kwhile B c := KSeq (KStar (KSeq (KAssume B) c)) (KAssume (fun s => ~ B s))
```

## Three ways to translate a language

There are three ways to turn your programs into core programs:

1. **Write the language in the core directly.** Your programs are core
   programs, and you only choose the atomic actions.
   `Examples/RobotExample.v` does this.
2. **Translate construct by construct.** For example, Imp's assignment
   becomes an action, and Imp's `while` becomes `kwhile`. You then prove
   that the translation behaves the same as the original. The repository
   does this for Imp in `Core/ImpCore.v`. The payoff is that the core's
   rules then work like rules for your own constructs.
3. **Give a small-step semantics,** and let the project build the
   translation and prove it correct (`Core/SmallStepCore.v`). This is the
   least work, since you only need your language's semantics.

We'll use the third way, as you would for a language of your own.

## Step 1: Imp's step relation

Imp (`Imp/Syntax.v`) has arithmetic and boolean expressions, assignment,
sequencing, `if`, `while`, nondeterministic choice, and `havoc`, which
assigns an arbitrary number to a variable. A state is a function from
variable names to numbers.

A small-step semantics describes execution one step at a time. At each
moment, there is a program still to run and a current state. We call
such a pair a *configuration*. A step turns one configuration into
another. When the program still to run is `CSkip`, there is nothing left
to do, and the run has finished.

Imp already has a small-step semantics (`Imp/SmallStep.v`): `cstep c s c'
s'` says that configuration `(c, s)` can step to `(c', s')`. A few of its
rules:

```coq
  | S_Asgn : forall x a st,
      cstep (CAsgn x a) st CSkip (update st x (aeval st a))
  | S_SeqSkip : forall c2 st,
      cstep (CSeq CSkip c2) st c2 st
  | S_While : forall b c st,
      cstep (CWhile b c) st (CIf b (CSeq c (CWhile b c)) CSkip) st
  | S_ChoiceL : forall c1 c2 st,
      cstep (CChoice c1 c2) st c1 st
```

The project expects a step relation between configurations written as
pairs, so we repackage `cstep` without changing it:

```coq
Definition istep (k k' : com * state) : Prop :=
  cstep (fst k) (snd k) (fst k') (snd k').
```

## Step 2: two facts about the finished program

The project needs to know which program means "finished", and two facts
about it. For Imp, the finished program is `CSkip`. The first fact is
that a finished program takes no more steps. The project uses this to
know that a run which reaches `CSkip` has really ended. The second is
that we can tell whether a program is finished, which the project needs
in order to decide when to stop stepping.

```coq
Lemma skip_stuck : forall s k', ~ istep (CSkip, s) k'.
Proof. intros s [c' s'] H. inversion H. Qed.

Lemma skip_dec : forall c, c = CSkip \/ c <> CSkip.
Proof. intros []; (left; reflexivity) || (right; discriminate). Qed.
```

Those two lemmas are everything the project asks for. The next three
steps describe what it builds from them.

## Step 3: what a step relation means

Before the project can translate Imp programs, it has to know what an
Imp program *does*, as determined by the step relation. That meaning has
two parts, one for each version of the logics.

**Which runs finish, and where.** Running `c` from state `s` can end in
state `s'` when some sequence of steps takes `(c, s)` to `(CSkip, s')`.
The project writes "some sequence of zero or more steps" as `smulti`.
This is all the ordinary logics need, so the project packages it as a
language, `ImpS := SLang istep CSkip`:

```coq
Definition SLang : Language :=
  mkLanguage Prog St (fun p s s' => smulti (p, s) (done, s')).
```

Here `Prog` and `St` are the types of programs and states (for Imp, `com`
and `state`), `done` is the finished program (`CSkip`), and a `Language`
is just programs, states, and this "can end in" relation.

**Which runs loop forever.** The nontermination-aware logics also need to
know from which states the program can run forever. That happens when the
steps can go on infinitely. The project writes this as `sdiv` ("diverges",
defined coinductively). To fit nontermination into the same "can end in"
shape as before, it uses states of type `option state`. `Some s` is an
ordinary state, and `None` is ⊥, the outcome "ran forever". The
nontermination-aware language is `ImpSB := SLangB istep CSkip`, and its
"can end in" relation has four cases:
- from `Some s` to `Some s'`: the program can finish in `s'`, as before;
- from `Some s` to `None`: the program can run forever from `s`;
- from `None` to `None`: once a run has run forever, it stays that way;
- from `None` to `Some s'`: never.

```coq
Definition ssemB (p : Prog) (o o' : option St) : Prop :=
  match o, o' with
  | None, None => True
  | None, Some _ => False
  | Some s, Some s' => smulti (p, s) (done, s')
  | Some s, None => sdiv (p, s)
  end.
```

**Why we check this against Imp's usual semantics.** `ImpS` is Imp *as
described by its step relation*. Everything the project proves will be
about `ImpS`. But Imp also has its usual, official semantics: the
big-step relation `ceval`, packaged as the language `Imp` in
`Imp/Lang.v`. That's the semantics people state theorems about. If `ImpS`
and `Imp` disagreed, our final theorems would be about the wrong
language. They don't disagree: `Imp/Equiv.v` already proves that big-step
and small-step Imp agree, and from that we get

```coq
Lemma ImpS_Imp : forall c s s', sem ImpS c s s' <-> sem Imp c s s'.
```

This lets every result we prove land on `Imp` itself. For your own
language, you only need such a lemma if you have a second, official
semantics. If the step relation *is* your definition, you can skip it.

## Step 4: the translation

Now we need, for each Imp program `c`, a core program that behaves
exactly like `c`. The core language knows nothing about Imp, but it can
perform actions we choose, and it can loop. So we make the core program
an *interpreter* for `c`.

The idea is this. The core program's state is a whole configuration:
the Imp program still to run, together with the Imp state. Its main
action, `SStep`, takes one Imp step, using `istep`. A loop repeats
`SStep` while the program still to run isn't `CSkip`. Before the loop
starts, the configuration must contain `c` as the program to run, so the
first action, `SLoad c`, puts `c` there and keeps the Imp state.

For example, here is how the translation of
`countdown := while x > 0 do x := x - 1 end` runs from a state with
`x = 1`. Each line is one configuration, and each arrow is one action:

```
(anything, x=1)
  --SLoad countdown-->   (countdown, x=1)
  --SStep-->             (if x > 0 then (x := x - 1; countdown) else skip, x=1)
  --SStep-->             (x := x - 1; countdown, x=1)
  --SStep-->             (skip; countdown, x=0)
  --SStep-->             (countdown, x=0)
  --SStep-->             (if x > 0 then ... else skip, x=0)
  --SStep-->             (skip, x=0)           finished, so the loop stops
```

In Rocq, the two actions' meaning, the "not finished yet" test, the loop,
and the translation `senc` are:

```coq
Definition sact_sem (a : sact Prog) (k k' : cfg) : Prop :=
  match a with
  | SLoad p => k' = (p, snd k)
  | SStep => step k k'
  end.

Definition running (k : cfg) : Prop := fst k <> done.
Definition sloop : kcom cfg (sact Prog) := kwhile running (KAct SStep).
Definition senc (p : Prog) : kcom cfg (sact Prog) :=
  KSeq (KAct (SLoad p)) sloop.
```

`cfg` is the type of configurations. For Imp, we call the translation
`ienc` (it is `senc CSkip`), and the actions' meaning `isem` (it is
`sact_sem istep`). The core language with these actions is
`KLang isem`.

The project proves that the translation behaves exactly like the
original, for every program. It has the same runs (`senc_run`): it can go
from a configuration with state `s` to a finished configuration with
state `s'` exactly when the original can go from `s` to `s'`. And it can
run forever from the same states (`senc_div`). Both are in
`Core/SmallStepCore.v`.

## Step 5: moving triples between a program and its translation

Triples about `countdown` and triples about its translation can't be
compared directly, because their assertions are about different things.
An assertion about Imp is a predicate on Imp states. An assertion about
the translation is a predicate on configurations. So each Imp assertion
has to be turned into an assertion on configurations.

For a precondition `P`, this is simple: look at the state part of the
configuration, `fun k => P (snd k)`. The program part doesn't matter,
because `SLoad` replaces it before anything else happens.

For a postcondition `Q`, looking only at the state part isn't enough.
Remember that an IL triple `{P} c {Q}` says *every* state in `Q` is the
end of some run. If `Q` became "the state part satisfies `Q`", it would
include configurations like `(x := 0, s)`, which are never where the
translated program stops. No run ends there, so the IL triple would be
false even when the Imp triple is true. The fix is to require the
program part to be finished: `Q` becomes "the program part is `CSkip`,
and the state part satisfies `Q`".

With these two conversions, the project proves the *transfer theorem*:
an Imp triple holds exactly when the converted triple holds for the
translation, in each of the sixteen logics. Combined with `ImpS_Imp`
from Step 3, the Imp side is ordinary big-step Imp:

```coq
Theorem ienc_cvalid : forall d p a (P Q : state -> Prop) c,
    cvalid d p a (@mkTriple Imp P c Q) <->
    cvalid d p a (@mkTriple (KLang isem) (fun k => P (snd k)) (ienc c)
                    (liftG snd ifin d p a Q)).
```

Reading the statement:
- `cvalid d p a t` says triple `t` is true in the logic chosen by
  `d p a`. For example, `cvalid Forward Plain Over` is Hoare logic and
  `cvalid Forward Plain Under` is incorrectness logic.
- `mkTriple L P c Q` is the triple `{P} c {Q}` for a program in language
  `L`.
- `fun k => P (snd k)` is the converted precondition.
- `liftG snd ifin d p a Q` is the converted postcondition. It computes
  "finished, and `Q`" for every logic except one, where "finished
  implies `Q`" is the right reading instead (see `Framework/Relational.v`
  if you need that logic).

`ienc_cvalid_bot` is the same theorem for the nontermination-aware
logics, with `ImpSB` on the Imp side.

So the plan for any proof is: prove the converted triple about the
translation, then apply the transfer theorem. Steps 6 to 8 show how to
prove the converted triple.

## Step 6: the logics you prove in

The project represents a logic as two things: a set of proof rules, and
a definition of which triples are true. A logic is only useful if its
rules match its definition of truth. So each logic comes packaged, as a
Rocq record of type `VLogic`, together with three proofs: that its notion
of truth is the right one for its place in the cube (for example, Hoare
validity for Hoare logic), that its rules are sound, and that they are
complete:

```coq
Record VLogic (L : Language) (d : direction) (p : polarity)
    (a : approximation) := mkVLogic {
  vl_logic : ProgramLogic L;
  vl_valid : forall t, valid vl_logic t <-> cvalid d p a t;
  vl_sound : locally_sound vl_logic;
  vl_complete : complete vl_logic
}.
```

You don't build any of these. `Examples/Common.v` provides all sixteen
for any choice of atomic actions, and we plug in `isem`:
- `HLv isem`, `ILv isem`, `NCv isem` and `SILv isem` for the four logics
  in the table at the top;
- `HLbv isem`, `ILbv isem`, `NCbv isem` and `SILbv isem` for their
  nontermination-aware versions;
- `PostDOv`, `PostDUv`, `PreDOv` and `PreDUv`, and the same with `bv`,
  for the remaining four.

How they are built is the point of the project, though you don't need it
to use them. Only one logic is built directly from the semantics: Hoare
logic for the core language, with one rule per construct. Each rule
describes exactly what its construct does to a set of states. For
example, the rule for an action says that from precondition `P`, action
`a` leads to exactly the states `a` can produce from states in `P`
(`sp_rel a P`):

```coq
  | F_Act : forall P a, fwd_rule GAct kpr0 (kt P (KAct a) (sp_rel a P))
```

Every other logic is computed from one built earlier, by a
*transformer*: a Rocq function that takes one `VLogic` record and returns
another, producing the new record's three proofs from the old one's. For
example, from `Examples/Common.v`:

```coq
Definition HLv : VLogic T Forward Plain Over := start_HL act_sem.
Definition PreDUv : VLogic T Backward Dual Under := vgalois_hl HLv.
Definition ILv : VLogic T Forward Plain Under := vto act_sem HLv _ _ _.
Definition HLbv : VLogic B Forward Plain Over := vto_bot act_sem HLv _ _ _.
```

There are three kinds of transformer:
- `vgalois_*` turns a logic into another that proves exactly the same
  triples. For example, Hoare logic and `PreDU` agree on every triple, so
  `PreDUv` is computed from `HLv`.
- `vcomplement_*` turns a logic into its partner, using the fact that
  `{P} c {Q}` holds in one exactly when `{not P} c {not Q}` holds in the
  other.
- `vto` and `vto_bot` move between logics whose rules can't be converted
  into each other directly, such as Hoare logic and incorrectness logic.
  Instead, they work out from the source logic what each action does, and
  build the target logic from that.

## Step 7: a Hoare logic proof

Let's prove that `countdown` always ends with `x = 0`. Following the plan
from Step 5, we prove the converted triple about the translation: from
any configuration, the translated program only stops at a configuration
that is finished and has `x = 0`.

The project writes "`{P} c {Q}` can be derived in logic `L`" as
`L ⊢ {{ P }} c {{ Q }}`, using a notation from `Core/TripleNotations.v`.
(The Rocq name behind the notation is `prov`.) So our goal is:

```coq
Definition countdown : com := <{ while "x" > 0 do "x" := "x" - 1 end }>.

Theorem countdown_HL :
  HLv isem ⊢ {{ fun k => True }} ienc countdown
             {{ fun k => fst k = CSkip /\ snd k "x" = 0 }}.
```

The proof rules are lemmas in `Core/Rules.v`. They are the usual Hoare
rules, stated for the core language and for any Hoare logic record `V`.
We need four:
- the rule for an action: before `a`, it suffices that every state `a`
  can produce satisfies `Q`;
- sequencing: chain `{P} c1 {R}` and `{R} c2 {Q}`;
- the while rule: if the body preserves an invariant `I` while the guard
  `B` holds, the loop ends in `I` with `B` false;
- consequence: strengthen the precondition and weaken the postcondition.

```coq
Lemma hl_act : forall Q a,
    prov V (fun s => forall s', act_sem a s s' -> Q s') (KAct a) Q.
Lemma hl_seq : forall P R Q c1 c2,
    prov V P c1 R -> prov V R c2 Q -> prov V P (KSeq c1 c2) Q.
Lemma hl_while : forall I (B : Σ -> Prop) c,
    prov V (fun s => I s /\ B s) c I ->
    prov V I (kwhile B c) (fun s => I s /\ ~ B s).
Lemma hl_cons : forall P P' Q Q' c,
    (forall s, P s -> P' s) -> prov V P' c Q' -> (forall s, Q' s -> Q s) ->
    prov V P c Q.
```

Every translated program has the same shape: load the program, then loop
taking steps. So every proof starts the same way:
1. `hl_seq` splits the load from the loop, and `hl_act` handles the load.
2. `hl_while` handles the loop. Its body is the single action `SStep`, so
   `hl_act` handles that too.

That leaves one real decision: the loop invariant. The loop's state is a
configuration, so the invariant is a property of configurations. It lists
where the program can be, and what holds of the Imp state there. Writing
`W` for the while loop, `A` for its body `x := x - 1`, and `g` for its
guard, `countdown` can only be:
- at the loop;
- at the loop's unfolding into an `if`;
- about to run the body, or just after it;
- finished, with `x = 0`.

These are exactly the configurations in the example run in Step 4. In
Rocq:

```coq
Definition I (k : com * state) : Prop :=
  fst k = W \/ fst k = CIf g (CSeq A W) CSkip \/ fst k = CSeq A W \/
  fst k = CSeq CSkip W \/ (fst k = CSkip /\ snd k "x" = 0).
```

The one lemma to prove is `I_step`: every step from a configuration
satisfying `I` lands in one satisfying `I`. It goes by case analysis on
the step (`inversion`). The interesting case is finishing: the only way
to reach `CSkip` is for the `if` to take its `else` branch, which happens
only when the guard is false, that is, when `x = 0`. When the loop stops,
the program part is `CSkip`, so the invariant gives `x = 0`.

Two tips:
- Give `hl_cons` its intermediate assertions explicitly, as in
  `apply (hl_cons _ _ _ P' _ Q')`. If you leave them for Rocq to guess,
  it usually guesses something unhelpful.
- For a language with several threads, the configuration records where
  every thread is, so the invariant describes all threads' positions at
  once. `Examples/ParExample.v` proves a two-thread program this way.

## Step 8: an incorrectness logic proof

Now let's prove that every state with `x = 0` is the end of some run of
`countdown` that started with `x = 1`. That's an incorrectness logic
triple, and it needs a different kind of loop argument. A Hoare invariant
says what is *preserved*. Incorrectness logic has to show that states are
*reached*. So instead of one invariant, its while rule takes a sequence
of assertions `X 0, X 1, X 2, ...`, one per iteration, where every state
in `X (n+1)` must be reachable by one iteration from some state in `X n`:

```coq
Lemma il_while : forall (X : nat -> Σ -> Prop) (B : Σ -> Prop) c,
    (forall n, prov V (fun s => X n s /\ B s) c (X (S n))) ->
    prov V (X 0) (kwhile B c) (fun s => exists n, X n s /\ ~ B s).
```

The natural choice of sequence is "the configurations after `n` steps".
Fix a target Imp state `s'` with `x = 0`. The run that reaches it is the
one from Step 4, started at `pre1 s'`, which is `s'` with `x` set to 1.
`d m s'` is the configuration after `m` steps of that run:

```coq
Definition d (m : nat) (s' : state) : com * state :=
  match m with
  | 0 => (W, pre1 s')
  | 1 => (CIf g (CSeq A W) CSkip, pre1 s')
  | 2 => (CSeq A W, pre1 s')
  | 3 => (CSeq CSkip W, post1 s')
  | 4 => (W, post1 s')
  | 5 => (CIf g (CSeq A W) CSkip, post1 s')
  | _ => (CSkip, post1 s')
  end.
```

`post1 s'` is the state after the assignment. Then `X m` is "the
configuration after `m` steps, for some target `s'`", capped at 6 steps.
Two lemmas finish the proof:
- `d_step`: each configuration steps to the next one. It's proved by
  `repeat constructor`.
- `post1_eq`: the run really ends at `s'`, that is, `post1 s' = s'`. Imp
  states are functions, so proving two states equal needs the axiom
  `functional_extensionality`.

The result is `countdown_IL`. Sufficient incorrectness logic (SIL) proofs
work the same way, with the sequence counting the steps still to go
instead of the steps taken.

## Step 9: the other logics

**The four logics outside the table.** You don't prove these directly.
Each of them proves exactly the same triples as one of the logics you
already have, possibly after negating the pre- and postcondition. Two
lemmas move a proof across: `vl_transport_same` (for the same triple) and
`vl_transport_compl` (for the negated triple). For example,
`countdown_PreDU` proves the `countdown_HL` triple in `PreDUv isem` with
one `apply vl_transport_same` followed by `exact countdown_HL`.

**The nontermination-aware versions.** These have their own rules, in
`Core/RulesBot.v`, with assertions over `option` configurations. Their
loop rules include an invariant rule, a decreasing-measure rule for HL⊥
(which proves termination), and rules for showing that a program can run
forever. `countdown` always terminates, so these logics don't say much
about it. `Examples/ParExample.v` proves all eight for a program that can
run forever.

## Step 10: back to Imp

The last step is the plan from Step 5. The record's soundness proof turns
a derivation into a true triple (`vl_valid_of`), and the transfer theorem
turns a true triple about the translation into a true triple about Imp:

```coq
Corollary countdown_correct :
  cvalid Forward Plain Over
    (@mkTriple Imp (fun _ => True) countdown (fun s => s "x" = 0)).
Proof.
  apply (ienc_cvalid Forward Plain Over), (vl_valid_of _ _ countdown_HL).
Qed.
```

This statement mentions only `Imp`, with its usual big-step semantics,
the program `countdown`, and Imp states. The core language and the
translation have disappeared.

## Things to know

- **Axioms.** The translation and the transfer theorems use no axioms,
  and neither does `countdown_correct`. Some logics use the axiom
  `classic` (excluded middle): those built by negating assertions, the
  nontermination-aware versions, and those built by `vto`. This matches
  how Cousot defines the cube. `countdown_reaches_zero`, the
  incorrectness result, uses `classic` for this reason, and
  `functional_extensionality` for the reason given in Step 8.
- **The rules are about steps, not about your syntax.** With the
  small-step translation, every program becomes one loop over
  configurations. That works for any language, but your invariants
  describe configurations, and no rule mentions Imp's own `while`. If you
  want rules that follow your constructs, translate construct by
  construct instead. For Imp that is `Core/ImpCore.v`, and
  `Examples/ImpProofs.v` uses an ordinary while rule.
- **Assertions are Rocq predicates.** Any side condition about states,
  such as the implications in `hl_cons`, is an ordinary Rocq goal.
  Completeness means every true triple has a derivation; it doesn't mean
  Rocq will find it for you.

In summary: give a step relation and prove two facts about the finished
program. The project then gives you sixteen logics with proof rules, all
proved sound and complete, and a transfer theorem that turns what you
prove in them into theorems about your own language.
