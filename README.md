# LogicTransformers

*Logic transformers* are functions from program logics to program logics.
For example, flipping the inclusion between the pre- and post-condition
state sets turns Hoare logic (over-approximation) into incorrectness logic
(under-approximation). The goal of this project is to make the edges of
Cousot's cube of program logics explicit as formally verified
transformations. Starting from any one vertex, you could then reach the
others, and each transformation would come with proofs that it preserves
soundness and/or completeness wherever that holds.

## Layout

| File | Contents |
|------|----------|
| `theories/Framework/Language.v` | `Language` record (programs, states, an input/output relation); `inv` |
| `theories/Framework/ProgramLogic.v` | Triples, rule sets as data (possibly infinite premise sets), `derivable`, `ProgramLogic`, `sound` / `complete` / `locally_sound` |
| `theories/Framework/Cube.v` | Cube validity `cvalid d p a` (direction × polarity × approximation) via `img`, `preimg`, `dimg` (p̃ost), `wlp` (p̃re); Galois collapses; exactness from two-sided validity |
| `theories/Framework/Relational.v` | Validity at every node as a property of a relation (`cvr`, `cvalid_cvr`), and its transfer along agreeing relations and projections (`cvr_transfer`, `cvr_proj`, `liftG`) |
| `theories/Framework/CubeLogic.v` | `CubeLogic`: a vertex + a named rule pool + a selection; generic per-vertex consequence; exactness ⇒ completeness |
| `theories/Framework/Transformer.v` | `Edge`s between validity notions, `run_edge`, preservation of soundness and completeness, composition; rule maps across languages |
| `theories/Framework/Aczel.v` | Aczel's correspondence: rules derive exactly the lfp of their consequence operator |
| `theories/Framework/Fixpoints.v` | Park induction for lfp, its order dual for gfp, and why the flipped version says nothing about the lfp |
| `theories/Framework/Verified.v` | `VLogic`: a logic packaged with its node, local soundness and completeness; transformers on these records (complement, Galois, inversion) |
| `theories/Transformers/Flip.v` | `restrict` (select rules) and `flip` (⊆ ⟷ ⊇) |
| `theories/Transformers/Complement.v` | Complement-duality `(d,p,a) ⟷ (d,p̃,ā)` on every node, as edges; `complement_cl` on cube logics |
| `theories/Transformers/Galois.v` | The Galois edges (identity maps between collapsed nodes) |
| `theories/Transformers/Augment.v` | `augment`: add a pool of rules (soundness if the new rules are sound; completeness always) |
| `theories/Transformers/Invert.v` | `inv_cl`: invert the semantics (forward ⟷ backward), moving to the inverse language |
| `theories/Imp/Syntax.v` | Imp syntax (arithmetic, booleans, commands, choice, havoc), states, expression evaluation; concrete syntax `<{ … }>` |
| `theories/Imp/BigStep.v` | Big-step semantics `ceval` (nondeterministic) |
| `theories/Imp/SmallStep.v` | Small-step semantics `cstep`, multi-step closure `cmulti` |
| `theories/Imp/Equiv.v` | `big_small_equiv : ceval c st st' <-> cmulti c st CSkip st'` |
| `theories/Imp/Lang.v` | Imp as a `Language` (big-step and small-step): the top face |
| `theories/Imp/Diverge.v` | Coinductive divergence `diverges` |
| `theories/Imp/LangBot.v` | `ImpBot`: states `option state` with `None = ⊥` absorbing: the bottom face |
| `theories/Logics/Hoare.v` | Standalone Hoare logic: `hoare_proof` vs `hoare_valid` / `hoare_valid_ss`, soundness and completeness |
| `theories/Logics/ImpRules.v` | The top-face rule pool, selections `classic`, `sym`, `bwd`, per-rule soundness, exactness of `sym` (sp) and `bwd` (wlp) |
| `theories/Logics/HoareLogic.v` | `HL`: the whole pool at the HL vertex |
| `theories/Logics/IL.v` | `IL := flip (restrict HL sym)` |
| `theories/Logics/NC.v` | `NC := run_edge hl_to_nc HL` |
| `theories/Logics/SIL.v` | SIL by two routes, and the proof that they agree |
| `theories/Logics/TopFace.v` | The four dual-polarity top-face nodes, by complement and Galois edges |
| `theories/Logics/Obstructions.v` | Loop semantics is an lfp; the order-flipped invariant rule is IL-unsound |
| `theories/Logics/BotRules.v` | Bottom-face forward pool (exact sp⊥, sound over and under) |
| `theories/Logics/BotWlpRules.v` | Bottom-face backward pool (exact wlp⊥, sound for HL⊥ and the wlp-dual) |
| `theories/Logics/BottomFace.v` | All eight bottom-face nodes; total/partial readings; `termination_not_recoverable` |
| `theories/Logics/Forget.v` | The vertical edge bottom → top (forget ⊥): sound at 6 of 8 nodes, unsound at SIL |
| `theories/Logics/CousotCube.v` | All 16 nodes sound and complete |
| `theories/Core/Kernel.v` | Structural core language (skip, atoms, assume, `;`, `⊕`, `*`), generic in states and atomic actions; `kwhile B c = (assume B; c)*; assume ¬B` and its run lemma |
| `theories/Core/ImpCore.v` | Imp encoded into the core; semantics and all cube validities preserved |
| `theories/Core/Generate.v` | Rule generator: forward (sp-exact) and backward (wlp-exact) rules per operator, from an atom relation |
| `theories/Core/CoreCube.v` | Generated HL, IL, SIL for any core language, sound and complete |
| `theories/Core/Regenerate.v` | IL ⟷ SIL transformers: read atoms off the source's derivations, generate, add, move |
| `theories/Core/ImpGenerated.v` | Imp's HL, IL, SIL obtained from the generator via the encoding |
| `theories/Core/KernelBot.v` | Divergence for the core language; `KLangB` (bottom face); loop lemmas: divergence needs the guard, divergence from a coinvariant, termination from a well-founded variant |
| `theories/Core/GenerateBot.v` | Bottom-face rule generator (exact sp⊥ and wlp⊥, pointwise star rules) |
| `theories/Core/CoreCousot.v` | All 16 nodes, generated, for any core language |
| `theories/Core/VCore.v` | For core languages: generated base records; reading the atoms' relation off any record; `vto` (and face-crossing variants) from any record to any node |
| `theories/Core/Rules.v` | Proof rules for any record at HL, IL, NC, SIL (per construct, consequence, `while`), admissible via the record's completeness |
| `theories/Core/RulesBot.v` | Proof rules for any record at HL⊥, IL⊥, NC⊥, SIL⊥: per construct, consequence, and loop rules (invariant, well-founded variant, iteration variant, coinvariant divergence, guard necessity) |
| `theories/Core/TripleNotations.v` | `V ⊢ {{ P }} c {{ Q }}` (HL), `V ⊢ ⟦ P ⟧ c ⟦ Q ⟧` (IL), and `⊢⊥` versions for the bottom face |
| `theories/Core/SmallStepCore.v` | Any small-step language is a core instance: `senc p = load p; while not done do step`, with runs and divergence preserved (`senc_run`, `senc_div`) and every cube validity transferred on both faces (`senc_cvalid`, `senc_cvalid_bot`) |
| `theories/Core/ImpCoreBot.v` | The Imp encoding preserves divergence (`enc_diverges`), hence all bottom-face validities (`enc_cvalid_bot`) |
| `theories/Core/ImpInstances.v` | Imp's top-face rules are derived rules of the generator |
| `theories/Core/ImpInstancesBot.v` | Imp's bottom-face rules are derived rules of the bottom-face generator |
| `theories/ParImp/ParImp.v` | Concurrent Imp: Imp with `p1 ∥ p2`, interleaving small-step semantics (unfair scheduler), `ParImp`/`ParImpB` and the encoding `penc` with its transfer theorems; `<{ }>` syntax in `pcom_scope` |
| `theories/Examples/Common.v` | The 16 logics for any core language as verified records: HL generated from the semantics, every other node obtained by applying transformers; `derive_*` pulls derivations out of the records; helpers for building a derivation by hand |
| `theories/Examples/ImpExample.v` | Imp example, *semantic side*: the program `count` in `<{ }>` syntax and its encoding; exact characterization of its runs (`count_run`) and divergence (`count_div`); each node's triple proved semantically valid (`v_*`) and derived by completeness (`imp_*`). A cross-check, with no Hoare-style reasoning |
| `theories/Examples/ImpProofs.v` | Imp example, *in the logics*: all 16 triples proved by applying rules (invariants, variants, coinvariants) in the transformed records; `count_*_from_rules` transfer the results back to the Imp program `count` itself, on both faces |
| `theories/Examples/StackExample.v` | Stack example, *semantic side*: a stack language with its own syntax and semantics, its encoding (`senc_correct`), the triangular-number program characterized (`triangle_run`, `triangle_no_div`), and each node's triple proved valid and derived by completeness |
| `theories/Examples/StackProofs.v` | Stack example, *in the logics*: all 16 triples proved with rules (total correctness by a well-founded variant) |
| `theories/Examples/ParExample.v` | Concurrent Imp example, *in the logics*: message passing (`mp`) proved with rules at all 16 nodes, using a global (Owicki-Gries style) invariant over both threads' positions; `mp_*` corollaries transfer the results to `mp` itself |
| `theories/Examples/RobotExample.v`, `RobotRules.v` | Supplementary: a toy grid-robot language defined directly in the core, with semantic and rule-based proofs at all 16 nodes, a hand-built HL derivation (`robot_HL_by_hand`), and explicit chains of transformers on records, including inversion (`robot_inverse_NC`) |

How the logics are built (each face):

```
                 restrict sym, flip
          HL  ───────────────────────▶  IL ──∼──▶ p̃ost ⊆
   (all pool rules)
       │  │
       │  └──∼──▶ p̃ost ⊇ ═Galois═ NC          HL ═Galois═ p̃re ⊇
       │ complement
       ▼                restrict bwd, flip
       NC ───────────────────────────────────▶ SIL ──∼──▶ p̃re ⊆
                                                ▲
   HL ──invert, complement──▶ HL(Imp⁻¹) ──restrict bwd, flip──▶ IL(Imp⁻¹) ──invert──┘
```

The two routes to SIL give the same logic (`SIL_routes_agree`). The
inversion route is built on the top face only.

Main results:

- `big_small_equiv`: big-step and small-step semantics agree.
- `hoare_sound_complete`, `hoare_sound_complete_ss`: the Hoare proof
  rules are sound and complete with respect to both semantics.
- `cousot_cube_top`, `cousot_cube_bottom`: all 16 nodes of the cube are
  sound and complete program logics for Imp.
- `galois_post_wlp`, `galois_pre_dimg`, `galois_pairs`: the Galois
  collapses, at validity level and as equal derivable sets.
- `complement_duality`: complement maps node `(d,p,a)` to `(d,p̃,ā)`.
- `HL_iff_hoare_proof`: HL derives exactly what `hoare_proof` derives.
- `exact_complete`, `flip_complete`: if the kept rules derive exact
  triples, the logic and its flip are both complete.
- `flip_classic_unsound`, `naive_flipped_invariant_unsound`,
  `flipped_invariant_trivial`, `flipped_park_not_lfp`, `sp_while_lfp`:
  why the order flip fails naively.
- `run_edge_locally_sound`, `run_edge_complete`, `run_compose_edge`:
  edges preserve local soundness and completeness, and compose.
- `SIL_routes_agree`, `flip_inv_cl`: commuting faces.
- `HLB_total_iff`, `HLB_partial_iff`: HL⊥ is total correctness, with
  partial correctness as the fragment whose posts allow ⊥.
- `termination_not_recoverable`: the top face does not determine the
  bottom face.
- `aczel_rules_lfp`, `aczel_op_lfp`: Aczel's correspondence.
- `fwd_theory`, `bwd_exact`, `GHL_complete`, `GIL_complete`,
  `GSIL_complete`: generated rules for the core language, for any
  atoms. The generator itself is axiom-free.
- `il_to_sil_correct`, `sil_to_il_correct`, `il_sil_il`: verified
  transformers across the IL ⟷ SIL gap, from any sound and complete
  source logic.
- `imp_HL_generated`, `imp_IL_generated`, `imp_SIL_generated`: Imp's
  logics from the generator alone.
- `vl_derive`, `vl_valid_of`, `vl_theory`: pull derivations and soundness
  out of a verified record. `vcomplement`, `vgalois_*`, `vinvert`: generic
  transformers on records. `vto`, `vto_bot`, `vfrom_bot`, `vbot_to`: from a
  record at any node to a record at any node, on either face, for any
  core language.
- `core_cousot_cube_top`, `core_cousot_cube_bottom`: for any states and
  atomic actions, all 16 nodes of the cube are sound and complete with
  generated rules only.
- `sym_instance`, `bwd_instance`, `sym_derivations`, `bwd_derivations`,
  `brule_instance`, `wrule_instance`: every hand-written Imp rule (both
  faces) is a derived rule of the generated system on encoded programs.
- `inv_cl_complete`, `inv_cl_locally_sound`: inversion preserves soundness
  and completeness for every cube logic (no axioms).
- `forget_cl_base_sound`, `forget_cl_complete`: forgetting ⊥ preserves
  soundness at reflecting nodes and completeness at forward nodes.
  `HL_from_bot` and `IL_from_bot` are the top-face HL and IL obtained this
  way. `forget_SIL_unsound`: at SIL it is unsound.

Assertions are shallowly embedded (`state -> Prop`), so completeness is
relative completeness in the sense of Cook. Axioms:

- `Classical_Prop.classic`, used by complement edges and by the
  bottom-face loop rules (see finding 9).
- `functional_extensionality`, used only by the counterexample
  `naive_flipped_invariant_unsound`.
- Everything else is axiom-free. That includes all inversion and Galois
  edges, the top-face HL and IL (soundness and completeness), and the
  soundness of IL⊥. IL⊥'s completeness inherits `classic` from
  bottom-face exactness.

## Examples

`theories/Examples/` instantiates the generated cube for three languages,
each with one looping program and a triple at all 16 nodes. The three
languages reach the core in three ways:

| | Imp | Stack | Concurrent Imp |
|---|---|---|---|
| How it reaches the core | existing syntax, `enc` + `enc_correct`, `enc_diverges` | own syntax and semantics, `senc` + `senc_correct` | small-step semantics, generic encoding `penc` (`Core/SmallStepCore.v`) |
| Program | `while 0<x do ((x:=x-1; y:=y+1) ⊕ skip)` | `loop (acc; dec)` | `(while f=0 do skip; y:=x) ∥ (x:=42; f:=1)` |
| Behaviour | moves `x` into `y`; may idle forever | `n::a::r ↦ 0::(a+1+…+n)::r`; always terminates | message passing; the reader may spin forever if the writer is starved |

Triples by node (top face; the bottom face is analogous, with ⊥):

| Node | Imp | Stack | Concurrent Imp |
|---|---|---|---|
| HL `post ⊆` | `{x+y=10} {x=0 ∧ y=10}` | `{[n;0]} {[0;tri n]}` | `{f=0} {y=42}` |
| IL `post ⊇` | `[x=3 ∧ y=7] [x=0 ∧ y=10]` | `[[n;0]] [[0;tri n]]` | `[f=0] [f=1 ∧ x=42 ∧ y=42]` |
| NC `pre ⊆` | reaching `x=0 ∧ y=10` needs `x+y=10` | reaching `[0;6]` needs `[n;a]`, `a+tri n=6` | ending with `y≠42` needs `f≠0` |
| SIL `pre ⊇` | from `x+y=10`, `y=10` is reachable | from `[3;0]`, `[0;6]` is reachable | from any state, `y=42` is reachable |
| `p̃ost ⊆` | all starts had `x+y=10` ⇒ `x≠0 ∨ y=10` | all starts two-element ⇒ `[0;a]` or nonzero top | all starts had `f=0` ⇒ not `f=1 ∧ x=42 ∧ y=42` |
| `p̃ost ⊇` | = NC (Galois) | = NC (Galois) | = NC (Galois) |
| `p̃re ⊆` | runs surely give `y=10` ⇒ `x+y=10` | runs surely give `[0;6]` ⇒ suitable `[n;a]` or stuck | no start forces `y≠42` |
| `p̃re ⊇` | = HL (Galois) | = HL (Galois) | = HL (Galois) |

On the bottom face, the nodes are about nontermination:
- Imp: divergence is reachable, and possible exactly from `0<x`.
- Stack: total correctness holds, and only ⊥ leads to ⊥.
- Concurrent Imp: divergence (starvation of the writer) is reachable,
  and possible exactly from `f=0`; from `f≠0` the program always
  terminates (total HL⊥, by a decreasing weight on residual programs).

A fourth, supplementary example (`RobotExample.v`, `RobotRules.v`) uses a
toy robot language written directly in the core. It is kept mainly
because it chains transformers on records explicitly (IL → SIL, IL → HL⊥,
and inversion), which the main examples do not.

**Concurrency.** An interleaving semantics is a step relation, so
`Core/SmallStepCore.v` encodes it as one loop over configurations
`(program, state)`: load the program, then step while not done. The
encoding is exact on both faces, and every validity transfers back to
the concurrent program (`penc_cvalid`, `penc_cvalid_bot`). The price is
modularity: the loop is the scheduler, so a loop invariant is a global
invariant over both threads' positions (Owicki-Gries style, without
interference freedom checks), not a thread-modular rule such as
rely/guarantee. Proofs are about whole closed programs.

**Records and transformers.** Logics are verified records
(`VLogic L d p a`: a logic, a proof that its validity is node
`(d, p, a)`, its local soundness, its completeness). `Examples/Common.v`
generates one record from the semantics (HL) and obtains every other node
by applying transformers to records:
- `vgalois_hl`, `vcomplement_*` and `vgalois_dimg_nc` for the HL class;
- `vto` to regenerate IL from the HL record and SIL from the IL record;
- `vto_bot` and `vbot_to` for the bottom face.

The semantic-side examples pull each derivation from a record's
completeness field (`vl_derive`). The rule-based ones pull soundness back
out (`vl_valid_of`) to transfer results to the source program.

**Notations.**
- Imp programs can be written as
  `<{ while "x" > 0 do ("x" := "x" - 1; "y" := "y" + 1) ⊕ skip end }>`
  (`com_scope`).
- Concurrent Imp uses the same brackets with `pcom_scope` open, plus
  `p1 ∥ p2`, which binds looser than `;`. A file should open only one of
  the two scopes, since `;`, `:=`, `if` and `while` are shared.
- Triples in a record are written `V ⊢ {{ P }} c {{ Q }}` (HL),
  `V ⊢ ⟦ P ⟧ c ⟦ Q ⟧` (IL), and `V ⊢⊥ …` on the bottom face
  (`triple_scope`).
- They are used in the example statements, and proof goals print with
  them.

**Writing proofs with rules.** `Core/Rules.v` gives rules for *any*
record at the HL, IL, NC and SIL nodes. There are rules for each
construct, consequence in the node's direction, and a `while` rule per
node:
- HL: the invariant rule;
- NC: a backward-invariant rule;
- IL: O'Hearn's iteration-indexed variant;
- SIL: a descending variant.

At the dual nodes you prove the complemented triple (or the Galois
partner's triple) and transport it (`vl_transport_compl`,
`vl_transport_same`). `Core/RulesBot.v` does the same for the bottom
face, whose loop rules are:
- HL⊥: an invariant rule (partial, divergence allowed) and a
  well-founded variant rule (total);
- IL⊥: an iteration variant, plus a coinvariant rule for reachable
  divergence;
- NC⊥: a backward invariant, plus guard necessity for divergence;
- SIL⊥: a descending variant, plus a coinvariant rule for possible
  divergence.

`ImpProofs.v`, `StackProofs.v` and `ParExample.v` prove all 16 triples
of each example this way. Each proof composes rules in the records the
transformers produced; the only remaining side conditions are facts about
states, in the consequence steps. Termination-flavoured NC⊥ facts are
proved as HL⊥ total correctness of the complemented triple and
transported. The rules are admissible: each is proved sound once, and the
record's completeness makes it derivable. The semantic proofs in
`ImpExample.v` and `StackExample.v` remain as a cross-check; the
concurrent example has only the rule-based side.

**How the semantic cross-check proofs work.** There are no syntactic
rules yet. The generated rules are semantic:
- an atom's rule mentions its relation;
- the star rule has one premise per iteration count (and, on the bottom
  face, per state);
- assertions are arbitrary Rocq predicates.

So a derivation by hand amounts to supplying the family of iterate
assertions for every loop, which *is* the loop's semantics. Each example
therefore characterizes its program once:
- the exact input/output relation (`count_run`, `triangle_run`);
- when it can diverge (`count_div`, `triangle_no_div`).

From these it proves each node's triple semantically valid, and obtains a
derivation in that node's generated logic from the logic's completeness
theorem. The derivations are genuine objects of the logics: completeness
builds them from the exact generated rules plus one consequence step.

`Common.v`'s `hand_gen` and `hand_cons` build HL derivations directly from
the generated rules: the star rule with a constant family (an invariant),
exact rules for the body, and consequence. This is what a textbook
invariant rule packages up.

**Axioms in the examples.**
- `functional_extensionality`, Imp and concurrent Imp only: their states
  are functions, so exhibiting a run that ends in a *given* state needs it.
- `classic`, at the nodes that go through complement, on the bottom face,
  and through `vto`. Reading the atoms' relation off an HL record needs
  double negation; reading it off IL or SIL records does not.
- Axiom-free: the stack characterization and encoding proof, the
  generic small-step encoding and its transfer theorems, the Imp
  encoding's divergence preservation, and the top-face HL and `p̃re ⊇`
  derivations.

## Relation to Cousot's cube

The target is the standard "Cousot cube": Fig. 3 of Cousot, *Calculational
Design of [In]Correctness Transformational Program Logics by Abstract
Interpretation* (POPL 2024). Cousot calls it a "hierarchical taxonomy of
transformational assertional logics", and Li, Zilberstein and Silva (*Total
Outcome Logic*, 2024) call it the Cousot cube.

- **Corners**: four transformers, on two faces.
  - The transformers are `post` (image), `pre` (preimage), and their complement
    duals `p̃ost = ¬∘post∘¬` and `p̃re = ¬∘pre∘¬` (`p̃re` is wlp).
  - Top face: partial correctness. Bottom face: postconditions may also
    mention nontermination `⊥`.
- **Two logics per corner**: one for `⊆` and one for `⊇`. That gives 16
  logics. Four pairs coincide by Galois connections, so 12 theories remain:
  - `post P ⊆ Q ⟺ P ⊆ p̃re Q`: Hoare logic is the same theory as subgoal
    induction;
  - `pre Q ⊆ P ⟺ Q ⊆ p̃ost P`;
  - each on both faces.
- **Edges**: inversion `⁻¹` (post ⟷ pre), complement-duality `∼`
  (post ⟷ p̃ost, pre ⟷ p̃re), the termination abstraction (top ⟷ bottom),
  and the order flip `⊆ ⟷ ⊇`.

In this development a vertex is `(direction, polarity, approximation)`, with
the termination face given by the language. `Forward/Backward` is
post/pre, `Plain/Dual` is τ/τ̃, and `Over/Under` is `τ(·) ⊆ ·` vs
`· ⊆ τ(·)`.

### Why edges can or cannot be taken naively

Cousot derives each logic's proof system from its theory: abstraction
followed by Aczel's correspondence between fixpoints and rules. This
project instead transforms one proof system into another, so it meets
obstructions that his method sidesteps. Findings so far:

1. **Order flip (⊆ ⟷ ⊇) works for statements, not for loops.**
   - Cousot, in *On the Design of Program Logics* (2024): "The incorrectness
     logic theory (7) is the ⊆-order dual of the Hoare logic theory (6). So
     the rules for statements, but for iteration, are the same because all
     correspond to the strongest postcondition logic theory (4) together
     with consequence".
   - He rejects exact rules plus a flipped consequence rule because "we can
     approximate the pre and postconditions by the consequence rules but not
     the loop invariant itself. Requiring the invariant to be the strongest
     would be too demanding."
   - The precise reason is that Park's fixpoint induction (the invariant
     rule, POPL Thm. II.3.1) is an lfp over-approximation principle. Its
     order dual is a **greatest**-fixpoint under-approximation principle
     ("By order-duality, this is sound and complete greatest fixpoint under
     approximation"). But loop semantics is a least fixpoint.
   - Under-approximating an lfp needs (transfinite) iterates (Thm. II.3.6).
     That is Cousot's IL loop rule, which is our `IR_WhileIdx`.
   - In this repo:
     - `flip_classic_unsound`: flipping the textbook rules is unsound, and
       backward assignment is the culprit.
     - `naive_flipped_invariant_unsound`: the order-flipped invariant rule
       is unsound for IL.
     - `naive_premises_gfp`: its premises only make the invariant a
       coinvariant, i.e. they bound the gfp.
     - `sp_while_lfp`: loop semantics is an lfp.
     - `flipped_park_not_lfp`: the abstract reason.
     - `flipped_invariant_trivial`: flipping the bare invariant rule is
       sound only because its conclusion always holds (zero iterations).
     - `flip_complete`: flipping a rule set that is exact for strongest
       postconditions preserves soundness and completeness.
   - Not in Cousot: transformers act on rule *presentations*. Two
     presentations of the same complete logic can flip to different logics.
     One is sound and complete; the other is unsound.

2. **Complement-duality is classical.**
   - Cousot states complement as a Galois *isomorphism*, from
     `X ⊆ Y ⇔ ¬X ⊇ ¬Y` and `¬¬X = X` in the Boolean lattice ℘(Σ).
   - With `Prop`-valued assertions this needs excluded middle. Every
     complement edge here uses `Classical_Prop.classic`; inversion and
     Galois edges do not.

3. **Inversion is an isomorphism, but onto the inverse semantics.**
   - "Backward logics originates from the inversion abstraction (using the
     inverse program semantics (⟦S⟧)⁻¹) or the dual complement abstraction"
     (POPL §I.3.9).
   - Inversion therefore changes the language: `IL(Imp)` inverts to
     `SIL(Imp⁻¹)`, not `SIL(Imp)`. The commuting face `SIL_routes_agree`
     goes through `HL(Imp⁻¹)`. Inversion needs no axioms.

4. **Backward (wlp) logics cannot use invariants for loops.**
   - Fixpoint abstraction needs the abstraction to preserve joins, "which is
     not always the case (for the dual problem α = p̃re in remark I.3.12 is a
     counter-example)" (POPL §II.3.3).
   - `p̃re` preserves meets, not joins, so the wlp loop rule `IR_WhileWlp`
     is a meet of iterates.

5. **Selection matters: no single rule set flips on both faces.**
   - The forward flip needs rules exact for strongest postconditions
     (`sym`). The backward flip needs complements of rules exact for wlp
     (`bwd`). Their union is not IL-sound.
   - So over-approximate logics, which tolerate every rule, act as hubs.

6. **Termination (the top ⟷ bottom edges).** Cousot warns of three things:
   - Counter-based termination in Hoare logic "is incomplete for unbounded
     nondeterminism" (§I.3.14.1).
   - "nontermination {P}S{false} is provable by the logic but its negation
     ¬({P}S{false}) is not in the logic" (§II.3.5).
   - Variant functions into ω are "sound but incomplete" (Thm. II.3.8,
     Ex. II.3.9). Completeness needs well-founded sets (Thm. II.3.11).
   - Imp has `havoc`, i.e. unbounded nondeterminism. Our bottom-face loop
     rules avoid variants altogether (see finding 9).

7. **Negation is outside the cube.** Hoare incorrectness `¬{P}S{Q}` is not
   reachable from IL: "incorrectness logic is not Hoare incorrectness
   logic. It is sufficient but not necessary" (Cousot 2024). His
   counterexample: `¬({true} x=0 {x≠0 ∧ x≠1})` holds, but
   `[true] x=0 [x=0 ∨ x=1]` does not.

8. **Infinite premises are legitimate.** Finite proofs "require the premiss
   P to be finite but transfinite proofs are also possible" (Cousot 2024).
   Our inductive `derivable` over premise sets is his model-theoretic (lfp)
   semantics of deductive systems.

9. **On the bottom face, loop rules must be pointwise.** This is our
   finding, not Cousot's.
   - With ⊥ in the post, a loop's exact post must say whether some run
     diverges: either a reachable body divergence or an infinite chain of
     iterations.
   - Under unbounded nondeterminism, the set-level iterates `postⁿ(P)` do
     not determine whether an infinite chain exists. Every depth can be
     reachable while every run terminates.
   - So the exact rules take one premise per state:
     - forward: `{s ∧ b} c {F s}` (`BR_While`);
     - backward: `(W s', c, ≠ s')` and `(Wd, c, ≠ ⊥)`, reading the step
       relation off complements (`WR_While`).
   - Chains are then followed inductively (termination) and coinductively
     (divergence).
   - Splitting a divergence into "body diverges" or "infinite chain" is
     classical, so HL⊥ soundness of these rules uses `classic`.
   - This sidesteps the variant-function incompleteness Cousot describes,
     at the price of state-indexed premises.

10. **The vertical (termination) edges are abstractions, not
    isomorphisms.**
    - `skip` and `skip ⊕ (while true skip)` have the same theory at every
      top-face node but different HL⊥ theories
      (`termination_not_recoverable`).
    - So no transformer that sees only top-face validity can produce a
      bottom-face logic: the top face is Cousot's termination abstraction
      of the bottom one.
    - Downward the abstraction is still a fragment: `HLB_partial_iff`
      shows partial correctness is HL⊥ on posts that allow ⊥.

11. **Forgetting ⊥ (bottom → top) is sound at six nodes, not at SIL.**
    - Restricting triples to proper states preserves validity everywhere
      except at SIL and its complement p̃re ⊆ (`forget_reflects`,
      `forget_not_reflecting_SIL`).
    - Those nodes assert that *some outcome* exists, and on the bottom face
      that outcome can be divergence.
    - The transformer `forget_cl` therefore preserves soundness at the
      other nodes, and completeness at forward nodes. But forgetting
      SIL⊥'s proof system gives an unsound logic (`forget_SIL_unsound`).
    - It keeps only rule instances whose premises are "⊥-determined"; for
      a sound source this loses no derivation.

12. **Rules can be generated from the semantics (Cousot's method,
    mechanized).**
    - For a structural core language, each operator's exact theory
      equation, read as Aczel rules, gives the generated rules. For example
      `sp(c*) P = ⋃ₙ spⁿ(P)` becomes an ω-premise rule.
    - Soundness at both nodes implies exactness (`fexact_iff`,
      `pexact_iff`), so completeness is by construction.
    - On the top face nothing needs to be chosen per node: since the
      operators preserve all unions or all intersections, ω-iterates
      suffice for loops. The invariant rules of textbook logics are not
      needed for completeness.

13. **Crossing IL ⟷ SIL needs new rules, and what crosses is the theory.**
    - `il_to_sil` and `sil_to_il` read the atoms' relation off the source's
      *derivations* (`{s} a {s'}` derivable), generate the missing rules,
      add them, and move with flip/complement.
    - They are verified for every sound and complete source.
    - They necessarily discard the source's own rules: complemented IL
      rules are not SIL-sound, and vice versa. So the only information
      that crosses this gap is the source's *theory* (its derivable
      singleton triples), never its proof system.
    - This complements finding 10: on the top face a single node's theory
      determines all the others; across the termination edge it does
      not.

14. **Hand-written rules are the generated ones, up to encoding.**
    - Imp's rules are derived rules of the generated system on encoded
      programs (`if` as a choice of `assume; c`, `while` as
      `(assume b; c)*; assume ¬b`).
    - On the bottom face, the generated star rule follows every body step,
      while Imp's loop rule follows only steps from states that satisfy
      the guard. For states where the guard fails, the generator's own
      exactness supplies an empty body post, and the two chain relations
      coincide.
    - For wlp loops, `¬(b → W)` and `b ∧ ¬W` agree only because Imp's
      tests are decidable. With semantic (undecidable) tests, the
      correspondence would need classical logic.

15. **Top → bottom is possible by regeneration, despite finding 10.**
    - `termination_not_recoverable` is about the theory of *individual
      programs*: no map from a program's top-face theory to its bottom-face
      theory exists.
    - For a structural language, the transformer `vto_bot` instead reads
      the theory of the *atoms* off the source record and regenerates using
      the language's known structure, which determines every program's
      divergence.
    - So the vertical edge exists as a transformer of logic records, but
      not as a map on theories.

## Building

```bash
# Install Dependencies
opam switch create rocq 4.14.1
opam pin add rocq-runtime 9.1.0
opam install rocq-prover dune

# Clone and build
git clone https://github.com/CharlesAverill/LogicTransformers && cd LogicTransformers
dune build
```
