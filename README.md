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
| `theories/Framework/Abstraction.v` | Cousot's definitions by abstraction: relations to transformers (`post`, `pre`, their complement duals; `post` as a Galois connection, `galois_post`), transformers to theories; every corner's theory is this project's validity (`theory_iff_cvr`, `cvalid_iff_theory`); commutation equations for composition, union and iteration |
| `theories/Framework/Taxonomy.v` | Verscht and Kaminski's eight transformers and sixteen logics, each proved equal to one corner: 8 on the ordinary face, 4 with divergence as ⊥, and 4 (their new unreachability logics) on the inverse program with unreachability as ⊥ (`taxonomy_in_cube`) |
| `theories/Framework/Uniform.v` | Which edges exist: the three groups of corners are exactly the classes related by uniform correspondences (`ucorr_iff_group`); no monotone uniform transformer crosses between the Hoare-logic group and the others (`no_monotone_crossing`) |
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
| `theories/Imp/DivergeEquiv.v` | Imp's big-step divergence is exactly an infinite small-step reduction (`diverges_iff_sdiverges`); Imp's bottom-face semantics restated with small steps alone (`semB_small`) |
| `theories/Imp/LangBot.v` | `ImpBot`: states `option state` with `None = ⊥` absorbing: the bottom face |
| `theories/Logics/Hoare.v` | Standalone Hoare logic: `hoare_proof` vs `hoare_valid` / `hoare_valid_ss`, soundness and completeness |
| `theories/Logics/ImpRules.v` | The top-face rule pool, selections `classic`, `sym`, `bwd`, per-rule soundness, exactness of `sym` (sp) and `bwd` (wlp) |
| `theories/Logics/HoareLogic.v` | `HL`: the whole pool at the HL vertex |
| `theories/Logics/IL.v` | `IL := flip (restrict HL sym)` |
| `theories/Logics/NC.v` | `NC := run_edge hl_to_nc HL` |
| `theories/Logics/SIL.v` | SIL by two routes, and the proof that they agree |
| `theories/Logics/TopFace.v` | The four dual-polarity top-face nodes, by complement and Galois edges |
| `theories/Logics/FlipPresentation.v` | Two Hoare logics with the same theorems (textbook and exact rules) whose flips differ: one sound and complete IL, one unsound (`flip_depends_on_presentation`, `flip_theorems_differ`) |
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
| `theories/Core/Calculational.v` | The calculational equations for each core construct (`post_seq`, `post_star`, `pre_choice`, ...), the equations the generated rules are read from |
| `theories/Core/Errors.v` | Error outcomes: a language with `error` and O'Hearn's two-outcome semantics (`okr`, `err`), its translation into the core (`enc_osem`), O'Hearn's triples `[P] c [ok: Q] [er: E]` as IL triples in any record (`oh_iff`), and his rules as lemmas (error, short-circuit sequencing, iteration, unrolling) |
| `theories/Core/Textbook.v` | Textbook proof systems as *primitive* rules (finitary invariant rules for HL and NC; O'Hearn's iteration-indexed rule for IL; a descending variant for SIL), each proved sound and complete on its own, axiom-free (`vHL_text`, `vIL_text`, `vNC_text`, `vSIL_text`) |
| `theories/Core/TextbookBot.v` | Textbook HL⊥ as primitive rules: an invariant rule allowing divergence, and a variant rule into any well-founded order (required only on the invariant); sound, and complete under unbounded nondeterminism (`vHLB_text`) |
| `theories/Core/TextbookILBot.v` | Textbook IL⊥ as primitive rules, including a divergence rule (the recurrent-set principle); sound, and complete (`vILB_text`) |
| `theories/Core/TextbookSILBot.v` | Textbook SIL⊥ as primitive rules, with a descending variant and a divergence rule; sound, and complete (`vSILB_text`) |
| `theories/Core/TextbookCube.v` | All sixteen corners from textbook rules alone: seven textbook systems, the other nine by the complement and Galois transformers |
| `theories/Core/SmallStepRules.v` | One rule per logic for small-step languages: `hl_senc`, `il_senc`, `nc_senc`, `sil_senc` reduce a proof to its invariant or variant obligations (load, step, exit) |
| `theories/Core/Rules.v` | Proof rules for any record at HL, IL, NC, SIL (per construct, consequence, `while`), admissible via the record's completeness |
| `theories/Core/RulesBot.v` | Proof rules for any record at HL⊥, IL⊥, NC⊥, SIL⊥: per construct, consequence, and loop rules (invariant, well-founded variant, iteration variant, coinvariant divergence, guard necessity) |
| `theories/Core/TripleNotations.v` | `V ⊢ {{ P }} c {{ Q }}` (HL), `V ⊢ ⟦ P ⟧ c ⟦ Q ⟧` (IL), and `⊢⊥` versions for the bottom face |
| `theories/Core/SmallStepCore.v` | Any small-step language is a core instance: `senc p = load p; while not done do step`, with runs and divergence preserved (`senc_run`, `senc_div`) and every cube validity transferred on both faces (`senc_cvalid`, `senc_cvalid_bot`) |
| `theories/Core/StepCore.v` | Any step relation is a core instance, with no requirement that finished programs are stuck: a *segment* `(p, q)` runs from residual `p` to residual `q`, encoded as `load p; step*; assume (residual = q)` (`segenc_run`), with every ordinary-face validity transferred (`segenc_cvalid`). Rules for segments in any IL record, for every step relation: composition (`sprov_trans`), one step (`sprov_step`), and transfer of a triple from another language along an inclusion of relations (`sprov_embed`, the monotonicity of IL) |
| `theories/Core/ImpCoreBot.v` | The Imp encoding preserves divergence (`enc_diverges`), hence all bottom-face validities (`enc_cvalid_bot`) |
| `theories/Core/ImpInstances.v` | Imp's top-face rules are derived rules of the generator |
| `theories/Core/ImpInstancesBot.v` | Imp's bottom-face rules are derived rules of the bottom-face generator |
| `theories/ParImp/ParImp.v` | Concurrent Imp: Imp with `p1 ∥ p2`, interleaving small-step semantics (unfair scheduler), `ParImp`/`ParImpB` and the encoding `penc` with its transfer theorems; `<{ }>` syntax in `pcom_scope` |
| `theories/Tutorial/ImpTutorial.v` | Companion to `tutorial/README.md`: Imp instantiated through its small-step semantics and `SmallStepCore`, with rule-based proofs and transfer back to big-step Imp |
| `theories/Examples/ErrorExample.v` | Reachable bugs proved with O'Hearn's rules: a guessed value, and an error raised inside a loop on its third iteration (`count3_error`) |
| `theories/Examples/RaceExample.v` | A lost update between two threads, found with incorrectness logic (`race_IL`, short form `race_IL_short`), refuting the intended Hoare triple (`race_not_correct`) |
| `theories/ParImp/RelyGuarantee.v` | Thread-modular reasoning for concurrent Imp: a rely/guarantee logic (`rg`), sound against the interleaving semantics (`rg_sound`); a closed proof gives the cube's Hoare validity (`rg_closed_hl`) and a derivation in any HL record (`rg_derive_HL`) |
| `theories/ParImp/RGIncomplete.v` | Rely/guarantee without auxiliary variables is incomplete: `x := x+1 ∥ x := x+1` from `x = 0` provably ends with `x = 2`, but no derivation proves it (`rg_incomplete`) |
| `theories/ParImp/RGGenerated.v` | A complete rely/guarantee logic, generated: rely/guarantee validity is the Hoare validity of a step relation in which environment steps follow the rely and a guarantee-breaking step goes to an error state (`rg_valid_iff`); the generated logic `RGv` is sound and complete for it (`rgprov_iff`), Jones's rules hold in it (`rgprov_par`, `rg_embed`), and it proves `x := x+1 ∥ x := x+1`, which Jones's rules alone cannot (`rg_generated_stronger`) |
| `theories/ParImp/ConcurrentIL.v` | Incorrectness logic for concurrent Imp, composing schedules (run one thread then the other; split into phases) plus a one-step rule and infinitary disjunction; sound and complete (`cil_sound`, `cil_complete`, `cil_iff`), entering the cube at IL (`cil_derive_IL`) |
| `theories/Examples/RaceCIL.v` | The lost update proved compositionally: one phase for the reads, one for the writes (`race_cil`) |
| `theories/Adversarial/AL.v` | Vanegue's adversarial logic, single thread: victim/adversary states with stores and channels, atoms run in a mode (assign, rand, read, write, `adv_assert`), commands with `local`. Only the language is defined: the logic is the generated IL record `ALv` (`al_valid_iff`), with the other corners alongside (`ALsil`, `ALhl`), and Vanegue's rules are lemmas (`al_assign`, `al_read`, `al_write`, `al_adv_success`, `al_local`, ...) |
| `theories/Adversarial/Interleaving.v` | Victim against adversary: small steps of either side and channel transfers, entered into the core as segments (`Core/StepCore.v`). The logic is the generated IL record `AILv`, sound and complete (`ail_iff`); its rules are the generic segment rules of `Core/StepCore.v`, and the language supplies only facts about its steps (`thread_l`, `prefix_r`, `com_va`, ...); ILAL's interleaving rules also hold (`ail_refl`, `ail_trans`, `ail_step_l`, `ail_com`, ...); `attack` states that an adversary can reach an outcome |
| `theories/Examples/Vanegue.v` | Vanegue's three examples, derived rule by rule in the generated logics: the trivial case (`example1_attack`), a round of the oscillating bit protocol (`obt_round_success`), equivalence testing (`eqtest_attack`) |
| `theories/Equivalence/Core.v` | For the core language with any atoms, the generated logic at each of the 16 corners proves exactly what the textbook logic at that corner proves (`gen_text_cube`) |
| `theories/Equivalence/ImpHL.v` | Textbook Hoare logic for Imp (`hoare_proof`) proves exactly what the generated Hoare logic proves of the encoded program (`hoare_iff_generated`) |
| `theories/Equivalence/ImpIL.v` | O'Hearn's incorrectness logic for Imp (`ohil`): sound and complete (`ohil_sound`, `ohil_complete`), and equivalent to the generated incorrectness logic (`ohil_iff_generated`) |
| `theories/Equivalence/Vanegue.v` | Vanegue's single-thread adversarial-logic rules (`van`), as ILAL states them: sound and complete (`van_sound`, `van_complete`), and equivalent to the generated logic (`van_iff_generated`) |
| `theories/Examples/MPRelyGuarantee.v` | Message passing proved thread by thread with rely/guarantee (`reader_rg`, `writer_rg`, `mp_rg`), then entered into the cube (`mp_correct_rg`, `mp_HL_from_rg`) |
| `theories/Examples/Common.v` | The 16 logics for any core language as verified records: HL generated from the semantics, every other node obtained by applying transformers; `derive_*` pulls derivations out of the records; helpers for building a derivation by hand |
| `theories/Examples/ImpExample.v` | Imp example, *semantic side*: the program `count` in `<{ }>` syntax and its encoding; exact characterization of its runs (`count_run`) and divergence (`count_div`); each node's triple proved semantically valid (`v_*`) and derived by completeness (`imp_*`). A cross-check, with no Hoare-style reasoning |
| `theories/Examples/ImpProofs.v` | Imp example, *in the logics*: all 16 triples proved by applying rules (invariants, variants, coinvariants) in the transformed records; `count_*_from_rules` transfer the results back to the Imp program `count` itself, on both faces |
| `theories/Examples/StackExample.v` | Stack example, *semantic side*: a stack language with its own syntax and semantics, its encoding (`senc_correct`), the triangular-number program characterized (`triangle_run`, `triangle_no_div`), and each node's triple proved valid and derived by completeness |
| `theories/Examples/StackBot.v` | The stack language on both faces: its own divergence, preserved by the encoding (`senc_diverges`), and validity transfer at all sixteen corners (`senc_cvalid`, `senc_cvalid_bot`) |
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

## Claims

`CLAIMS.md` lists every headline claim with the theorem that proves it,
its file, and its axioms as Rocq reports them. Regenerate it after
`dune build` with `python3 scripts/claims.py`, which fails if a listed
theorem is missing.

## Tutorial

`tutorial/README.md` walks through instantiating the framework for a new
language, using Imp's small-step semantics and the companion file
`theories/Tutorial/ImpTutorial.v`.

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

**Proof effort.** Lines of theorem statements and proofs for all
sixteen corners, per example, against the hand-written Imp logics of
`Logics/` (rule pool, soundness and completeness at four corners, for one
language):

| | Corners | Lines | Per corner |
|---|---|---|---|
| Imp (`ImpProofs.v`) | 16 | 271 | 17 |
| Stack (`StackProofs.v`) | 16 | 308 | 19 |
| Message passing (`ParExample.v`) | 16 | 414 | 26 |
| Robot (`RobotRules.v`) | 15 | 274 | 18 |
| Hand-written Imp logics (`Logics/`) | 4 | ~870 | n/a |

Instantiating a new language through `SmallStepCore` takes about 30
lines (`Tutorial/ImpTutorial.v`, steps 1 to 3).

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

16. **Which edges exist, precisely (`Framework/Uniform.v`).**
    - *Variance.* Enlarging a program's relation can only falsify triples
      at HL, NC, p̃ost ⊇ and p̃re ⊇ (`cvr_anti`), and can only validate
      triples at IL, p̃ost ⊆, SIL and p̃re ⊆ (`cvr_mono`).
    - *Correspondences.* A uniform correspondence maps each triple's pre
      and post without looking at the program, so that validity at two
      corners agrees for every relation; Galois connections and
      complement duality are examples. Two corners correspond exactly
      when they are in the same group (`ucorr_iff_group`): {HL, p̃re ⊇,
      p̃ost ⊇, NC}, {IL, p̃ost ⊆}, {SIL, p̃re ⊆}. Variance separates the
      first group from the others. Direction separates the last two
      (`no_ucorr_IL_SIL`, `no_ucorr_SIL_IL`).
    - *Transformers.* A uniform transformer is a function on rule sets
      that never sees the semantics. No monotone one turns every sound
      and complete logic at a corner of one variance into a sound and
      complete logic at a corner of the other (`no_monotone_crossing`,
      axiom-free). Every transformer that maps rules one at a time is
      monotone (`rulewise_monotone`). The source logics in the proof are
      the most naive ones: every valid triple as an axiom.
    - Both conditions matter: a transformer that sees the semantics can
      always cross by returning the target's valid triples as axioms.
      `vto` crosses from HL by reading derivations negatively (an action
      can take `s` to `s'` when `{s} a {≠ s'}` is *not* derivable), which
      is not monotone. The theorem shows some such dependence is
      unavoidable. It turns findings 1 and 13 from counterexamples into
      a classification.

17. **Completeness doesn't need exact or invariant-free rules
    (`Core/Textbook.v`).**
    - The generated logics are complete because their rules are exact.
      The textbook systems are complete too, with the familiar rules as
      primitives and an arbitrary consequence rule: Hoare logic with the
      finitary invariant rule, NC with a backward invariant rule, IL with
      O'Hearn's iteration-indexed rule, SIL with a descending variant.
    - The proofs are Cook's argument: derive the triple with the exact
      transformer (wlp, sp or preimage), by induction on the program, and
      weaken. For HL the loop invariant is the wlp of the whole loop; for
      NC, the preimage of the whole loop.
    - IL and SIL keep one premise per iteration count, as in the
      literature: an under-approximate loop rule needs to say how many
      iterations reach each state.
    - These records can start the transformer pipeline
      (`IL_from_textbook`).
    - On the nontermination-aware face, textbook HL⊥ is complete too
      (`Core/TextbookBot.v`): an invariant rule that allows divergence,
      and a variant rule into *any* well-founded order, required only on
      the invariant. Cousot notes that variants into the naturals are
      incomplete under unbounded nondeterminism; a general well-founded
      order is enough. The completeness proof takes "one more iteration"
      as the variant, which is well-founded on states that cannot
      diverge (classically, a state that is not yields an infinite run).
    - IL⊥ and SIL⊥ are complete with textbook rules too
      (`Core/TextbookILBot.v`, `Core/TextbookSILBot.v`). Each adds a
      *divergence rule*: if every state of a set `J` has a body step back
      into `J`, the loop can run forever from `J`. This is the
      recurrent-set principle for proving nontermination (Gupta et al.),
      as a proof rule. Completeness splits on how a loop diverges: the
      body diverging at a reachable iterate is covered by the loop's
      iteration rule, and iterating forever by the divergence rule.
    - With these, all sixteen corners have records built from textbook
      rules alone (`Core/TextbookCube.v`): seven textbook systems, and
      the other nine computed by the complement and Galois transformers.
      No corner needs the generated exact rules.

18. **When flipping works, exactly (`Transformers/Flip.v`,
    `Logics/FlipPresentation.v`).**
    - For an exact rule set, flipping gives sound and complete logics at
      both approximations if and only if every kept rule is sound at both
      (`flip_works_iff`). Such rules map exact triples to exact triples
      (`bisound_exact_preserving`).
    - Whether that holds depends on how the rules are written, not on
      what they prove. Imp's textbook Hoare rules and its exact forward
      rules are both sound and complete, so they prove the same triples
      (`HLc_HLs_same_theorems`). Flipping the exact rules gives a sound
      and complete IL; flipping the textbook rules gives an unsound one
      (`flip_depends_on_presentation`). So the two flips prove different
      triples (`flip_theorems_differ`): a flip is not a function of a
      logic's theorems. This makes finding 5 a theorem.

19. **The definitions are Cousot's (`Framework/Abstraction.v`,
    `Core/Calculational.v`).**
    - Cousot defines each theory in two abstractions: the semantics to a
      transformer (`post`, `pre`, or their duals `¬∘post∘¬`, `¬∘pre∘¬`),
      then the transformer to the pairs `⟨P, Q⟩` it relates by `⊆` or
      `⊇`. These are stated as he gives them, `post` is shown to be a
      Galois connection that loses nothing (`galois_post`,
      `gpost_apost`), and each corner's theory is proved equal to this
      project's validity (`theory_iff_cvr`, `cvalid_iff_theory`). The
      correspondence is no longer by inspection.
    - The commutation equations his calculational design reads rules
      from are proved for every core construct: `post (c1; c2) =
      post c2 ∘ post c1`, `post (c1 ⊕ c2) = post c1 ∨ post c2`,
      `post c* = ∃n. (post c)ⁿ`, and the same for `pre` (axiom-free).
    - From those equations and monotonicity alone, Hoare logic's rules
      are derived by calculation, without looking at runs: sequencing,
      choice, Park's invariant rule, and the exact iteration rule
      (`calc_seq`, `calc_choice`, `calc_star_park`, `calc_star_exact`).

20. **The cube commutes, at the level of theorems (`Framework/Verified.v`).**
    - Any two records at the same corner, for the same language, prove
      the same triples (`vl_same_theorems`). So every diagram of
      transformers commutes: a record's theorems don't depend on the
      path that computed it. Inverting twice gives back the original
      theorems, over the twice-inverted language (`vinvert_involutive`).
    - Proof systems don't commute: finding 18 gives two with the same
      theorems and different rules. `SIL_routes_agree` is a case where
      two routes give the same rules too.

21. **Error outcomes: O'Hearn's incorrectness logic is in the cube
    (`Core/Errors.v`).**
    - A language with `error`, over any atomic actions, has O'Hearn's
      semantics: one relation for normal outcomes and one for errors,
      with errors short-circuiting sequencing and escaping loops.
    - Translated into the core with states tagged `Ok` or `Err` (errors
      pass through everything that follows), its runs are exactly that
      semantics (`enc_osem`, axiom-free).
    - So no new logic is needed: in any record at the IL corner,
      O'Hearn's triple `[P] c [ok: Q] [er: E]` is the IL triple with
      precondition `Ok P` and postcondition `Ok Q ∨ Err E` (`oh_iff`).
      His rules are lemmas there (`oh_error`, `oh_seq`, `oh_star`,
      `oh_unroll`, ...). The same encoding gives every other corner with
      errors; for example SIL with an `Err` postcondition is sufficient
      incorrectness about errors.
    - `Examples/ErrorExample.v` proves two bugs reachable this way,
      including one raised inside a loop.

22. **A lost update, found with incorrectness logic
    (`Examples/RaceExample.v`).**
    - Two threads each increment `x` through a local copy. IL proves that
      every final state with `x = 1` (one update lost) is reachable from
      `x = 0`, and this refutes the intended Hoare triple
      `{x = 0} race {x = 2}` (`race_not_correct`).
    - `Core/SmallStepRules.v` reduces such proofs to their idea: the same
      proof is a dozen lines with `il_senc` (`race_IL_short`).

26. **The generated logics are as powerful as the textbook ones
    (`Equivalence/`).**
    - For the core language, at every one of the sixteen corners, the
      generated logic and the textbook logic prove exactly the same
      triples (`gen_text_cube`).
    - For concrete languages, the published rule sets prove exactly what
      the generated logics prove of the encoded programs:
      - textbook Hoare logic for Imp (`hoare_iff_generated`, axiom-free);
      - O'Hearn's incorrectness logic for Imp (`ohil_iff_generated`);
      - Vanegue's adversarial logic (`van_iff_generated`).
    - Each published system is proved sound and complete for its
      validity, and the generated logic is too, so they have the same
      theorems. The completeness proofs for O'Hearn's and Vanegue's
      rules are mechanized here by Cook's argument with strongest
      postconditions (O'Hearn's paper proves his complete on paper, and
      ILAL mechanizes Vanegue's).
    - Rely/guarantee validity is a cube validity too
      (`ParImp/RGGenerated.v`): Hoare validity of a step relation where
      environment steps follow the rely and a step that breaks the
      guarantee goes to an error state. The generated logic for it is
      sound and complete (`rgprov_iff`), Jones's rules hold in it
      (`rg_embed`), and it proves `x := x+1 ∥ x := x+1`. Jones's rules
      alone, without auxiliary variables, prove strictly fewer triples
      (`rg_incomplete`, `rg_generated_stronger`): which triples a fixed
      rule set proves is a fact about that rule set, so no transformer
      makes them complete. Their classical completeness needs ghosts.

25. **Adversarial logic is incorrectness logic for a two-party
    concurrent language (`Adversarial/`).**
    - Vanegue's adversarial logic reasons about a victim and an
      adversary that share no memory and talk through channels. Its
      triples are under-approximate: every state in the post is reached
      from the pre.
    - Only the language is defined here: paired states, atoms run in a
      victim or adversary mode, small steps, and channel transfers.
      The logic is generated, by the same transformers as every other
      language: single-thread adversarial logic is the IL record of its
      atoms (`al_valid_iff`), and the interleaved logic is the IL record
      of the interleaving, entered as segments of a step relation
      (`Core/StepCore.v`, `ail_iff`). Soundness and completeness are
      fields of the records, and the other fifteen corners come with
      them, for example SIL for adversarial programs (`ALsil`).
    - Vanegue's three examples are derivations in the generated logics
      (`Examples/Vanegue.v`), using only rules that hold for every
      language. Each thread's part uses the rules of `Core/Rules.v`
      (`il_seq`, `il_choice_l`, `il_act_pt`, `il_assume_pt`); the attack
      uses the segment rules of `Core/StepCore.v`, which hold for every
      step relation (`sprov_trans`, `sprov_step`, and `sprov_embed` to
      bring in a thread). The language contributes only facts about its
      semantics, as side conditions: what each atom does, that a
      thread's run is a run of the interleaving, and what a transfer
      does. No rule was written for adversarial logic.
    - Vanegue's own rule statements, and ILAL's interleaving rules, also
      hold in the generated logics.
    - It is IL rather than a new axis of the cube because its validity
      resolves every choice existentially, the victim's as well as the
      adversary's. A validity where the victim's choices are universal
      and the adversary's existential would be a game, not a relation,
      and is not a corner of the cube for any language.
    - The generated records use `classic`, and the state updates
      `functional_extensionality`.

24. **Thread-modular reasoning enters the cube at the Hoare-logic corner
    (`ParImp/RelyGuarantee.v`).**
    - A rely/guarantee logic for concurrent Imp: `rg R G P c Q` says that
      if every step of the other threads satisfies `R`, then every step
      of `c` satisfies `G`, and `c` only finishes in `Q`. It is proved
      sound against the same interleaving semantics the cube uses
      (`rg_sound`), with environment steps interleaved. The parallel rule
      verifies each thread separately.
    - A closed program proved this way has a valid Hoare triple for the
      concurrent language (`rg_closed_hl`), so a derivation in any HL
      record (`rg_derive_HL`); every other corner is then computed by
      the transformers. Rely/guarantee is a sound way into the cube, not
      a replacement for it: it is incomplete without auxiliary variables.
    - `Examples/MPRelyGuarantee.v` re-proves message passing thread by
      thread, with a loop invariant about the reader alone
      (`f ≠ 0 → x = 42`), where `ParExample.v` needed a global invariant
      over both threads' positions.
    - Rely/guarantee as it stands cannot be complete, and this is a
      theorem (`ParImp/RGIncomplete.v`): `x := x+1 ∥ x := x+1` from
      `x = 0` always ends with `x = 2`, but no derivation proves it,
      for any rely and guarantee. The parallel rule's post is the
      conjunction of the threads' posts, and each thread alone ends with
      `x = 1`. Classical completeness results add auxiliary (ghost)
      variables to record what the other thread has done.
    - Under-approximation composes differently
      (`ParImp/ConcurrentIL.v`). Two threads' claims that *some* run
      exists cannot be merged in general, so concurrent incorrectness
      logic composes *schedules*: run one thread then the other, or
      split both into phases. The lost update is two phases, both reads
      then both writes (`Examples/RaceCIL.v`). With a one-step rule and
      infinitary disjunction the logic is also complete (`cil_complete`):
      it proves exactly the valid IL triples of concurrent Imp
      (`cil_iff`), and its proofs enter the cube at IL.

23. **Verscht and Kaminski's taxonomy is the cube, extended by inversion
    (`Framework/Taxonomy.v`).**
    - Their sixteen logics come from eight predicate transformers
      (angelic or demonic, liberal or not, wp or sp), each over- or
      under-approximated. With divergence made explicit as a predicate,
      each of their logics is proved equal to exactly one corner
      (`taxonomy_in_cube`).
    - 8 are corners of the ordinary face (Hoare, incorrectness, Lisbon or
      SIL, necessary preconditions, partial incorrectness, and their
      contrapositives). 4 are corners of the nontermination-aware face
      (total correctness, angelic partial correctness, and their
      contrapositives).
    - Their remaining 4, built from the transformers they introduce for
      unreachable final states and note are absent from Cousot's cube,
      are corners of the nontermination-aware face of the *inverse*
      program, with ⊥ read as "unreachable". They conjecture the cube
      could be extended with a new symbol for unreachability, dual to ⊥.
      No new symbol is needed: inversion and the existing ⊥ suffice.
    - Two of the sixteen use `classic`; the rest are constructive.

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

Tested with Rocq 9.1.0 and dune 3.21. `scripts/check.sh` runs the whole
artifact check: the build, no `Admitted` or `admit`, no line over 80
characters, and a regenerated `CLAIMS.md` that matches the committed one
(so every claimed theorem exists and its axioms are as stated).
