#!/usr/bin/env python3
"""Regenerate CLAIMS.md: each headline claim, its theorem, and its axioms.

Run from the repository root after `dune build`:

    python3 scripts/claims.py

The script asks Rocq for `Print Assumptions` of every theorem below, so the
axiom column is always the one the build actually checks. It fails if a
theorem is missing.
"""

import os
import re
import subprocess
import sys
import tempfile

# (section, claim, module, theorem)
CLAIMS = [
    ("Definitions", "Each corner's validity is Cousot's theory, defined by abstraction",
     "Framework.Abstraction", "theory_iff_cvr"),
    ("Definitions", "post is a Galois connection between relations and transformers",
     "Framework.Abstraction", "galois_post"),
    ("Definitions", "Hoare rules derived by calculation: Park's invariant rule",
     "Core.Calculational", "calc_star_park"),
    ("Definitions", "Hoare rules derived by calculation: exact iteration rule",
     "Core.Calculational", "calc_star_exact"),
    ("Definitions", "Verscht and Kaminski's sixteen logics are corners of the cube",
     "Framework.Taxonomy", "taxonomy_in_cube"),
    ("Logics", "Generated logics are sound and complete at all corners, ordinary face",
     "Core.CoreCousot", "core_cousot_cube_top"),
    ("Logics", "Generated logics are sound and complete at all corners, bottom face",
     "Core.CoreCousot", "core_cousot_cube_bottom"),
    ("Logics", "Textbook Hoare logic, primitive and complete",
     "Core.Textbook", "vHL_text"),
    ("Logics", "Textbook incorrectness logic, primitive and complete",
     "Core.Textbook", "vIL_text"),
    ("Logics", "Textbook necessary-condition logic, primitive and complete",
     "Core.Textbook", "vNC_text"),
    ("Logics", "Textbook sufficient incorrectness logic, primitive and complete",
     "Core.Textbook", "vSIL_text"),
    ("Logics", "Textbook HL with nontermination: well-founded variants, complete",
     "Core.TextbookBot", "vHLB_text"),
    ("Logics", "Textbook IL with nontermination: recurrent-set divergence rule, complete",
     "Core.TextbookILBot", "vILB_text"),
    ("Logics", "Textbook SIL with nontermination: divergence rule, complete",
     "Core.TextbookSILBot", "vSILB_text"),
    ("Logics", "All sixteen corners from textbook rules: NC with nontermination, by transformers",
     "Core.TextbookCube", "tNCb"),
    ("Logics", "O'Hearn's two-outcome triples are IL triples in any record",
     "Core.Errors", "oh_iff"),
    ("Equivalence", "Each generated logic proves what the textbook logic at its corner proves, all 16 corners",
     "Equivalence.Core", "gen_text_cube"),
    ("Equivalence", "Textbook Hoare logic for Imp proves what the generated Hoare logic proves",
     "Equivalence.ImpHL", "hoare_iff_generated"),
    ("Equivalence", "O'Hearn's incorrectness logic for Imp is sound and complete",
     "Equivalence.ImpIL", "ohil_complete"),
    ("Equivalence", "... and proves what the generated incorrectness logic proves",
     "Equivalence.ImpIL", "ohil_iff_generated"),
    ("Equivalence", "Vanegue's adversarial-logic rules are complete",
     "Equivalence.Vanegue", "van_complete"),
    ("Equivalence", "... and prove what the generated adversarial logic proves",
     "Equivalence.Vanegue", "van_iff_generated"),
    ("Equivalence", "Sufficient incorrectness logic for Imp proves what the generated logic proves",
     "Equivalence.ImpSIL", "sil_iff_generated"),
    ("Equivalence", "Total-correctness Hoare logic for Imp (well-founded variants) likewise",
     "Equivalence.ImpTotal", "tc_iff_generated"),
    ("Equivalence", "O'Hearn's ok/error rules are complete",
     "Equivalence.Errors", "ohl_complete"),
    ("Equivalence", "... and prove what the generated incorrectness logic proves",
     "Equivalence.Errors", "ohl_iff_generated"),
    ("Equivalence", "ILAL's interleaved adversarial rules prove what the generated logic proves",
     "Equivalence.ILAL", "ilal_iff_generated"),
    ("Equivalence", "Cook: syntactic Hoare logic is complete relative to expressiveness of loops",
     "Equivalence.Cook", "hs_complete"),
    ("Equivalence", "... and, with first-order formulas, complete outright for loop-free programs",
     "Equivalence.Cook", "fo_complete_loop_free"),
    ("Equivalence", "Gödel's beta-function codes every finite sequence (via the stdlib CRT)",
     "Equivalence.Beta", "beta_exists"),
    ("Equivalence", "Every weakest liberal precondition of Imp is a first-order arithmetic formula",
     "Equivalence.Godel", "wlp_expressible"),
    ("Equivalence", "... so Hoare logic over first-order arithmetic is complete for Imp, outright",
     "Equivalence.Godel", "fa_complete"),
    ("Transformers", "Records at the same corner prove the same triples (the cube commutes)",
     "Framework.Verified", "vl_same_theorems"),
    ("Transformers", "The complement edge, on verified logics (classical)",
     "Framework.Verified", "vcomplement"),
    ("Transformers", "The inversion edge (constructive)",
     "Framework.Verified", "vinvert"),
    ("Transformers", "A Galois edge (constructive)",
     "Framework.Verified", "vgalois_hl"),
    ("Transformers", "Inverting twice gives back the same theorems",
     "Framework.Verified", "vinvert_involutive"),
    ("Transformers", "Flipping works exactly when every kept rule is sound at both approximations",
     "Transformers.Flip", "flip_works_iff"),
    ("Transformers", "The two routes to SIL agree",
     "ImpCube.SIL", "SIL_routes_agree"),
    ("Obstructions", "Uniform correspondences exist exactly within the three groups",
     "Framework.Uniform", "ucorr_iff_group"),
    ("Obstructions", "No monotone uniform transformer crosses between the groups",
     "Framework.Uniform", "no_monotone_crossing"),
    ("Obstructions", "Flipping the textbook Hoare rules is unsound",
     "ImpCube.IL", "flip_classic_unsound"),
    ("Obstructions", "No single rule selection flips on both faces",
     "ImpCube.IL", "flip_union_unsound"),
    ("Obstructions", "Natural-number variants are incomplete under unbounded nondeterminism",
     "Equivalence.Variants", "wloop_not_tcn"),
    ("Obstructions", "... though the loop terminates, by a well-founded variant",
     "Equivalence.Variants", "wloop_total"),
    ("Obstructions", "Hoare incorrectness is not incorrectness logic (Cousot's example)",
     "ImpCube.Negation", "negation_not_il"),
    ("Obstructions", "Two-player games are not a function of the program's relation",
     "Adversarial.Game", "game_not_relational"),
    ("Obstructions", "... so no corner of the cube expresses game validity",
     "Adversarial.Game", "game_not_a_corner"),
    ("Obstructions", "Outcome logic, unlike games, is Hoare logic over sets of outcomes",
     "Framework.Outcome", "ol_is_hoare"),
    ("Obstructions", "Flipping depends on presentation: same theorems, different flips",
     "ImpCube.FlipPresentation", "flip_theorems_differ"),
    ("Obstructions", "The order-flipped invariant rule is unsound",
     "ImpCube.Obstructions", "naive_flipped_invariant_unsound"),
    ("Obstructions", "Flipped Park induction does not characterize the least fixpoint",
     "Framework.Fixpoints", "flipped_park_not_lfp"),
    ("Obstructions", "Ordinary theorems do not determine nontermination-aware ones",
     "ImpCube.BottomFace", "termination_not_recoverable"),
    ("Obstructions", "Forgetting bottom from SIL is unsound",
     "ImpCube.Forget", "forget_SIL_unsound"),
    ("Languages", "Imp's translation preserves terminating runs",
     "Core.ImpCore", "enc_correct"),
    ("Languages", "Imp's translation preserves divergence",
     "Core.ImpCoreBot", "enc_diverges"),
    ("Languages", "Imp's big-step divergence is infinite small-step reduction",
     "Imp.DivergeEquiv", "diverges_iff_sdiverges"),
    ("Languages", "Any small-step language: validity transfers at all corners (ordinary)",
     "Core.SmallStepCore", "senc_cvalid"),
    ("Languages", "Any small-step language: validity transfers at all corners (bottom)",
     "Core.SmallStepCore", "senc_cvalid_bot"),
    ("Languages", "The error language's translation is O'Hearn's semantics",
     "Core.Errors", "enc_osem"),
    ("Languages", "Concurrent Imp: validity transfers at all corners (bottom)",
     "ParImp.ParImp", "penc_cvalid_bot"),
    ("Languages", "Stack language: validity transfers at all corners (bottom)",
     "Examples.StackBot", "senc_cvalid_bot"),
    ("Proofs", "One rule per logic for small-step languages: Hoare logic",
     "Core.SmallStepRules", "hl_senc"),
    ("Proofs", "Rules at the dual corners, in any record: complement of O'Hearn's variant",
     "Core.DualRules", "fdo_star"),
    ("Proofs", "... and the complement of the descending variant",
     "Core.DualRules", "bdo_star"),
    ("Proofs", "Segment rules for any step relation: transfer along an inclusion (IL)",
     "Core.StepCore", "sprov_embed"),
    ("Proofs", "Segment rules for any step relation: configuration invariants (HL)",
     "Core.StepCore", "hsprov_inv"),
    ("Proofs", "One rule per logic for small-step languages: incorrectness logic",
     "Core.SmallStepRules", "il_senc"),
    ("Concurrency", "Rely/guarantee for concurrent Imp is sound",
     "ParImp.RelyGuarantee", "rg_sound"),
    ("Concurrency", "A closed rely/guarantee proof gives the cube's Hoare validity",
     "ParImp.RelyGuarantee", "rg_closed_hl"),
    ("Concurrency", "Message passing proved thread by thread",
     "Examples.MPRelyGuarantee", "mp_correct_rg"),
    ("Concurrency", "... and derived in the cube's Hoare-logic record",
     "Examples.MPRelyGuarantee", "mp_HL_from_rg"),
    ("Concurrency", "Rely/guarantee without auxiliary variables is incomplete",
     "ParImp.RGIncomplete", "rg_incomplete"),
    ("Concurrency", "Rely/guarantee validity is a cube validity (Hoare logic of a step relation)",
     "ParImp.RGGenerated", "rg_valid_iff"),
    ("Concurrency", "The generated rely/guarantee logic is sound and complete",
     "ParImp.RGGenerated", "rgprov_iff"),
    ("Concurrency", "Jones's rules hold in it: every rely/guarantee derivation embeds",
     "ParImp.RGGenerated", "rg_embed"),
    ("Concurrency", "... proved there by a configuration invariant, a rule for any step relation",
     "ParImp.RGGenerated", "inc2_by_invariant"),
    ("Concurrency", "... and it is strictly stronger than Jones's rules without ghosts",
     "ParImp.RGGenerated", "rg_generated_stronger"),
    ("Concurrency", "Auxiliary-variable rule: a ghost proof gives a Hoare triple for the erased program",
     "ParImp.RGGhost", "aux_rule"),
    ("Concurrency", "... and with two ghosts, Jones's rules prove x := x+1 || x := x+1",
     "ParImp.RGGhost", "inc2_by_ghosts"),
    ("Concurrency", "Raad et al.'s parallel rule, with separation as disjoint variables, holds",
     "ParImp.DisjointPar", "il_disjoint_par"),
    ("Concurrency", "Jones's while rule is incomplete under interference, even with ghosts",
     "ParImp.RGWhile", "rg_while_incomplete"),
    ("Concurrency", "With a repaired while rule, rely/guarantee is complete for sequential code",
     "ParImp.RGComplete", "rgc_complete_seq"),
    ("Concurrency", "Concurrent incorrectness logic is sound",
     "ParImp.ConcurrentIL", "cil_sound"),
    ("Concurrency", "Concurrent incorrectness logic is complete",
     "ParImp.ConcurrentIL", "cil_complete"),
    ("Concurrency", "The lost update found compositionally (phases)",
     "Examples.RaceCIL", "race_cil"),
    ("Concurrency", "Adversarial logic is the generated IL record over its atoms",
     "Adversarial.AL", "al_valid_iff"),
    ("Concurrency", "Victim against adversary: the generated logic is sound and complete",
     "Adversarial.Interleaving", "ail_iff"),
    ("Concurrency", "The interleaving rules (step, transfer, transitivity) hold in the generated logic",
     "Adversarial.Interleaving", "ail_trans"),
    ("Examples", "Vanegue's example 1: the adversary wins the trivial case",
     "Examples.Vanegue", "example1_attack"),
    ("Examples", "Vanegue's example 2: a round of the oscillating bit protocol",
     "Examples.Vanegue", "obt_round_success"),
    ("Examples", "Vanegue's example 3: two services quote the same price for a large order",
     "Examples.Vanegue", "eqtest_attack"),
    ("Examples", "Message passing is correct from f = 0",
     "Examples.ParExample", "mp_correct"),
    ("Examples", "The message-passing reader can be starved",
     "Examples.ParExample", "mp_starvation"),
    ("Examples", "A lost update refutes the intended Hoare triple",
     "Examples.RaceExample", "race_not_correct"),
    ("Examples", "An error raised inside a loop is reachable",
     "Examples.ErrorExample", "count3_bug_reachable"),
    ("Examples", "Tutorial: countdown is correct, for big-step Imp",
     "Tutorial.ImpTutorial", "countdown_correct"),
]

SHORT = {
    "Classical_Prop.classic": "classic",
    "FunctionalExtensionality.functional_extensionality_dep": "funext",
}


def main():
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    build = os.path.join(root, "_build", "default", "theories")
    mods = sorted({m for _, _, m, _ in CLAIMS})
    lines = ["From LogicTransformers Require " + m + "." for m in mods]
    for _, _, m, t in CLAIMS:
        name = "LogicTransformers." + m + "." + t
        lines.append('Goal True. idtac "@@' + name + '". exact I. Qed.')
        lines.append("Print Assumptions " + name + ".")
    with tempfile.TemporaryDirectory() as tmp:
        path = os.path.join(tmp, "Claims.v")
        with open(path, "w") as f:
            f.write("\n".join(lines) + "\n")
        res = subprocess.run(["rocq", "c", "-Q", build, "LogicTransformers", path],
                             capture_output=True, text=True)
    out = res.stdout + res.stderr
    if res.returncode != 0:
        sys.stderr.write(out)
        sys.exit("rocq failed: a claimed theorem is probably missing")
    axioms = {}
    for chunk in out.split("@@")[1:]:
        name, _, body = chunk.partition("\n")
        found = set()
        if "Closed under the global context" not in body:
            for ax in re.findall(r"^\s*([A-Za-z_][\w.]*) :", body, re.M):
                found.add(SHORT.get(ax, ax))
        axioms[name.strip()] = sorted(found)
    rows = ["# Claims and the theorems that prove them", "",
            "Generated by `python3 scripts/claims.py` from the compiled development.",
            "The axiom column is Rocq's `Print Assumptions`. `classic` is excluded",
            "middle; `funext` is functional extensionality.", ""]
    section = None
    for sec, claim, m, t in CLAIMS:
        if sec != section:
            rows += ["", "## " + sec, "", "| Claim | Theorem | File | Axioms |",
                     "|---|---|---|---|"]
            section = sec
        ax = axioms.get("LogicTransformers." + m + "." + t, ["?"])
        f = "theories/" + m.replace(".", "/") + ".v"
        rows.append("| %s | `%s` | `%s` | %s |" %
                    (claim, t, f, ", ".join(ax) if ax else "none"))
    with open(os.path.join(root, "CLAIMS.md"), "w") as f:
        f.write("\n".join(rows) + "\n")
    print("wrote CLAIMS.md (%d claims)" % len(CLAIMS))


if __name__ == "__main__":
    main()
