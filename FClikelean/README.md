# Prospective Formal Conjectures target

This directory contains an unofficial, AI-assisted statement mock-up for
Erdős Problem #811. It is not an official Formal Conjectures file and has not
been reviewed, approved, submitted, or merged by that project.

## Theorem coverage of the supplied problem page

[`Erdos811.lean`](Erdos811.lean) records the following nine theorem
statements. Having a definition alone does not count as theorem coverage.
All names below are inside the `Erdos811` namespace.

The Lean file imports the shared canonical definitions from
[`../lean/Erdos811NaturalDefinitions.lean`](../lean/Erdos811NaturalDefinitions.lean).
That file contains the colouring structure, the five familiar definitions
(colour degree, balance, rainbow copy, edge count and threshold), and the
additional `UsesEveryColor` predicate. The definitions are no longer copied
independently into the catalogue and proof source.
Quantifiers and colour counts appear directly in the theorem statements;
unused counterexample predicates and statement-wide wrappers have been removed.
Theorem docstrings are limited to one or two lines. Explanatory details live here.

| Problem or result on the supplied page | Theorem declaration |
|---|---|
| Classify the finite graphs with the balanced rainbow property | `erdos_811.classification` |
| The balanced six-colour C6 question | `erdos_811.parts.cycle_six` |
| The balanced six-colour K4 question | `erdos_811.parts.clique_four` |
| Determine the quantitative threshold function `n ↦ d_G(n)` | `erdos_811.variants.rainbow_threshold` |
| The Erdős--Tuza lower and upper bounds for `d_C4(n)` | `erdos_811.variants.erdos_tuza_cycle_four_bounds` |
| Infinitely many graphs fail the property | `erdos_811.variants.infinitely_many_counterexample_graphs` |
| Odd `ℓ ≥ 3`, `m = ⌊√ℓ + 7/2⌋`: arbitrarily large balanced ℓ-colourings avoiding rainbow K_m | `erdos_811.variants.axenovich_clemen_odd_colours` |
| The all-cliques conjecture for every `q ≥ 4` | `erdos_811.variants.axenovich_clemen_all_cliques` |
| The Clemen--Wagner arbitrarily-large K4 counterexamples | `erdos_811.variants.clemen_wagner_clique_four` |

The threshold question is represented by an unknown function answer. The
C4 bound quantifies one positive real constant before the sufficiently-large
host size, and explicitly witnesses a finite natural threshold. Infinitely
many graphs means infinitely many possible vertex counts, which avoids
counting different labellings of a single finite graph. The odd-colour result
uses `ℓ` colours; the all-cliques target uses `q.choose 2` colours.
The negative six-colour K4 challenge and the arbitrarily-large K4 result
have separate declarations: the former needs one counterexample, the latter
requires counterexamples above every size bound.
For this particular clique problem they are mathematically equivalent, using
lexicographic amplification to obtain the converse from one nontrivial base.

The q=5, q=8, q=9 and q≥12 finite-base constructions are retained in the
proof project under `../lean/` as ingredients of
`erdos_811.variants.axenovich_clemen_all_cliques`. They are not listed as
separate problem targets here. This catalogue contains only the nine
problem/result theorem declarations above.

The public all-cliques target spells out its quantifiers and colour count:

```lean
theorem erdos_811.variants.axenovich_clemen_all_cliques :
    answer(True) ↔
      ∀ q : ℕ, 4 ≤ q →
        ∀ n₀ : ℕ, ∃ n : ℕ,
          n₀ ≤ n ∧
          Nat.ModEq (q.choose 2) n 1 ∧
          ∃ κ : CompleteEdgeColoring (Fin n) (Fin (q.choose 2)),
            κ.IsBalanced ∧
            ¬ HasRainbowCopy (SimpleGraph.completeGraph (Fin q)) κ
```

The legacy proof core still uses its original definitions and abbreviations.
`Erdos811NaturalBridge` proves their conversion to the shared canonical
definitions. `Erdos811NaturalTarget` supplies the proved legacy theorem to this
bridge and states the corrected target explicitly. No new research assumption
is introduced. The final naked proposition matches the right side above.

The old Formal Conjectures/LRAT development in
[`../lean/Erdos811FC.lean`](../lean/Erdos811FC.lean) is historical and retains
the old definition. The current proof source is
[`../lean/Erdos811NaturalTarget.lean`](../lean/Erdos811NaturalTarget.lean).
Its Mathlib-only copy/paste artifact is
[`../lean4web/Erdos811Lean4WebSingle.lean`](../lean4web/Erdos811Lean4WebSingle.lean);
the memory-bounded split sources are kept in the sibling working archive.

All `sorry` declarations in this directory are intentional statement holes.
They are not proof artifacts and must not be presented as a verified solution.
`category research solved` on a cited result records its known mathematical
status, not a completed Lean proof in this file.

## Threshold convention and sources

The semantic revision uses `(n - 1) / m` for balance and `Nat.ModEq m n 1`
for congruence. This repairs the one-colour boundary. D3 (rainbow copy) is
unchanged. Edgeless graphs are explicitly included in a separate MAIN case.
The screenshot's literal `floor(n/m)` is therefore normalized to the paper's
convention, not preserved at one colour. Under `m > 1` and `n ≡ 1 (mod m)`
the two degrees agree; the all-cliques endpoint always has `m ≥ 6`.

The threshold takes a proof that `0 < edgeCount G` and a positive host order
`n : ℕ+`; zero-colour/zero-vertex inputs are not silently totalized. The C4
statement explicitly supplies its positive-edge-count witness before the
real bound constant. `UsesEveryColor` requires an off-diagonal edge for every
colour; diagonal dummy values cannot satisfy it. It is a premise on the
colourings quantified in the threshold, not a field added to all colourings.

For example, at G=K3 and n=3 the revised threshold is 0: every admissible
three-colouring uses all three colours on its three edges. An all-red palette
colouring no longer supplies an inadmissible counterexample.

The threshold minimizes over `d ≤ (n - 1) / e(G)` and is `⊤` if no such
threshold forces a rainbow copy. Without this bound, impossible colour-degree
requirements would make the universal implication vacuously true and give a
misleading finite threshold. This corrects the earlier unbounded infimum in
the statement mock-up.

The convention and odd-colour construction were checked against
[Axenovich--Clemen, Section 1 and Theorem 3.3](https://arxiv.org/html/2209.13867v2).
Theorem 3.3 supplies host sizes `(ℓ + 1)^k`; the catalogue uses its
arbitrarily-large formulation from the problem page.
The admissible-degree restriction also appears in the abstract of
[Erdős--Tuza (1993)](https://doi.org/10.1016/S0167-5060(08)70377-7).
The C4 inequality is transcribed from the supplied problem-page screenshot,
with its sufficiently-large-n quantifier made explicit.

Imports name the required Formal Conjectures utilities and Mathlib modules
explicitly so that checking this statement catalogue does not load all of
Mathlib through the umbrella `FormalConjecturesUtil` import.

The revised catalogue passes elaboration with Lean 4.34.0-rc1 under `-M3072 -j1`
(2026-09-15), using the separately compiled shared definitions.
This verifies the declaration types, with the expected `sorry` warnings;
it is not proof verification of the listed research statements.

Reproduce from the workspace root:

```sh
python3 fclikelean理解用/validate_semantic_revision.py catalogue
```

## Scope boundary

The all-cliques conjecture says that every `K_q`, `q ≥ 4`, has arbitrarily
large balanced counterexamples. Even a proof of that target would not answer
the original request to classify every graph `G`.

The finite-base proof files, including
[`../lean/Q5Certificate.lean`](../lean/Q5Certificate.lean), remain available
in the shared Formal Conjectures-dependent proof development.
