# Erdős Problem #811 in Lean

This repository contains a statement catalogue and a proof of the all-cliques
conjecture associated with [Erdős Problem #811][problem]. It does **not** solve
the main problem of classifying all finite graphs with the balanced rainbow
property.

The development has two components:

1. **Nine source-level statements.** [The FC-shaped catalogue](FClikelean/Erdos811.lean)
   includes MAIN, the two six-colour challenges, and six variants or known results
   from the supplied problem page.
2. **A proof for every clique of order at least four.** For every `q ≥ 4`,
   there are arbitrarily large completely balanced colourings using exactly
   `q.choose 2` colours with no rainbow `K_q`.

**Try it in Lean4Web:** [open the standalone proof](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Ferdos-811-lean%2Frefs%2Fheads%2Fmain%2Flean4web%2FErdos811Lean4WebSingle.lean)

Start with the [standalone proof](lean4web/Erdos811Lean4WebSingle.lean), or read
the short [final theorem](lean/Erdos811NaturalTarget.lean). The standalone file
needs only Lean and Mathlib, not Formal Conjectures. It is also the copy/paste
artifact for [Lean4Web](https://live.lean-lang.org/), provided a compatible
Lean/Mathlib `4.27.0` environment is available. Local checking is recommended
because the complete proof is resource-intensive.

## Problem and variant status

For a graph `G` with `m = e(G) > 0`, its balanced rainbow property means:
for every sufficiently large `n ≡ 1 (mod m)`, every completely balanced
`m`-colouring of `K_n` contains a rainbow copy of `G`. A rainbow copy has
pairwise distinct edge colours; it need not be an induced subgraph.

All declaration names below are relative to the namespace `Erdos811`.

| Entry | Statement and relation to MAIN | Status | Source |
|---|---|---|---|
| MAIN — `erdos_811.classification` | Determine exactly which finite graphs have the balanced rainbow property. | OPEN; not solved here | [#811][problem], Erdős–Pyber–Tuza / [Erdős–Tuza][ertu] |
| `erdos_811.parts.cycle_six` | Does every balanced six-colouring of `K_(6k+1)`, `k ≥ 1`, contain a rainbow `C6`? This asks for every such order, not just sufficiently large orders. | OPEN; not solved here | Erdős's six-colour challenge on [#811][problem] |
| `erdos_811.parts.clique_four` | The corresponding question for `K4`. Its negative answer also excludes `K4` from MAIN via amplification. | SOLVED previously — No | [Clemen–Wagner 2023][cw] |

### Problem-page remarks: variants and known results

The following names have the prefix `erdos_811.variants.`.

| Entry | Statement and relation to MAIN | Status | Source |
|---|---|---|---|
| `rainbow_threshold` | Determine `d_G(n)`, the least admissible minimum degree in each colour that forces a rainbow `G`. A quantitative extension of MAIN. | OPEN in general | [#811][problem], [Erdős–Tuza][ertu] |
| `erdos_tuza_cycle_four_bounds` | Eventually `⌊n/6⌋ ≤ d_C4(n) ≤ (1/4 − c)n` for some `c > 0`. Bounds for one graph, not an exact general threshold. | SOLVED previously | [Erdős–Tuza 1993][ertu], inequality recorded on [#811][problem] |
| `infinitely_many_counterexample_graphs` | Infinitely many finite graphs fail MAIN's property. Thus “every graph has it” was already disproved. | SOLVED previously | [Axenovich–Clemen][ac] |
| `axenovich_clemen_odd_colours` | For odd `ℓ ≥ 3`, arbitrarily large balanced `ℓ`-colourings avoid rainbow `K_⌊√ℓ+7/2⌋`. Here `ℓ` need not equal the clique's edge count. | SOLVED previously | [Axenovich–Clemen, Theorem 3.3][ac] |
| `clemen_wagner_clique_four` | Arbitrarily large balanced six-colourings avoid rainbow `K4`: the explicit MAIN counterexample formulation of the result above. | SOLVED previously | [Clemen–Wagner 2023][cw] |
| `axenovich_clemen_all_cliques` | Every `K_q`, `q ≥ 4`, fails MAIN's property, using exactly `e(K_q)` colours. This classifies this clique family on the No side, not all graphs. | OPEN → SOLVED — proof in this repository | [Axenovich–Clemen, Conjecture 1.3][ac]; [Lean endpoint](lean/Erdos811NaturalTarget.lean) |

The last row subsumes the `K4` counterexamples and implies infinitely many No
graphs. It does not answer the `C6` question or determine the general threshold.
The odd-colour theorem changes the palette size and is not simply another
name for the all-cliques conjecture.

## Formal Conjectures-shaped proved target

The [catalogue](FClikelean/Erdos811.lean) records the all-cliques entry as follows,
inside `namespace Erdos811`:

```lean
@[category research open, AMS 5]
theorem erdos_811.variants.axenovich_clemen_all_cliques :
    answer(True) ↔
      ∀ q : ℕ, 4 ≤ q →
        ∀ n₀ : ℕ, ∃ n : ℕ,
          n₀ ≤ n ∧
          Nat.ModEq (q.choose 2) n 1 ∧
          ∃ κ : CompleteEdgeColoring (Fin n) (Fin (q.choose 2)),
            κ.IsBalanced ∧
            ¬ HasRainbowCopy (SimpleGraph.completeGraph (Fin q)) κ := by
  sorry
```

`answer(True)` records the proposed affirmative answer to the
*counterexample-existence conjecture*, not to MAIN's rainbow property.
The final `sorry` is a catalogue placeholder. All nine catalogue proof bodies
are placeholders, including entries tagged `research solved`; those tags
describe source status, not proofs in that file.

The separate [proof endpoint](lean/Erdos811NaturalTarget.lean) proves the
right-hand proposition directly, without the `answer` wrapper:

```lean
theorem erdos_811.variants.axenovich_clemen_all_cliques :
    ∀ q : ℕ, 4 ≤ q →
      ∀ n₀ : ℕ, ∃ n : ℕ,
        n₀ ≤ n ∧
        Nat.ModEq (q.choose 2) n 1 ∧
        ∃ κ : CompleteEdgeColoring (Fin n) (Fin (q.choose 2)),
          κ.IsBalanced ∧
          ¬ HasRainbowCopy (SimpleGraph.completeGraph (Fin q)) κ := by
  intro q hq n₀
  obtain ⟨n, hn, hmod, κ, _hused, hbal, hno⟩ :=
    all_cliques_counterexamples_using_every_color q hq n₀
  exact ⟨n, hn, hmod, κ, hbal, hno⟩
```

The stronger theorem `Erdos811.all_cliques_counterexamples_using_every_color`
also supplies `κ.UsesEveryColor`. It applies a proved conversion to the proved
construction, not to an assumed research result. The catalogue and proof are
checked separately: their shared declaration name does not make the
catalogue's `sorry` a dependency of the proof.

### Natural-language conventions

The [shared definitions](lean/Erdos811NaturalDefinitions.lean) count only
off-diagonal edges, identify the two orientations of an undirected edge, and
require injective vertex maps for rainbow copies. Balance uses `(n − 1) / m`,
and congruence uses `Nat.ModEq m n 1`.

This follows the [paper's complete-balance convention][ac]. The supplied
page's `⌊n/m⌋` agrees when `m > 1` and `n ≡ 1 (mod m)`; `(n − 1) / m` also
handles one colour correctly. The clique target always has `m ≥ 6`.

The threshold requires positive host order, positive edge count, every colour
on an actual edge, and `d ≤ ⌊(n − 1)/e(G)⌋`; it is `∞` if no admissible
threshold works. Edgeless graphs are included separately in MAIN. Further
conventions are explained in [FClikelean/README.md](FClikelean/README.md).

## Directory layout

| File | Role |
|---|---|
| [FClikelean/Erdos811.lean](FClikelean/Erdos811.lean) | Nine statements with FC-style metadata and intentional proof placeholders |
| [FClikelean/README.md](FClikelean/README.md) | Declaration-to-source mapping and definition conventions |
| [lean/Erdos811NaturalDefinitions.lean](lean/Erdos811NaturalDefinitions.lean) | Canonical definitions shared by catalogue and endpoint |
| [lean/Erdos811NaturalBridge.lean](lean/Erdos811NaturalBridge.lean) | Proved transfer from the construction's legacy definitions |
| [lean/Erdos811NaturalTarget.lean](lean/Erdos811NaturalTarget.lean) | Current endpoint and stronger all-colours-used theorem |
| [lean4web/Erdos811Lean4WebSingle.lean](lean4web/Erdos811Lean4WebSingle.lean) | Complete Mathlib-only proof, including current definitions, bridge and endpoint |
| [lean/Erdos811FC.lean](lean/Erdos811FC.lean) and [lean/lakefile.toml](lean/lakefile.toml) | Historical FC/LRAT development and build configuration; not the current standalone verification route |

The short endpoint imports split modules that are inlined in the standalone
file. Use the bundle to check the current result without the separate
development archive. A default `lake build` in `lean/` targets the historical
development, not the revised endpoint.

## Verification

| Artifact | Environment | Recorded check on 2026-09-15 |
|---|---|---|
| Complete standalone proof | Lean / Mathlib `4.27.0` | Passed from source; exit code 0; approximately 58 minutes |
| Shared-definition bridge | Lean / Mathlib `4.27.0` | Passed; no warnings |
| FC-shaped catalogue | Lean / Mathlib `4.34.0-rc1`, Formal Conjectures utilities | Elaborated successfully; nine expected proof-placeholder warnings |

The standalone file contains 96 bundled modules and 14,975 lines. The full
run used `-M3072 -j1` and emitted 92 style/linter warnings in retained proof
code, with no proof-hole warnings. Both current endpoint declarations report:

```text
[propext, Classical.choice, Quot.sound]
```

Their dependencies contain no `sorryAx` or project-specific mathematical
axioms. The proof does not use `sorry`, `admit`, or the `native_decide` tactic.
Its `q = 9` branch uses the arithmetic proof, not the historical SAT/LRAT route.

### Rechecking the standalone proof

With Lean's `elan` toolchain manager installed, prepare a separate Mathlib
`v4.27.0` checkout and fetch its compiled dependencies:

```sh
git clone --branch v4.27.0 --depth 1 https://github.com/leanprover-community/mathlib4.git erdos811-mathlib
cd erdos811-mathlib
lake exe cache get
```

From that checkout, run the following after replacing `/absolute/path/to`
with the path to this repository:

```sh
lake env lean -M3072 -j1 "/absolute/path/to/lean4web/Erdos811Lean4WebSingle.lean"
```

The checked Mathlib revision is
`a3a10db0e9d66acbebf76c5e6a135066525ac900` (`v4.27.0`). Allow substantial time
and several gigabytes of memory; runtime depends on the machine or browser
session. No development-archive modules are needed by this single-file route.

The catalogue's recorded elaboration used Formal Conjectures commit
`205d301d60d01a2a432cbea611f9383cd08f9065` and separately compiled
`Erdos811NaturalDefinitions`, with Lean `4.34.0-rc1`. Elaboration checks
statement types; it does not discharge the nine `sorry`s.

SHA-256 of the fully checked standalone source:

```text
2a777ad201e386a38af5c70b3a75d1fec5064a9c94c5d1dc6b4d7dea3600cdcd
```

## Mathematical proof explanation (AI generated)

The proof first constructs a finite balanced counterexample for each clique
order, using specific constructions for the small cases and a uniform tail
argument.

| Clique order | Finite construction or argument |
|---|---|
| `q = 4` | The known Clemen–Wagner six-colouring of `K13` |
| `q = 5` | A ten-colouring of `K21`, with a compact finite certificate |
| `q = 6, 7, 10, 11` | Round-robin colourings and weak-Sidon bounds |
| `q = 8` | An arithmetic proof for a 28-colouring of `K57` |
| `q = 9` | An unanchored arithmetic proof for a 36-colouring of `K73` |
| `q ≥ 12` | A probabilistic pairing construction |

Lexicographic powers preserve balance and the absence of rainbow cliques,
so each nontrivial finite base produces examples above every size bound.
This is the amplification principle of [Axenovich–Clemen, Section 2][ac],
also proved in the development.

The final bridge preserves colours, colour degrees and rainbow copies while
converting to the shared definitions. Taking a sufficiently large example
makes every colour degree positive, giving the stronger all-colours-used
conclusion. These steps do not classify arbitrary graphs.

## References

- [Erdős Problems #811][problem] — main question and problem-page remarks.
- [P. Erdős and Z. Tuza (1993)][ertu] — original rainbow-subgraph problem and thresholds.
- [M. Axenovich and F. C. Clemen, *Rainbow Subgraphs in Edge-colored Complete Graphs — Answering two Questions by Erdős and Tuza*][ac].
- [F. C. Clemen and A. Z. Wagner, *A note on balanced edge-colorings avoiding rainbow cliques of size four* (2023)][cw].
- [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) — statement-format reference; this catalogue is unofficial.
- [Erdős #878 Lean repository](https://github.com/KitaKen1/erdos-878-lean) — README presentation model.

## AI usage disclosure

KitaKen1 (Kenta Kitamura) directed this development with assistance from
OpenAI Codex in formalization, proof development and documentation.

[problem]: https://www.erdosproblems.com/811
[ertu]: https://doi.org/10.1016/S0167-5060(08)70377-7
[ac]: https://arxiv.org/html/2209.13867v2
[cw]: https://arxiv.org/abs/2303.15476
