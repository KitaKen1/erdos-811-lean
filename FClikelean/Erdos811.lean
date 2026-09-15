/-
This Lean file was created by KitaKen1 (Kenta Kitamura) with assistance from OpenAI Codex.

It imitates the style of Formal Conjectures for a possible future proposal.
It is not an official Formal Conjectures file and has not been reviewed,
approved, submitted, or merged by that project.
-/

import FormalConjecturesUtil.Answer
import FormalConjecturesUtil.Attributes.Basic
import Erdos811NaturalDefinitions
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Erdős Problem 811

Nine problem/result statements from [Erdős Problem #811](https://www.erdosproblems.com/811).
Proofs are intentionally left as `sorry`; sources and conventions are in `README.md`.
The definitions are shared with the proved natural-language endpoint through
`Erdos811NaturalDefinitions`, not duplicated in this catalogue.
-/

open Classical Filter

namespace Erdos811

/-- Classify graphs forced as rainbow copies by all sufficiently large balanced colourings. -/
@[category research open, AMS 5]
theorem erdos_811.classification (α : Type*) [Fintype α] [DecidableEq α] :
    {G : SimpleGraph α | edgeCount G = 0 ∨
      (0 < edgeCount G ∧
      ∀ᶠ n : ℕ in atTop, Nat.ModEq (edgeCount G) n 1 →
        ∀ κ : CompleteEdgeColoring (Fin n) (Fin (edgeCount G)),
          κ.IsBalanced → HasRainbowCopy G κ)} = answer(sorry) := by
  sorry

/-- Does every balanced six-colouring of `K_(6k+1)`, `k ≥ 1`, contain a rainbow C6? -/
@[category research open, AMS 5]
theorem erdos_811.parts.cycle_six :
    answer(sorry) ↔
      ∀ k : ℕ, 1 ≤ k →
        ∀ κ : CompleteEdgeColoring (Fin (6 * k + 1)) (Fin 6),
          κ.IsBalanced → HasRainbowCopy (SimpleGraph.cycleGraph 6) κ := by
  sorry

/-- Does every balanced six-colouring of `K_(6k+1)`, `k ≥ 1`, contain a rainbow K4? -/
@[category research solved, AMS 5]
theorem erdos_811.parts.clique_four :
    answer(False) ↔
      ∀ k : ℕ, 1 ≤ k →
        ∀ κ : CompleteEdgeColoring (Fin (6 * k + 1)) (Fin 6),
          κ.IsBalanced → HasRainbowCopy (SimpleGraph.completeGraph (Fin 4)) κ := by
  sorry

/-- Determine the threshold function `n ↦ d_G(n)` for each finite graph G. -/
@[category research open, AMS 5]
theorem erdos_811.variants.rainbow_threshold
    (v : ℕ) (G : SimpleGraph (Fin v)) (hG : 0 < edgeCount G) :
    (fun n : ℕ+ => rainbowThreshold G hG n) = answer(sorry) := by
  sorry

/-- Erdős--Tuza: eventually `⌊n/6⌋ ≤ d_C4(n) ≤ (1/4 - c)n` for some `c > 0`. -/
@[category research solved, AMS 5]
theorem erdos_811.variants.erdos_tuza_cycle_four_bounds :
    ∃ hG : 0 < edgeCount (SimpleGraph.cycleGraph 4),
      ∃ c : ℝ, 0 < c ∧
        ∀ᶠ n : ℕ+ in atTop, ∃ d : ℕ,
          rainbowThreshold (SimpleGraph.cycleGraph 4) hG n = (d : ℕ∞) ∧
          (n : ℕ) / 6 ≤ d ∧
          (d : ℝ) ≤ (1 / 4 - c) * ((n : ℕ) : ℝ) := by
  sorry

/-- Axenovich--Clemen: infinitely many finite graphs have arbitrarily large balanced counterexamples. -/
@[category research solved, AMS 5]
theorem erdos_811.variants.infinitely_many_counterexample_graphs :
    Set.Infinite {v : ℕ | ∃ G : SimpleGraph (Fin v),
      0 < edgeCount G ∧
      ∀ n₀ : ℕ, ∃ n : ℕ,
        n₀ ≤ n ∧
        Nat.ModEq (edgeCount G) n 1 ∧
        ∃ κ : CompleteEdgeColoring (Fin n) (Fin (edgeCount G)),
          κ.IsBalanced ∧ ¬ HasRainbowCopy G κ} := by
  sorry

/-- Axenovich--Clemen: odd `ℓ ≥ 3` admits arbitrarily large balanced ℓ-colourings
without a rainbow clique of order `⌊√ℓ + 7/2⌋`. -/
@[category research solved, AMS 5]
theorem erdos_811.variants.axenovich_clemen_odd_colours :
    ∀ ℓ : ℕ, 3 ≤ ℓ → Odd ℓ →
      let m : ℕ := ⌊Real.sqrt (ℓ : ℝ) + 7 / 2⌋₊
      ∀ n₀ : ℕ, ∃ n : ℕ,
        n₀ ≤ n ∧
        Nat.ModEq ℓ n 1 ∧
        ∃ κ : CompleteEdgeColoring (Fin n) (Fin ℓ),
          κ.IsBalanced ∧ ¬ HasRainbowCopy (SimpleGraph.completeGraph (Fin m)) κ := by
  sorry

/-- Clemen--Wagner: arbitrarily large balanced six-colourings avoid rainbow K4. -/
@[category research solved, AMS 5]
theorem erdos_811.variants.clemen_wagner_clique_four :
    ∀ n₀ : ℕ, ∃ n : ℕ,
      n₀ ≤ n ∧
      Nat.ModEq 6 n 1 ∧
      ∃ κ : CompleteEdgeColoring (Fin n) (Fin 6),
        κ.IsBalanced ∧ ¬ HasRainbowCopy (SimpleGraph.completeGraph (Fin 4)) κ := by
  sorry

/-- Axenovich--Clemen conjecture: every `q ≥ 4` has arbitrarily large balanced
`q.choose 2`-colourings with no rainbow K_q. -/
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

end Erdos811
