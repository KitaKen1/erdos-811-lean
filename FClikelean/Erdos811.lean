/-
This Lean file was created by KitaKen1 (Kenta Kitamura) with assistance from OpenAI Codex.

It imitates the style of Formal Conjectures for a possible future proposal.
It is not an official Formal Conjectures file and has not been reviewed,
approved, submitted, or merged by that project.
-/

import FormalConjecturesUtil.Answer
import FormalConjecturesUtil.Attributes.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.PNat.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Erdős Problem 811

Nine problem/result statements from [Erdős Problem #811](https://www.erdosproblems.com/811).
Proofs are intentionally left as `sorry`; sources and conventions are in `README.md`.
All problem-specific definitions are included below so that this statement draft
can be used as one file in a Formal Conjectures checkout, with no custom imports.
Their bodies match `lean/Erdos811NaturalDefinitions.lean` in the proof development.
-/

open Classical Filter

namespace Erdos811

/-- A complete edge-colouring; diagonal values are dummy values, never edges. -/
structure CompleteEdgeColoring (V C : Type*) where
  color : V → V → C
  color_symm : ∀ v w, color v w = color w v

/-- Count the actual edges of colour c incident with v; exclude the diagonal. -/
def CompleteEdgeColoring.colorDegree {V C : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq C] (κ : CompleteEdgeColoring V C) (v : V) (c : C) : ℕ :=
  ((Finset.univ.erase v).filter fun w => κ.color v w = c).card

/-- Every colour has degree (|V|-1)/|C| at every vertex. -/
def CompleteEdgeColoring.IsBalanced {V C : Type*} [Fintype V] [DecidableEq V]
    [Fintype C] [DecidableEq C] (κ : CompleteEdgeColoring V C) : Prop :=
  ∀ v c, κ.colorDegree v c = (Fintype.card V - 1) / Fintype.card C

/-- All palette colours occur on real edges, not merely on the diagonal. -/
def CompleteEdgeColoring.UsesEveryColor {V C : Type*}
    (κ : CompleteEdgeColoring V C) : Prop :=
  ∀ c, ∃ v w, v ≠ w ∧ κ.color v w = c

/-- An ordinary, not necessarily induced, rainbow copy of G. -/
def HasRainbowCopy {α V C : Type*} (G : SimpleGraph α)
    (κ : CompleteEdgeColoring V C) : Prop :=
  ∃ f : α ↪ V, ∀ ⦃a b c d : α⦄,
    G.Adj a b → G.Adj c d → ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) →
      κ.color (f a) (f b) ≠ κ.color (f c) (f d)

/-- Number of unordered edges of a finite graph. -/
noncomputable def edgeCount {α : Type*} [Fintype α] (G : SimpleGraph α) : ℕ :=
  Nat.card G.edgeSet

/-- Paper convention: positive order, positive number of edges, and every
palette colour used. The infimum of an empty admissible set is infinity. -/
noncomputable def rainbowThreshold {α : Type*} [Fintype α]
    (G : SimpleGraph α) (_hG : 0 < edgeCount G) (n : ℕ+) : ℕ∞ :=
  sInf ((fun d : ℕ => (d : ℕ∞)) ''
    {d : ℕ | d ≤ ((n : ℕ) - 1) / edgeCount G ∧
      ∀ κ : CompleteEdgeColoring (Fin (n : ℕ)) (Fin (edgeCount G)),
        κ.UsesEveryColor →
        (∀ v c, d ≤ κ.colorDegree v c) → HasRainbowCopy G κ})

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
