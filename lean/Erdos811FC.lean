import FormalConjecturesUtil
import Erdos811Definitions
import Q5Certificate
import Q4Certificate
import Lexicographic
import LexAmplification
import CyclicBases
import Q8PaperInfinityGraph
import Q9NoInfLRATFinal
import ProbabilisticBound
import RoundRobinSidonCases

/-!
# Erdős Problem 811: Formal Conjectures proof target

HISTORICAL ENTRY POINT: this file retains the legacy floor(n/m) definitions
and LRAT route. The corrected natural-language endpoint is
`Erdos811NaturalTarget.lean`, included in the current Mathlib-only public bundle.
The revised FClikelean catalogue imports `Erdos811NaturalDefinitions` instead.
Do not import the legacy and canonical Erdos811 definition modules together.

This file mirrors the exact all-cliques target declared in
`../FClikelean/Erdos811.lean`. The q = 5 finite certificate is imported from
`Q5Certificate`; q = 8 uses the checked paper-style certificate, and q = 9 now
uses the staged LRAT replay plus the finite translation bridge in
  `Q9Symmetry`. The q = 6, 7, 10, 11 bases use the search-free weak-Sidon
  proof. The q ≥ 12 probabilistic witness and final all-q dispatcher are also
  connected; any remaining certificate boundary stays visible in the audit.
-/

open Classical Filter

namespace Erdos811

private theorem q5_finite_base_for_target :
    HasBalancedCounterexampleAt (SimpleGraph.completeGraph (Fin 5)) 21 := by
  exact Erdos811.q5_finite_base

/-- Kernel-checkable versions of the independently checked cyclic bases. -/
private theorem q8_finite_base :
    HasBalancedCounterexampleAt (SimpleGraph.completeGraph (Fin 8)) 57 :=
  q8_finite_base_paper

private theorem q9_finite_base :
    HasBalancedCounterexampleAt (SimpleGraph.completeGraph (Fin 9)) 73 := by
  have hEdge : edgeCount (SimpleGraph.completeGraph (Fin 9)) = 36 := by
    rw [edgeCount_completeGraph_fin]
    decide
  unfold HasBalancedCounterexampleAt
  rw [hEdge]
  refine ⟨by norm_num, q9Coloring, q9_balanced, ?_⟩
  exact q9_no_rainbow_staged_lrat

theorem hasArbitrarilyLarge_of_finite_counterexample
    (q n : ℕ)
    (hbase : HasBalancedCounterexampleAt
      (SimpleGraph.completeGraph (Fin q)) n)
    (hn : 2 ≤ n)
    (hm : 1 < edgeCount (SimpleGraph.completeGraph (Fin q))) :
    HasArbitrarilyLargeBalancedCounterexamples
      (SimpleGraph.completeGraph (Fin q)) := by
  rcases hbase with ⟨hmod, κ, hbal, hno⟩
  exact hasArbitrarilyLarge_of_finite_base q n hmod κ hbal hno hn hm

theorem q5_lex_square_balanced :
    (lexColoring q5Coloring).IsBalanced := by
  apply lexColoring_isBalanced_of_balanced q5Coloring 2 q5_balanced
  · norm_num
  · norm_num

theorem q5_lex_square_no_rainbow :
    ¬ HasRainbowCopy (SimpleGraph.completeGraph (Fin 5))
      (lexColoring q5Coloring) := by
  exact lexColoring_no_rainbow_of_no_rainbow 5 q5Coloring q5_no_rainbow

theorem q5_lexPow_no_rainbow (k : ℕ) :
    ¬ HasRainbowCopy (SimpleGraph.completeGraph (Fin 5))
      (lexPowColoring q5Coloring k) := by
  exact lexPow_no_rainbow q5Coloring 5 q5_no_rainbow k

theorem q8_lex_square_balanced :
    (lexColoring q8Coloring).IsBalanced := by
  apply lexColoring_isBalanced_of_balanced q8Coloring 2 q8_balanced
  · norm_num
  · norm_num

theorem q9_lex_square_balanced :
    (lexColoring q9Coloring).IsBalanced := by
  apply lexColoring_isBalanced_of_balanced q9Coloring 2 q9_balanced
  · norm_num
  · norm_num

/- The finite bases now feed the canonical `Fin`-host amplification lemma.
   These are deliberately stated separately from the final all-q theorem so
   that each finite certificate and its amplification can be audited on its
   own. -/
theorem q5_arbitrarily_large :
    HasArbitrarilyLargeBalancedCounterexamples
      (SimpleGraph.completeGraph (Fin 5)) := by
  apply hasArbitrarilyLarge_of_finite_counterexample 5 21 q5_finite_base
  · norm_num
  · norm_num [edgeCount_completeGraph_fin, Nat.choose]

theorem q8_arbitrarily_large :
    HasArbitrarilyLargeBalancedCounterexamples
      (SimpleGraph.completeGraph (Fin 8)) := by
  apply hasArbitrarilyLarge_of_finite_counterexample 8 57 q8_finite_base
  · norm_num
  · norm_num [edgeCount_completeGraph_fin, Nat.choose]

theorem q9_arbitrarily_large :
    HasArbitrarilyLargeBalancedCounterexamples
      (SimpleGraph.completeGraph (Fin 9)) := by
  apply hasArbitrarilyLarge_of_finite_counterexample 9 73 q9_finite_base
  · norm_num
  · norm_num [edgeCount_completeGraph_fin, Nat.choose]

#print axioms q5_arbitrarily_large
#print axioms q8_arbitrarily_large
#print axioms q9_arbitrarily_large

theorem q4_arbitrarily_large :
    HasArbitrarilyLargeBalancedCounterexamples
      (SimpleGraph.completeGraph (Fin 4)) := by
  apply hasArbitrarilyLarge_of_finite_counterexample 4 13 q4_finite_base
  · norm_num
  · norm_num [edgeCount_completeGraph_fin, Nat.choose]

#print axioms q4_arbitrarily_large

/- The standard round-robin objects make the finite obligations explicit. -/
theorem q6_finite_base_of_roundRobin_no_rainbow
    (hno : ¬ HasRainbowCopy (SimpleGraph.completeGraph (Fin 6))
      q6RoundRobinColoring) :
    HasBalancedCounterexampleAt
      (SimpleGraph.completeGraph (Fin 6)) 16 := by
  have hEdge : edgeCount (SimpleGraph.completeGraph (Fin 6)) = 15 := by
    rw [edgeCount_completeGraph_fin]
    decide
  unfold HasBalancedCounterexampleAt
  refine ⟨q6_roundRobin_order, ?_⟩
  rw [hEdge]
  exact ⟨q6RoundRobinColoring, q6_roundRobin_balanced, hno⟩

theorem q6_finite_base :
    HasBalancedCounterexampleAt
      (SimpleGraph.completeGraph (Fin 6)) 16 :=
  q6_finite_base_of_roundRobin_no_rainbow q6_no_rainbow_sidon

theorem q6_arbitrarily_large :
    HasArbitrarilyLargeBalancedCounterexamples
      (SimpleGraph.completeGraph (Fin 6)) := by
  apply hasArbitrarilyLarge_of_finite_counterexample 6 16 q6_finite_base
  · norm_num
  · norm_num [edgeCount_completeGraph_fin, Nat.choose]

#print axioms q6_arbitrarily_large

theorem q7_finite_base_of_roundRobin_no_rainbow
    (hno : ¬ HasRainbowCopy (SimpleGraph.completeGraph (Fin 7))
      q7RoundRobinColoring) :
    HasBalancedCounterexampleAt
      (SimpleGraph.completeGraph (Fin 7)) 22 := by
  have hEdge : edgeCount (SimpleGraph.completeGraph (Fin 7)) = 21 := by
    rw [edgeCount_completeGraph_fin]
    decide
  unfold HasBalancedCounterexampleAt
  refine ⟨q7_roundRobin_order, ?_⟩
  rw [hEdge]
  exact ⟨q7RoundRobinColoring, q7_roundRobin_balanced, hno⟩

theorem q7_finite_base :
    HasBalancedCounterexampleAt
      (SimpleGraph.completeGraph (Fin 7)) 22 :=
  q7_finite_base_of_roundRobin_no_rainbow q7_no_rainbow_sidon

theorem q7_arbitrarily_large :
    HasArbitrarilyLargeBalancedCounterexamples
      (SimpleGraph.completeGraph (Fin 7)) := by
  apply hasArbitrarilyLarge_of_finite_counterexample 7 22 q7_finite_base
  · norm_num
  · norm_num [edgeCount_completeGraph_fin, Nat.choose]

#print axioms q7_arbitrarily_large

theorem q10_finite_base_of_roundRobin_no_rainbow
    (hno : ¬ HasRainbowCopy (SimpleGraph.completeGraph (Fin 10))
      q10RoundRobinColoring) :
    HasBalancedCounterexampleAt
      (SimpleGraph.completeGraph (Fin 10)) 46 := by
  have hEdge : edgeCount (SimpleGraph.completeGraph (Fin 10)) = 45 := by
    rw [edgeCount_completeGraph_fin]
    decide
  unfold HasBalancedCounterexampleAt
  refine ⟨q10_roundRobin_order, ?_⟩
  rw [hEdge]
  exact ⟨q10RoundRobinColoring, q10_roundRobin_balanced, hno⟩

theorem q11_finite_base_of_roundRobin_no_rainbow
    (hno : ¬ HasRainbowCopy (SimpleGraph.completeGraph (Fin 11))
      q11RoundRobinColoring) :
    HasBalancedCounterexampleAt
      (SimpleGraph.completeGraph (Fin 11)) 56 := by
  have hEdge : edgeCount (SimpleGraph.completeGraph (Fin 11)) = 55 := by
    rw [edgeCount_completeGraph_fin]
    decide
  unfold HasBalancedCounterexampleAt
  refine ⟨q11_roundRobin_order, ?_⟩
  rw [hEdge]
  exact ⟨q11RoundRobinColoring, q11_roundRobin_balanced, hno⟩

theorem q10_finite_base :
    HasBalancedCounterexampleAt
      (SimpleGraph.completeGraph (Fin 10)) 46 :=
  q10_finite_base_of_roundRobin_no_rainbow q10_no_rainbow_sidon

theorem q10_arbitrarily_large :
    HasArbitrarilyLargeBalancedCounterexamples
      (SimpleGraph.completeGraph (Fin 10)) := by
  apply hasArbitrarilyLarge_of_finite_counterexample 10 46 q10_finite_base
  · norm_num
  · norm_num [edgeCount_completeGraph_fin, Nat.choose]

#print axioms q10_arbitrarily_large

theorem q11_finite_base :
    HasBalancedCounterexampleAt
      (SimpleGraph.completeGraph (Fin 11)) 56 :=
  q11_finite_base_of_roundRobin_no_rainbow q11_no_rainbow_sidon

theorem q11_arbitrarily_large :
    HasArbitrarilyLargeBalancedCounterexamples
      (SimpleGraph.completeGraph (Fin 11)) := by
  apply hasArbitrarilyLarge_of_finite_counterexample 11 56 q11_finite_base
  · norm_num
  · norm_num [edgeCount_completeGraph_fin, Nat.choose]

#print axioms q11_arbitrarily_large

theorem q12_probability_checkpoint : expectedBadOrbit 12 < 1 :=
  q12_expectedBadOrbit_lt_one

theorem q12_probability_stronger_checkpoint :
    expectedBadOrbit 12 < (3 : ℚ) / 20 :=
  q12_expectedBadOrbit_lt_three_twentieths

theorem q13_probability_ratio_checkpoint :
    ∀ q : ℕ, 13 ≤ q → (36 : ℚ) * q / 2 ^ q < 1 :=
  ratio_36q_two_pow_lt_one

theorem probabilistic_order_checkpoint (q : ℕ) (hq : 4 ≤ q) :
    (2 * q * (q - 1) + 1) %
        edgeCount (SimpleGraph.completeGraph (Fin q)) = 1 :=
  probabilistic_order_mod_edgeCount q hq

/- Once the finite bases and probabilistic pairing lemma are supplied, the
   remaining quantifier bookkeeping is entirely elementary. Keeping this
   dispatcher explicit makes every q-case auditable. -/
theorem all_cliques_of_base_family
    (h4 : HasArbitrarilyLargeBalancedCounterexamples
      (SimpleGraph.completeGraph (Fin 4)))
    (h6 : HasArbitrarilyLargeBalancedCounterexamples
      (SimpleGraph.completeGraph (Fin 6)))
    (h7 : HasArbitrarilyLargeBalancedCounterexamples
      (SimpleGraph.completeGraph (Fin 7)))
    (hprob : ∀ q : ℕ, 12 ≤ q → HasProbabilisticPairingWitness q) :
    AllCliquesHaveCounterexamples := by
  intro q hq
  by_cases hlarge : 12 ≤ q
  · exact probabilistic_witness_to_arbitrarily_large q (by omega)
      (hprob q hlarge)
  · have hqle : q ≤ 11 := by omega
    have hcases : q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 ∨ q = 8 ∨
        q = 9 ∨ q = 10 ∨ q = 11 := by omega
    rcases hcases with rfl | hcases
    · exact h4
    rcases hcases with rfl | hcases
    · exact q5_arbitrarily_large
    rcases hcases with rfl | hcases
    · exact h6
    rcases hcases with rfl | hcases
    · exact h7
    rcases hcases with rfl | hcases
    · exact q8_arbitrarily_large
    rcases hcases with rfl | hcases
    · exact q9_arbitrarily_large
    rcases hcases with rfl | rfl
    · exact q10_arbitrarily_large
    · exact q11_arbitrarily_large

#print axioms all_cliques_of_base_family

/-- The remaining mathematical input: a pairing of the `2m` cyclic
    difference classes with no bad translation orbit. -/
private theorem probabilistic_pairing_witness :
    ∀ q : ℕ, 12 ≤ q → HasProbabilisticPairingWitness q := by
  intro q hq
  exact probabilistic_pairing_witness_of_expectedBadOrbit_lt_one q hq

/-- The finite-base statement is now a direct consequence of the explicit
    pairing-witness interface and the congruence lemma. -/
private theorem probabilistic_bases :
    ∀ q : ℕ, 12 ≤ q →
      HasBalancedCounterexampleAt (SimpleGraph.completeGraph (Fin q))
        (2 * q * (q - 1) + 1) := by
  intro q hq
  exact probabilistic_witness_to_finite_base q (by omega)
    (probabilistic_pairing_witness q hq)

theorem all_cliques_from_remaining_inputs
    (h7 : HasArbitrarilyLargeBalancedCounterexamples
      (SimpleGraph.completeGraph (Fin 7)))
    :
    AllCliquesHaveCounterexamples := by
  apply all_cliques_of_base_family q4_arbitrarily_large q6_arbitrarily_large
    h7
  exact probabilistic_pairing_witness

#print axioms all_cliques_from_remaining_inputs

/-- Axenovich--Clemen: every clique `K_q`, `q ≥ 4`, has arbitrarily large
    balanced counterexamples. -/
@[category research open, AMS 5]
theorem erdos_811.variants.axenovich_clemen_all_cliques :
    answer(True) ↔
      ∀ q : ℕ, 4 ≤ q →
        ∀ n₀ : ℕ, ∃ n : ℕ,
          n₀ ≤ n ∧
          n % (q.choose 2) = 1 ∧
          ∃ κ : CompleteEdgeColoring (Fin n) (Fin (q.choose 2)),
            κ.IsBalanced ∧
            ¬ HasRainbowCopy (SimpleGraph.completeGraph (Fin q)) κ := by
  constructor
  · intro _
    intro q hq
    have h := all_cliques_from_remaining_inputs q7_arbitrarily_large q hq
    simp only [HasArbitrarilyLargeBalancedCounterexamples,
      HasBalancedCounterexampleAt] at h
    rw [edgeCount_completeGraph_fin q] at h
    exact h
  · intro _
    trivial

#check erdos_811.variants.axenovich_clemen_all_cliques
#print axioms erdos_811.variants.axenovich_clemen_all_cliques

end Erdos811
