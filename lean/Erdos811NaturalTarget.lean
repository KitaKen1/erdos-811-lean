import Erdos811KernelAllCliquesSplit
import Erdos811NaturalBridge

/-! Public endpoint in the canonical, natural-language definitions.
The legacy proof is used as a proved theorem, not an extra assumption.
All colours can additionally be required to occur on actual edges. -/

namespace Erdos811

theorem all_cliques_counterexamples_using_every_color :
    ∀ q : ℕ, 4 ≤ q → ∀ n₀ : ℕ, ∃ n : ℕ,
      n₀ ≤ n ∧ Nat.ModEq (q.choose 2) n 1 ∧
      ∃ κ : CompleteEdgeColoring (Fin n) (Fin (q.choose 2)),
        κ.UsesEveryColor ∧ κ.IsBalanced ∧
        ¬ HasRainbowCopy (SimpleGraph.completeGraph (Fin q)) κ := by
  exact Erdos811NaturalBridge.all_cliques_transfer
    Erdos811KernelAllCliquesSplit.axenovich_clemen_all_cliques_kernel

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

#check erdos_811.variants.axenovich_clemen_all_cliques
#print axioms erdos_811.variants.axenovich_clemen_all_cliques
#print axioms all_cliques_counterexamples_using_every_color

end Erdos811
