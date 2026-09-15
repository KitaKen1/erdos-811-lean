import Erdos811NaturalDefinitions
import Lean4WebGraphDefinitionsKernel
import Mathlib.Data.Nat.Choose.Basic
import Lean.Elab.Tactic.Omega

/-! The only interface between the legacy proof core and the canonical target.
No existence result is assumed globally. The transfer theorem has an explicit
input that the final endpoint supplies with the proved legacy theorem. -/

namespace Erdos811NaturalBridge

def toNatural {V C : Type*}
    (κ : Erdos811Lean4Web.CompleteEdgeColoring V C) :
    Erdos811.CompleteEdgeColoring V C where
  color := κ.color
  color_symm := κ.color_symm

theorem colorDegree_toNatural {V C : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq C] (κ : Erdos811Lean4Web.CompleteEdgeColoring V C)
    (v : V) (c : C) :
    (toNatural κ).colorDegree v c = κ.colorDegree v c := rfl

theorem rainbow_toNatural_iff {α V C : Type*} (G : SimpleGraph α)
    (κ : Erdos811Lean4Web.CompleteEdgeColoring V C) :
    Erdos811.HasRainbowCopy G (toNatural κ) ↔
      Erdos811Lean4Web.HasRainbowCopy G κ := Iff.rfl

theorem remainder_one_iff_modEq {n m : ℕ} (hm : 1 < m) :
    n % m = 1 ↔ Nat.ModEq m n 1 := by
  change n % m = 1 ↔ n % m = 1 % m
  rw [Nat.mod_eq_of_lt hm]

theorem pred_div_eq_div {n m : ℕ} (hm : 1 < m)
    (hn : Nat.ModEq m n 1) : (n - 1) / m = n / m := by
  have hr := (remainder_one_iff_modEq hm).mpr hn
  have hdiv := Nat.mod_add_div n m
  have hsub : n - 1 = m * (n / m) := by omega
  rw [hsub]
  exact Nat.mul_div_cancel_left (n / m) (by omega)

theorem balanced_toNatural_iff {n m : ℕ}
    (κ : Erdos811Lean4Web.CompleteEdgeColoring (Fin n) (Fin m))
    (hm : 1 < m) (hn : Nat.ModEq m n 1) :
    (toNatural κ).IsBalanced ↔ κ.IsBalanced := by
  unfold Erdos811.CompleteEdgeColoring.IsBalanced
    Erdos811Lean4Web.CompleteEdgeColoring.IsBalanced
  simp only [Fintype.card_fin, colorDegree_toNatural, pred_div_eq_div hm hn]

theorem balanced_uses_every_color {n m : ℕ} (hm : 0 < m) (hn : m < n)
    (κ : Erdos811.CompleteEdgeColoring (Fin n) (Fin m))
    (hbal : κ.IsBalanced) : κ.UsesEveryColor := by
  intro c
  let v : Fin n := ⟨0, by omega⟩
  have hpos : 0 < κ.colorDegree v c := by
    rw [hbal v c]
    simp only [Fintype.card_fin]
    exact Nat.div_pos (by omega) hm
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
  rcases Finset.mem_filter.mp hw with ⟨hmem, hcol⟩
  exact ⟨v, w, (Finset.mem_erase.mp hmem).1.symm, hcol⟩

theorem choose_two_gt_one {q : ℕ} (hq : 4 ≤ q) : 1 < q.choose 2 := by
  have h := Nat.choose_le_choose 2 hq
  have h4 : Nat.choose 4 2 = 6 := by decide
  rw [h4] at h
  omega

theorem all_cliques_transfer
    (hlegacy : ∀ q : ℕ, 4 ≤ q → ∀ n₀ : ℕ, ∃ n : ℕ,
      n₀ ≤ n ∧ n % (q.choose 2) = 1 ∧
      ∃ κ : Erdos811Lean4Web.CompleteEdgeColoring (Fin n) (Fin (q.choose 2)),
        κ.IsBalanced ∧
        ¬ Erdos811Lean4Web.HasRainbowCopy (SimpleGraph.completeGraph (Fin q)) κ) :
    ∀ q : ℕ, 4 ≤ q → ∀ n₀ : ℕ, ∃ n : ℕ,
      n₀ ≤ n ∧ Nat.ModEq (q.choose 2) n 1 ∧
      ∃ κ : Erdos811.CompleteEdgeColoring (Fin n) (Fin (q.choose 2)),
        κ.UsesEveryColor ∧ κ.IsBalanced ∧
        ¬ Erdos811.HasRainbowCopy (SimpleGraph.completeGraph (Fin q)) κ := by
  intro q hq n₀
  have hm := choose_two_gt_one hq
  obtain ⟨n, hn, hr, κ, hbal, hno⟩ := hlegacy q hq (max n₀ (q.choose 2 + 1))
  have hlarge : q.choose 2 < n := lt_of_lt_of_le (by omega) (le_trans (le_max_right _ _) hn)
  have hn₀ : n₀ ≤ n := le_trans (le_max_left _ _) hn
  have hmod := (remainder_one_iff_modEq hm).mp hr
  have hbal' := (balanced_toNatural_iff κ hm hmod).mpr hbal
  refine ⟨n, hn₀, hmod, toNatural κ, ?_, hbal', ?_⟩
  · exact balanced_uses_every_color (by omega) hlarge (toNatural κ) hbal'
  · intro h
    exact hno ((rainbow_toNatural_iff _ κ).mp h)

#print axioms balanced_toNatural_iff
#print axioms all_cliques_transfer

end Erdos811NaturalBridge
