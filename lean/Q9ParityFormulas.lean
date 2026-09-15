import Q9Parity
import Q9FastSearch

/-! Natural-number formulas for the cyclic q=9 edge colours. -/

namespace Erdos811

lemma q9Color_val_fast (i j : Fin 73) :
    (q9Coloring.color i j).val = q9EdgeColorFast i.val j.val := by
  by_cases hi : i.val = 72 <;> by_cases hj : j.val = 72 <;>
    simp [q9Coloring, q9EdgeColorFast, hi, hj]

lemma q9_edge_formula_nat {x y : Nat} (hx : x < 72) (hy : y < 72) :
    q9EdgeColorFast x y =
      (((x + 1) / 2) + ((y + 1) / 2) - (x % 2) * (y % 2)) % 36 := by
  have hxeq : x ≠ 72 := by omega
  have hyeq : y ≠ 72 := by omega
  simp only [q9EdgeColorFast, hxeq, hyeq, ↓reduceIte]
  have hxe : x % 2 = 0 ∨ x % 2 = 1 := by omega
  have hye : y % 2 = 0 ∨ y % 2 = 1 := by omega
  have hxrep : x = 2 * (x / 2) + x % 2 := by omega
  have hyrep : y = 2 * (y / 2) + y % 2 := by omega
  have hxyrep : x + y + 1 =
      2 * (x / 2 + y / 2) + (x % 2 + y % 2 + 1) := by omega
  rw [hxyrep]
  rcases hxe with hxe | hxe <;> rcases hye with hye | hye <;>
    simp [hxe, hye] <;> omega

lemma q9_infty_edge_formula_nat {x : Nat} :
    q9EdgeColorFast 72 x = x % 36 := by
  simp [q9EdgeColorFast]

lemma q9_edge_formula_zmod {x y : Nat} (hx : x < 72) (hy : y < 72) :
    ((q9EdgeColorFast x y : Nat) : ZMod 36) =
      (((x + 1) / 2 : Nat) : ZMod 36) +
        (((y + 1) / 2 : Nat) : ZMod 36) -
        ((x % 2 : Nat) : ZMod 36) * ((y % 2 : Nat) : ZMod 36) := by
  rw [q9_edge_formula_nat hx hy]
  have hsub : (x + 1) / 2 + (y + 1) / 2 ≥ (x % 2) * (y % 2) := by
    have hxe : x % 2 = 0 ∨ x % 2 = 1 := by omega
    have hye : y % 2 = 0 ∨ y % 2 = 1 := by omega
    have hxpos : x % 2 = 1 → 0 < x := by
      intro h
      have hne : x ≠ 0 := by
        intro hz
        subst x
        simp at h
      exact Nat.pos_of_ne_zero hne
    have hypos : y % 2 = 1 → 0 < y := by
      intro h
      have hne : y ≠ 0 := by
        intro hz
        subst y
        simp at h
      exact Nat.pos_of_ne_zero hne
    rcases hxe with hxe | hxe <;> rcases hye with hye | hye <;>
      simp [hxe, hye] <;> omega
  rw [ZMod.natCast_mod, Nat.cast_sub hsub]
  simp only [Nat.cast_add, Nat.cast_mul]

end Erdos811
