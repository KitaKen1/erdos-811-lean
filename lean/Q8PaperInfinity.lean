import Q8PaperCore

/-! Conditional arithmetic for the ∞ branch of the q=8 paper proof.

The residue-support classification and the derivation of these three row
equations from a rainbow copy are NOT supplied by this module. Once those
bridges are proved, the collision below needs no enumeration of the lifts.
-/

namespace Erdos811

/-- The sum of rows 2, 3 and 5 for the normalized support
`[2,4,7,9,11,12,13]` forces the collision congruence. -/
lemma q8Infinity_three_rows (t : Fin 7 → Nat)
    (h2 : (2 * t 0 + t 1 + t 2 + 2 * t 3 + t 4 + t 6) % 4 = 3)
    (h3 : (t 0 + t 1 + 2 * t 2 + t 3 + t 4 + t 5 + t 6) % 4 = 3)
    (h5 : (t 0 + t 2 + 2 * t 4 + 3 * t 5 + t 6) % 4 = 3) :
    (t 3 + t 6 + 2 * t 1) % 4 = 3 := by
  omega

/-- The finite edge between residues 9 and 13 has the same colour as
the infinity edge incident to residue 4. -/
lemma q8Infinity_collision_of_congruence (u v w : Nat)
    (h : (u + v + 2 * w) % 4 = 3) :
    q8PaperColorNat (9 + 14 * u) (13 + 14 * v) =
      q8PaperColorNat 56 (4 + 14 * w) := by
  have hu : 9 + 14 * u ≠ 56 := by omega
  have hv : 13 + 14 * v ≠ 56 := by omega
  simp only [q8PaperColorNat, hu, hv, ite_false, ite_true]
  omega

theorem q8NormalizedInfinity_collision (t : Fin 7 → Nat)
    (h2 : (2 * t 0 + t 1 + t 2 + 2 * t 3 + t 4 + t 6) % 4 = 3)
    (h3 : (t 0 + t 1 + 2 * t 2 + t 3 + t 4 + t 5 + t 6) % 4 = 3)
    (h5 : (t 0 + t 2 + 2 * t 4 + 3 * t 5 + t 6) % 4 = 3) :
    q8PaperColorNat (9 + 14 * t 3) (13 + 14 * t 6) =
      q8PaperColorNat 56 (4 + 14 * t 1) := by
  exact q8Infinity_collision_of_congruence (t 3) (t 6) (t 1)
    (q8Infinity_three_rows t h2 h3 h5)

#print axioms q8NormalizedInfinity_collision

end Erdos811
