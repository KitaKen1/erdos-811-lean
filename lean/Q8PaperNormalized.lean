import Q8PaperInfinity
import Mathlib.Data.List.Nodup
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.SplitIfs

/-! The normalized infinity type has no rainbow lift.

The support classification up to translation is a separate obligation.
This module derives the three congruences from distinct edge colours,
rather than accepting those congruences as assumptions.
-/

namespace Erdos811

def q8NormalizedVertices (t : Fin 7 → Nat) : Fin 8 → Nat :=
  ![2 + 14 * t 0, 4 + 14 * t 1, 7 + 14 * t 2, 9 + 14 * t 3,
    11 + 14 * t 4, 12 + 14 * t 5, 13 + 14 * t 6, 56]

def q8Row2Pairs : Fin 4 → Fin 8 × Fin 8 := ![(0,7), (1,6), (2,4), (3,7)]
def q8Row3Pairs : Fin 4 → Fin 8 × Fin 8 := ![(0,1), (2,5), (2,6), (3,4)]
def q8Row5Pairs : Fin 4 → Fin 8 × Fin 8 := ![(0,2), (4,5), (4,6), (5,7)]

def q8Row2Lifts (t : Fin 7 → Nat) : Fin 4 → Nat :=
  ![2 * t 0, 1 + t 1 + t 6, 1 + t 2 + t 4, 1 + 2 * t 3]
def q8Row3Lifts (t : Fin 7 → Nat) : Fin 4 → Nat :=
  ![t 0 + t 1, 1 + t 2 + t 5, 1 + t 2 + t 6, 1 + t 3 + t 4]
def q8Row5Lifts (t : Fin 7 → Nat) : Fin 4 → Nat :=
  ![t 0 + t 2, 1 + t 4 + t 5, 1 + t 4 + t 6, 1 + 2 * t 5]

lemma q8PairColor_injective_of_nodup (x : Fin 8 → Nat)
    (hnd : (q8FinitePairColors x).Nodup)
    {p q : Fin 8 × Fin 8} (hp : p ∈ q8Pairs) (hq : q ∈ q8Pairs)
    (hc : q8PaperColorNat (x p.1) (x p.2) = q8PaperColorNat (x q.1) (x q.2)) :
    p = q := by
  exact List.inj_on_of_nodup_map hnd hp hq (Fin.ext hc)

/-- Four distinct residues modulo 4 use all residues, so their sum is 2 modulo 4. -/
lemma q8Four_lifts_sum (a : Fin 4 → Nat)
    (hinj : Function.Injective (fun i => a i % 4)) :
    (a 0 + a 1 + a 2 + a 3) % 4 = 2 := by
  let f : Fin 4 → Fin 4 := fun i => ⟨a i % 4, Nat.mod_lt _ (by decide)⟩
  have hf : Function.Injective f := by
    intro i j h
    exact hinj (congrArg Fin.val h)
  let e : Fin 4 ≃ Fin 4 := Equiv.ofBijective f ⟨hf, Finite.surjective_of_injective hf⟩
  have hs : (∑ i : Fin 4, a i % 4) = 6 := by
    calc
      _ = ∑ i : Fin 4, (e i).val := rfl
      _ = ∑ i : Fin 4, i.val := e.sum_comp (fun i => i.val)
      _ = 6 := by decide
  simp [Fin.sum_univ_succ] at hs
  omega

lemma q8Four_edges_sum (x : Fin 8 → Nat) (hnd : (q8FinitePairColors x).Nodup)
    (p : Fin 4 → Fin 8 × Fin 8) (hp : ∀ i, p i ∈ q8Pairs)
    (hpi : Function.Injective p) (a : Fin 4 → Nat) (c : Nat)
    (hc : ∀ i, q8PaperColorNat (x (p i).1) (x (p i).2) = c + 7 * (a i % 4)) :
    (a 0 + a 1 + a 2 + a 3) % 4 = 2 := by
  apply q8Four_lifts_sum
  intro i j hij
  change a i % 4 = a j % 4 at hij
  apply hpi
  apply q8PairColor_injective_of_nodup x hnd (hp i) (hp j)
  rw [hc i, hc j, hij]

lemma q8Lift_ne_infinity (r u : Nat) (hr0 : 0 < r) (hr14 : r < 14) :
    r + 14 * u ≠ 56 := by omega

lemma q8Row2_colors (t : Fin 7 → Nat) (i : Fin 4) :
    q8PaperColorNat (q8NormalizedVertices t (q8Row2Pairs i).1)
      (q8NormalizedVertices t (q8Row2Pairs i).2) = 2 + 7 * (q8Row2Lifts t i % 4) := by
  fin_cases i <;>
    simp [q8NormalizedVertices, q8Row2Pairs, q8Row2Lifts, q8PaperColorNat,
      q8Lift_ne_infinity] <;> omega

lemma q8Row3_colors (t : Fin 7 → Nat) (i : Fin 4) :
    q8PaperColorNat (q8NormalizedVertices t (q8Row3Pairs i).1)
      (q8NormalizedVertices t (q8Row3Pairs i).2) = 3 + 7 * (q8Row3Lifts t i % 4) := by
  fin_cases i <;>
    simp [q8NormalizedVertices, q8Row3Pairs, q8Row3Lifts, q8PaperColorNat,
      q8Lift_ne_infinity] <;> omega

lemma q8Row5_colors (t : Fin 7 → Nat) (i : Fin 4) :
    q8PaperColorNat (q8NormalizedVertices t (q8Row5Pairs i).1)
      (q8NormalizedVertices t (q8Row5Pairs i).2) = 5 + 7 * (q8Row5Lifts t i % 4) := by
  fin_cases i <;>
    simp [q8NormalizedVertices, q8Row5Pairs, q8Row5Lifts, q8PaperColorNat,
      q8Lift_ne_infinity] <;> omega

lemma q8Normalized_row2 (t : Fin 7 → Nat)
    (hnd : (q8FinitePairColors (q8NormalizedVertices t)).Nodup) :
    (2 * t 0 + t 1 + t 2 + 2 * t 3 + t 4 + t 6) % 4 = 3 := by
  have h := q8Four_edges_sum (q8NormalizedVertices t) hnd q8Row2Pairs
    (by decide) (by decide) (q8Row2Lifts t) 2 (q8Row2_colors t)
  simp [q8Row2Lifts] at h
  omega

lemma q8Normalized_row3 (t : Fin 7 → Nat)
    (hnd : (q8FinitePairColors (q8NormalizedVertices t)).Nodup) :
    (t 0 + t 1 + 2 * t 2 + t 3 + t 4 + t 5 + t 6) % 4 = 3 := by
  have h := q8Four_edges_sum (q8NormalizedVertices t) hnd q8Row3Pairs
    (by decide) (by decide) (q8Row3Lifts t) 3 (q8Row3_colors t)
  simp [q8Row3Lifts] at h
  omega

lemma q8Normalized_row5 (t : Fin 7 → Nat)
    (hnd : (q8FinitePairColors (q8NormalizedVertices t)).Nodup) :
    (t 0 + t 2 + 2 * t 4 + 3 * t 5 + t 6) % 4 = 3 := by
  have h := q8Four_edges_sum (q8NormalizedVertices t) hnd q8Row5Pairs
    (by decide) (by decide) (q8Row5Lifts t) 5 (q8Row5_colors t)
  simp [q8Row5Lifts] at h
  omega

lemma q8PaperColorNat_comm (x y : Nat) : q8PaperColorNat x y = q8PaperColorNat y x := by
  by_cases hx : x = 56 <;> by_cases hy : y = 56 <;>
    simp [q8PaperColorNat, hx, hy, Nat.add_comm]

/-- No lift of the normalized residue support is rainbow. Only the support
normalization, not extra congruence hypotheses, is required. -/
theorem q8NormalizedInfinity_not_nodup (t : Fin 7 → Nat) :
    ¬ (q8FinitePairColors (q8NormalizedVertices t)).Nodup := by
  intro hnd
  have hc := q8NormalizedInfinity_collision t (q8Normalized_row2 t hnd)
    (q8Normalized_row3 t hnd) (q8Normalized_row5 t hnd)
  have hcol :
      q8PaperColorNat (q8NormalizedVertices t 3) (q8NormalizedVertices t 6) =
        q8PaperColorNat (q8NormalizedVertices t 1) (q8NormalizedVertices t 7) := by
    change q8PaperColorNat (9 + 14 * t 3) (13 + 14 * t 6) =
      q8PaperColorNat (4 + 14 * t 1) 56
    rw [q8PaperColorNat_comm (4 + 14 * t 1) 56]
    exact hc
  have he := q8PairColor_injective_of_nodup (q8NormalizedVertices t) hnd
    (p := (3,6)) (q := (1,7)) (by decide) (by decide) hcol
  have hn : (3,6) ≠ ((1,7) : Fin 8 × Fin 8) := by decide
  exact hn he

#print axioms q8NormalizedInfinity_not_nodup

end Erdos811
