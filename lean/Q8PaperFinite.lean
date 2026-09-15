import Q8PaperCore

/-! The finite-vertex branch of the q=8 cyclic base, without a search oracle. -/

namespace Erdos811

def q8Residues (x : Fin 8 → Nat) (i : Fin 8) : Fin 4 :=
  ⟨x i % 4, Nat.mod_lt _ (by decide)⟩

lemma q8_nat_sum_cast {α : Type*} (l : List α) (f : α → Nat) :
    ((l.map f).sum : Int) = (l.map (fun a => (f a : Int))).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih]

lemma q8VertexSum_add (e f : Fin 8 → Int) :
    q8VertexSum (fun i => e i + f i) = q8VertexSum e + q8VertexSum f := by
  simp only [q8VertexSum]
  ring

lemma q8Parity_indicator (a : Fin 4) :
    ((a.val % 2 : Nat) : Int) =
      (if a = 1 then 1 else 0) + (if a = 3 then 1 else 0) := by
  fin_cases a <;> decide

lemma q8ParitySum_eq_counts (x : Fin 8 → Nat) :
    q8VertexSum (fun i => ((x i % 2 : Nat) : Int)) =
      (q8ResidueCount (q8Residues x) 1 : Int) +
        q8ResidueCount (q8Residues x) 3 := by
  have hp (i : Fin 8) : x i % 2 = (q8Residues x i).val % 2 := by
    dsimp [q8Residues]
    omega
  have he : (fun i => ((x i % 2 : Nat) : Int)) =
      (fun i => q8ResidueIndicator (q8Residues x) 1 i +
        q8ResidueIndicator (q8Residues x) 3 i) := by
    funext i
    rw [hp]
    exact q8Parity_indicator (q8Residues x i)
  rw [he, q8VertexSum_add, q8ResidueIndicator_sum, q8ResidueIndicator_sum]

lemma q8OddProducts_eq_choose (x : Fin 8 → Nat) :
    (q8Pairs.map (fun ij => (x ij.1 % 2) * (x ij.2 % 2))).sum =
      (q8ResidueCount (q8Residues x) 1 +
        q8ResidueCount (q8Residues x) 3).choose 2 := by
  have he (i : Fin 8) : ((x i % 2 : Nat) : Int) = 0 ∨
      ((x i % 2 : Nat) : Int) = 1 := by omega
  have hc :
      ((q8Pairs.map (fun ij => (x ij.1 % 2) * (x ij.2 % 2))).sum : Int) =
        q8PairProducts (fun i => ((x i % 2 : Nat) : Int)) := by
    rw [q8_nat_sum_cast]
    simp only [q8PairProducts, Nat.cast_mul]
  have h := q8PairProducts_eq_choose (fun i => ((x i % 2 : Nat) : Int)) he
  rw [q8ParitySum_eq_counts] at h
  rw [← Nat.cast_add, ← q8_cast_choose_two] at h
  exact_mod_cast hc.trans h

lemma q8Finite_choose_mod7 (x : Fin 8 → Nat)
    (hfin : ∀ i, x i < 56) (hnd : (q8FinitePairColors x).Nodup) :
    (q8ResidueCount (q8Residues x) 1 +
      q8ResidueCount (q8Residues x) 3).choose 2 % 7 = 0 := by
  have hb := q8FinitePairB_mod_zero_of_color_sum x hfin
    (q8FinitePairColors_sum x hnd)
  have hs := congrArg (fun n : Nat => n % 7) (q8PairB_sum_add_oddProducts x)
  rw [Nat.add_mod, hb, Nat.zero_add, Nat.mod_mod, Nat.mul_mod] at hs
  norm_num at hs
  rw [q8OddProducts_eq_choose] at hs
  exact hs

lemma q8FiniteOddWeight_eq_count (x : Fin 8 → Nat) (hfin : ∀ i, x i < 56) :
    q8OddPairWeight (q8Residues x) = (q8FiniteOddColorCount x : Int) := by
  unfold q8FiniteOddColorCount
  rw [q8_nat_sum_cast]
  simp only [q8FinitePairColors, List.map_map, Function.comp_def]
  unfold q8OddPairWeight
  apply congrArg List.sum
  apply List.map_congr_left
  intro ij hij
  have hp := q8FiniteEdgeParityFormula (x ij.1) (x ij.2) (hfin ij.1) (hfin ij.2)
  dsimp [q8Residues]
  rw [hp]
  split <;> simp_all

/-- Eight finite vertices cannot give 28 distinct colours. No injectivity
assumption or precomputed search result is needed. -/
theorem q8FinitePairColors_not_nodup (x : Fin 8 → Nat) (hfin : ∀ i, x i < 56) :
    ¬ (q8FinitePairColors x).Nodup := by
  intro hnd
  exact q8FinitePaperContradiction_of_mod7_and_distinct x hfin hnd
    (q8Residues x) (q8Finite_choose_mod7 x hfin hnd)
    (q8FiniteOddWeight_eq_count x hfin)

#print axioms q8FinitePairColors_not_nodup

end Erdos811
