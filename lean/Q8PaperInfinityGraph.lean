import Q8PaperInfinityNormalization
import Q8Paper

/-! Graph-level wrapper for the normalized infinity branch.

The arithmetic/finite-support normalization stays in the lightweight target
`Q8PaperInfinityNormalization`; this file only performs the final permutation
of an arbitrary `K₈` embedding so that the infinity vertex is the last index.
-/

namespace Erdos811

theorem q8_no_infinity_rainbow_paper (f : Fin 8 ↪ Fin 57)
    (hf : ∀ ⦃a b c d : Fin 8⦄,
      (SimpleGraph.completeGraph (Fin 8)).Adj a b →
      (SimpleGraph.completeGraph (Fin 8)).Adj c d →
      ¬ SameUndirectedEdge a b c d →
      q8Coloring.color (f a) (f b) ≠ q8Coloring.color (f c) (f d)) :
    False := by
  obtain ⟨i0, hi0⟩ := q8Rainbow_must_contain_infinity f hf
  let sw : Equiv.Perm (Fin 8) := Equiv.swap i0 (Fin.last 7)
  let g : Fin 8 ↪ Fin 57 :=
    { toFun := fun i => f (sw i)
      inj' := by
        intro i j hij
        apply sw.injective
        apply f.injective
        exact hij }
  have hglast : (g (Fin.last 7)).val = 56 := by
    simpa [g, sw] using hi0
  let x : Fin 7 → Nat := fun i => (g i.castSucc).val
  have hfin : ∀ i, x i < 56 := by
    intro i
    change (g i.castSucc).val < 56
    have hne : g i.castSucc ≠ g (Fin.last 7) := by
      intro heq
      have hij : i.castSucc = Fin.last 7 := g.injective heq
      exact (Fin.castSucc_ne_last i) hij
    have hv : (g i.castSucc).val < 57 := (g i.castSucc).isLt
    have hneq : (g i.castSucc).val ≠ 56 := by
      intro hv56
      apply hne
      exact Fin.ext (hv56.trans hglast.symm)
    omega
  have hxi : Function.Injective x := by
    intro i j hij
    apply (Fin.castSucc_injective 7)
    apply g.injective
    apply Fin.ext
    simpa only [x] using hij
  have hxg (i : Fin 8) :
      q8WithInfinity x i = (g i).val := by
    cases i using Fin.lastCases with
    | last =>
        rw [q8WithInfinity_last]
        exact hglast.symm
    | cast j =>
        rw [q8WithInfinity_castSucc]
  have hfg : ∀ ⦃a b c d : Fin 8⦄,
      (SimpleGraph.completeGraph (Fin 8)).Adj a b →
      (SimpleGraph.completeGraph (Fin 8)).Adj c d →
      ¬ SameUndirectedEdge a b c d →
      q8Coloring.color (g a) (g b) ≠ q8Coloring.color (g c) (g d) := by
    intro a b c d hab hcd hnot
    have hab' : (SimpleGraph.completeGraph (Fin 8)).Adj (sw a) (sw b) := by
      simpa using sw.injective.ne (by simpa using hab)
    have hcd' : (SimpleGraph.completeGraph (Fin 8)).Adj (sw c) (sw d) := by
      simpa using sw.injective.ne (by simpa using hcd)
    have hnot' : ¬ SameUndirectedEdge (sw a) (sw b) (sw c) (sw d) := by
      intro hs
      apply hnot
      rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨sw.injective h1, sw.injective h2⟩
      · exact Or.inr ⟨sw.injective h1, sw.injective h2⟩
    change q8Coloring.color (f (sw a)) (f (sw b)) ≠
      q8Coloring.color (f (sw c)) (f (sw d))
    exact hf hab' hcd' hnot'
  have hnd : (q8FinitePairColors (q8WithInfinity x)).Nodup := by
    apply q8FinitePairColors_nodup
    intro a b c d hab hcd hnot heq
    apply hfg hab hcd hnot
    apply Fin.ext
    simpa only [q8PaperColor_eq, hxg] using heq
  exact q8Normalized_nodup_transfer x (0 : Fin 7) hfin hxi hnd

theorem q8_no_rainbow_paper :
    ¬ HasRainbowCopy (SimpleGraph.completeGraph (Fin 8)) q8Coloring := by
  rintro ⟨f, hf⟩
  exact q8_no_infinity_rainbow_paper f hf

/-- The explicit balanced q=8 finite base using the paper certificate. -/
theorem q8_finite_base_paper :
    HasBalancedCounterexampleAt (SimpleGraph.completeGraph (Fin 8)) 57 := by
  have hEdge : edgeCount (SimpleGraph.completeGraph (Fin 8)) = 28 := by
    rw [edgeCount_completeGraph_fin]
    decide
  unfold HasBalancedCounterexampleAt
  rw [hEdge]
  exact ⟨by norm_num, q8Coloring, q8_balanced, q8_no_rainbow_paper⟩

#print axioms q8_no_infinity_rainbow_paper
#print axioms q8_no_rainbow_paper
#print axioms q8_finite_base_paper

end Erdos811
