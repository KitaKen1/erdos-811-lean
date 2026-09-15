import CyclicBases
import Q8PaperFinite

/-! Graph-level bridge from the numerical q=8 paper proof to the shared FC colouring. -/

namespace Erdos811

lemma q8PaperColor_eq (i j : Fin 57) :
    (q8Coloring.color i j).val = q8PaperColorNat i.val j.val := by
  by_cases hi : i.val = 56 <;> by_cases hj : j.val = 56 <;>
    simp [q8Coloring, q8PaperColorNat, hi, hj]

lemma q8Pairs_same_undirected_eq : ∀ p q : Fin 8 × Fin 8,
    p ∈ q8Pairs → q ∈ q8Pairs → SameUndirectedEdge p.1 p.2 q.1 q.2 → p = q := by
  intro p q hp hq hs
  rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Prod.ext h1 h2
  · have hpord := q8Pairs_ordered p hp
    have hqord := q8Pairs_ordered q hq
    exfalso
    omega


lemma q8FinitePairColors_nodup (x : Fin 8 → Nat)
    (hf : ∀ ⦃a b c d : Fin 8⦄,
      (SimpleGraph.completeGraph (Fin 8)).Adj a b →
      (SimpleGraph.completeGraph (Fin 8)).Adj c d →
      ¬ SameUndirectedEdge a b c d →
      q8PaperColorNat (x a) (x b) ≠ q8PaperColorNat (x c) (x d)) :
    (q8FinitePairColors x).Nodup := by
  apply (List.nodup_iff_pairwise_ne).2
  apply (List.pairwise_map).2
  apply list_pairwise_of_mem_ne q8Pairs_nodup
  intro p hp q hq hpq hcol
  have hpord := q8Pairs_ordered p hp
  have hqord := q8Pairs_ordered q hq
  have hsame : ¬ SameUndirectedEdge p.1 p.2 q.1 q.2 := by
    intro hs
    exact hpq (q8Pairs_same_undirected_eq p q hp hq hs)
  have hadj1 : (SimpleGraph.completeGraph (Fin 8)).Adj p.1 p.2 := by
    simpa using hpord.ne
  have hadj2 : (SimpleGraph.completeGraph (Fin 8)).Adj q.1 q.2 := by
    simpa using hqord.ne
  have hne := hf hadj1 hadj2 hsame
  exact hne (congrArg Fin.val hcol)

/-- The actual cyclic colouring has no rainbow K8 whose vertices all avoid ∞. -/
theorem q8_no_finite_rainbow_paper (f : Fin 8 ↪ Fin 57)
    (hfin : ∀ i, (f i).val < 56) :
    ¬ (∀ ⦃a b c d : Fin 8⦄,
      (SimpleGraph.completeGraph (Fin 8)).Adj a b →
      (SimpleGraph.completeGraph (Fin 8)).Adj c d →
      ¬ SameUndirectedEdge a b c d →
      q8Coloring.color (f a) (f b) ≠ q8Coloring.color (f c) (f d)) := by
  intro hf
  apply q8FinitePairColors_not_nodup (fun i => (f i).val) hfin
  apply q8FinitePairColors_nodup
  intro a b c d hab hcd hnot heq
  apply hf hab hcd hnot
  apply Fin.ext
  simpa only [q8PaperColor_eq] using heq

/-- This is a reduction to the ∞ branch, not a proof of the entire q=8 base. -/
theorem q8Rainbow_must_contain_infinity (f : Fin 8 ↪ Fin 57)
    (hf : ∀ ⦃a b c d : Fin 8⦄,
      (SimpleGraph.completeGraph (Fin 8)).Adj a b →
      (SimpleGraph.completeGraph (Fin 8)).Adj c d →
      ¬ SameUndirectedEdge a b c d →
      q8Coloring.color (f a) (f b) ≠ q8Coloring.color (f c) (f d)) :
    ∃ i, (f i).val = 56 := by
  by_contra h
  have hfin (i : Fin 8) : (f i).val < 56 := by
    have hi : (f i).val ≠ 56 := fun hi => h ⟨i, hi⟩
    have hlt := (f i).isLt
    omega
  exact q8_no_finite_rainbow_paper f hfin hf

#print axioms q8_no_finite_rainbow_paper
#print axioms q8Rainbow_must_contain_infinity

end Erdos811
