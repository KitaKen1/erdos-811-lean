import Q9ParityFormulas

/-! The finite edge index used by the q=9 parity/SAT bridge. -/

namespace Erdos811

def q9EdgePairs : Finset (Fin 9 × Fin 9) :=
  (Finset.univ.product Finset.univ).filter (fun p => p.1 < p.2)

lemma q9EdgePairs_card : q9EdgePairs.card = 36 := by
  decide

lemma q9Rainbow_edge_color_injective
    {g : Fin 9 ↪ Fin 73}
    (hf : ∀ ⦃a b c d : Fin 9⦄,
      (SimpleGraph.completeGraph (Fin 9)).Adj a b →
      (SimpleGraph.completeGraph (Fin 9)).Adj c d →
      ¬ SameUndirectedEdge (g a) (g b) (g c) (g d) →
      q9Coloring.color (g a) (g b) ≠ q9Coloring.color (g c) (g d)) :
    Function.Injective (fun p : {p // p ∈ q9EdgePairs} =>
      q9Coloring.color (g p.1.1) (g p.1.2)) := by
  intro p q heq
  by_contra hpq
  have hp_mem := Finset.mem_filter.mp p.2
  have hq_mem := Finset.mem_filter.mp q.2
  have hpne : p.1.1 ≠ p.1.2 := by exact ne_of_lt hp_mem.2
  have hqne : q.1.1 ≠ q.1.2 := by exact ne_of_lt hq_mem.2
  have hpAdj : (SimpleGraph.completeGraph (Fin 9)).Adj p.1.1 p.1.2 := by
    simpa [SimpleGraph.completeGraph] using hpne
  have hqAdj : (SimpleGraph.completeGraph (Fin 9)).Adj q.1.1 q.1.2 := by
    simpa [SimpleGraph.completeGraph] using hqne
  have hsame : ¬ SameUndirectedEdge (g p.1.1) (g p.1.2)
      (g q.1.1) (g q.1.2) := by
    intro hs
    rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · apply hpq
      apply Subtype.ext
      apply Prod.ext
      · exact g.injective h1
      · exact g.injective h2
    · have h1' : p.1.1 = q.1.2 := g.injective h1
      have h2' : p.1.2 = q.1.1 := g.injective h2
      have hp_lt := hp_mem.2
      have hq_lt := hq_mem.2
      omega
  exact (hf hpAdj hqAdj hsame) heq

lemma q9Rainbow_edge_color_sum
    {g : Fin 9 ↪ Fin 73}
    (hf : ∀ ⦃a b c d : Fin 9⦄,
      (SimpleGraph.completeGraph (Fin 9)).Adj a b →
      (SimpleGraph.completeGraph (Fin 9)).Adj c d →
      ¬ SameUndirectedEdge (g a) (g b) (g c) (g d) →
      q9Coloring.color (g a) (g b) ≠ q9Coloring.color (g c) (g d)) :
    ∑ p : {p // p ∈ q9EdgePairs},
      (q9Coloring.color (g p.1.1) (g p.1.2)).val = 630 := by
  apply q9_sum_image_fin36
    (fun p : {p // p ∈ q9EdgePairs} =>
      q9Coloring.color (g p.1.1) (g p.1.2))
  · exact q9Rainbow_edge_color_injective hf
  · exact q9EdgePairs_card

end Erdos811
