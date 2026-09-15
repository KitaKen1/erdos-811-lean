import FormalConjecturesUtil
import Erdos811Definitions

/-!
## The Clemen--Wagner q = 4 finite certificate

The matrix is the K₁₃ certificate printed in Figure 1 of Clemen--Wagner,
"Balanced edge-colorings avoiding rainbow cliques of size four"
(https://doi.org/10.37236/11965).  The paper
labels the six off-diagonal colours 1,...,6; the certificate below shifts
them to `Fin 6 = {0,...,5}` and puts an arbitrary zero on the diagonal.
-/

namespace Erdos811

def q4Matrix : Matrix (Fin 13) (Fin 13) (Fin 6) := !![
  0,1,4,3,0,2,2,5,3,1,5,4,0;
  1,0,2,5,4,5,3,0,2,0,3,4,1;
  4,2,0,4,3,1,5,2,0,5,1,0,3;
  3,5,4,0,1,3,4,1,0,2,2,0,5;
  0,4,3,1,0,2,0,5,1,4,3,5,2;
  2,5,1,3,2,0,0,3,4,5,4,1,0;
  2,3,5,4,0,0,0,1,4,3,1,5,2;
  5,0,2,1,5,3,1,0,2,4,0,3,4;
  3,2,0,0,1,4,4,2,0,3,5,1,5;
  1,0,5,2,4,5,3,4,3,0,0,2,1;
  5,3,1,2,3,4,1,0,5,0,0,2,4;
  4,4,0,0,5,1,5,3,1,2,2,0,3;
  0,1,3,5,2,0,2,4,5,1,4,3,0]

def q4Coloring : CompleteEdgeColoring (Fin 13) (Fin 6) where
  color := q4Matrix
  color_symm v w := by
    apply Fin.ext
    decide +revert

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
theorem q4_balanced : q4Coloring.IsBalanced := by
  unfold CompleteEdgeColoring.IsBalanced CompleteEdgeColoring.colorDegree
  decide

def q4EdgeColors (a b c d : Fin 13) : List (Fin 6) :=
  [q4Coloring.color a b, q4Coloring.color a c, q4Coloring.color a d,
   q4Coloring.color b c, q4Coloring.color b d, q4Coloring.color c d]

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
theorem q4_no_rainbow_sorted :
    ∀ a b c d : Fin 13, a < b → b < c → c < d →
      ¬ (q4EdgeColors a b c d).Nodup := by
  decide +revert

set_option maxHeartbeats 0 in
theorem q4_no_rainbow :
    ¬ HasRainbowCopy (SimpleGraph.completeGraph (Fin 4)) q4Coloring := by
  classical
  rintro ⟨f, hf⟩
  let s : Finset (Fin 13) := Finset.univ.image f
  have hs_card : s.card = 4 := by
    dsimp [s]
    apply (Finset.card_image_iff).2
    intro x hx y hy hxy
    exact f.injective hxy
  let g : Fin 4 ↪ Fin 13 := (s.orderEmbOfFin hs_card).toEmbedding
  have hg_mem (i : Fin 4) : g i ∈ s := by
    exact Finset.orderEmbOfFin_mem s hs_card i
  have hmem_image (i : Fin 4) : g i ∈ Finset.univ.image f := by
    simpa [s] using hg_mem i
  let p : Fin 4 → Fin 4 := fun i =>
    Classical.choose (Finset.mem_image.mp (hmem_image i))
  have hp_spec (i : Fin 4) : f (p i) = g i := by
    dsimp [p]
    exact (Classical.choose_spec (Finset.mem_image.mp (hmem_image i))).2
  let pEmb : Fin 4 ↪ Fin 4 := {
    toFun := p
    inj' := by
      intro i j hij
      apply g.injective
      rw [← hp_spec i, ← hp_spec j, hij]
  }
  have hdiff {a b c d : Fin 4}
      (hab : a ≠ b) (hcd : c ≠ d)
      (hnot : ¬ SameUndirectedEdge a b c d) :
      q4Coloring.color (g a) (g b) ≠ q4Coloring.color (g c) (g d) := by
    rw [← hp_spec a, ← hp_spec b, ← hp_spec c, ← hp_spec d]
    apply hf
    · intro hEq
      exact hab (pEmb.injective hEq)
    · intro hEq
      exact hcd (pEmb.injective hEq)
    · intro hsame
      apply hnot
      rcases hsame with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨pEmb.injective h1, pEmb.injective h2⟩
      · exact Or.inr ⟨pEmb.injective h1, pEmb.injective h2⟩
  have hcolors : (q4EdgeColors (g 0) (g 1) (g 2) (g 3)).Nodup := by
    simp only [q4EdgeColors, List.nodup_cons, List.not_mem_nil, List.mem_cons,
      not_or, not_false_eq_true, true_and]
    repeat' constructor
    all_goals apply hdiff <;> simp [SameUndirectedEdge]
  exact q4_no_rainbow_sorted (g 0) (g 1) (g 2) (g 3)
    ((s.orderEmbOfFin hs_card).lt_iff_lt.mpr (by decide))
    ((s.orderEmbOfFin hs_card).lt_iff_lt.mpr (by decide))
    ((s.orderEmbOfFin hs_card).lt_iff_lt.mpr (by decide)) hcolors

theorem q4_finite_base :
    HasBalancedCounterexampleAt (SimpleGraph.completeGraph (Fin 4)) 13 := by
  have hEdge : edgeCount (SimpleGraph.completeGraph (Fin 4)) = 6 := by
    rw [edgeCount_completeGraph_fin]
    decide
  unfold HasBalancedCounterexampleAt
  rw [hEdge]
  refine ⟨by norm_num, q4Coloring, q4_balanced, q4_no_rainbow⟩

#print axioms q4_finite_base

end Erdos811
