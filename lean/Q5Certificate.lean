import FormalConjecturesUtil
import Erdos811Definitions

/-!
## A kernel-checkable q = 5 finite certificate

This is deliberately kept separate from the statement file.  The matrix is a
plain finite datum; the two `decide` blocks below check its balance and its
finite obstruction inside the Lean kernel.  No external axiom or
`native_decide` is used.
-/

namespace Erdos811

def q5Matrix : Matrix (Fin 21) (Fin 21) (Fin 10) := !![
  0,2,9,4,3,9,6,0,4,7,8,5,6,3,1,5,8,7,2,0,1;
  2,0,3,4,9,6,8,6,7,4,1,2,8,7,3,9,1,0,5,0,5;
  9,3,0,3,6,7,9,4,0,6,8,4,2,8,0,7,5,2,1,5,1;
  4,4,3,0,7,7,2,5,1,9,2,0,5,8,9,0,6,1,3,8,6;
  3,9,6,7,0,3,5,1,8,2,5,8,1,2,6,0,7,0,4,9,4;
  9,6,7,7,3,0,1,8,6,0,5,5,1,3,8,2,2,9,0,4,4;
  6,8,9,2,5,1,0,7,1,8,4,6,7,0,2,9,0,5,4,3,3;
  0,6,4,5,1,8,7,0,9,8,7,1,9,0,2,2,3,4,6,5,3;
  4,7,0,1,8,6,1,9,0,0,2,3,7,2,4,3,9,5,8,6,5;
  7,4,6,9,2,0,8,8,0,0,6,4,3,5,1,5,1,3,2,9,7;
  8,1,8,2,5,5,4,7,2,6,0,0,3,9,9,6,4,3,7,1,0;
  5,2,4,0,8,5,6,1,3,4,0,0,8,1,7,6,3,9,9,2,7;
  6,8,2,5,1,1,7,9,7,3,3,8,0,9,5,4,0,6,0,4,2;
  3,7,8,8,2,3,0,0,2,5,9,1,9,0,4,1,7,4,5,6,6;
  1,3,0,9,6,8,2,2,4,1,9,7,5,4,0,8,5,6,7,3,0;
  5,9,7,0,0,2,9,2,3,5,6,6,4,1,8,0,4,1,3,7,8;
  8,1,5,6,7,2,0,3,9,1,4,3,0,7,5,4,0,8,6,2,9;
  7,0,2,1,0,9,5,4,5,3,3,9,6,4,6,1,8,0,8,7,2;
  2,5,1,3,4,0,4,6,8,2,7,9,0,5,7,3,6,8,0,1,9;
  0,0,5,8,9,4,3,5,6,9,1,2,4,6,3,7,2,7,1,0,8;
  1,5,1,6,4,4,3,3,5,7,0,7,2,6,0,8,9,2,9,8,0]

def q5Coloring : CompleteEdgeColoring (Fin 21) (Fin 10) where
  color := q5Matrix
  color_symm v w := by
    apply Fin.ext
    decide +revert

theorem q5_balanced : q5Coloring.IsBalanced := by
  unfold CompleteEdgeColoring.IsBalanced CompleteEdgeColoring.colorDegree
  decide

def q5EdgeColors (a b c d e : Fin 21) : List (Fin 10) :=
  [q5Coloring.color a b, q5Coloring.color a c, q5Coloring.color a d,
   q5Coloring.color a e, q5Coloring.color b c, q5Coloring.color b d,
   q5Coloring.color b e, q5Coloring.color c d, q5Coloring.color c e,
   q5Coloring.color d e]

abbrev Q5Pair := Fin 21 × Fin 21
abbrev Q5Triple := Q5Pair × Fin 21
abbrev Q5Quad := Q5Triple × Fin 21
abbrev Q5Five := Q5Quad × Fin 21

def q5TupleColors (p : Q5Five) : List (Fin 10) :=
  let a := p.1.1.1.1
  let b := p.1.1.1.2
  let c := p.1.1.2
  let d := p.1.2
  let e := p.2
  q5EdgeColors a b c d e

def q5FiveListAt (a : Fin 21) : List Q5Five :=
  ((List.finRange 21).filter (fun b => decide (a < b))).flatMap (fun b =>
    ((List.finRange 21).filter (fun c => decide (b < c))).flatMap (fun c =>
      ((List.finRange 21).filter (fun d => decide (c < d))).flatMap (fun d =>
        ((List.finRange 21).filter (fun e => decide (d < e))).map
          (fun e => ((((a, b), c), d), e)))))

def q5BadListAt (a : Fin 21) : List Q5Five :=
  (q5FiveListAt a).filter (fun p => decide (q5TupleColors p).Nodup)

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem q5_bad_list_at0_nil : q5BadListAt 0 = [] := by decide +revert

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem q5_bad_list_at1_nil : q5BadListAt 1 = [] := by decide +revert

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem q5_bad_list_at2_nil : q5BadListAt 2 = [] := by decide +revert

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem q5_bad_list_at3_nil : q5BadListAt 3 = [] := by decide +revert

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem q5_bad_list_at4_nil : q5BadListAt 4 = [] := by decide +revert

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem q5_bad_list_at5_nil : q5BadListAt 5 = [] := by decide +revert

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem q5_bad_list_at6_nil : q5BadListAt 6 = [] := by decide +revert

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem q5_bad_list_at7_nil : q5BadListAt 7 = [] := by decide +revert

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem q5_bad_list_at8_nil : q5BadListAt 8 = [] := by decide +revert

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem q5_bad_list_at9_nil : q5BadListAt 9 = [] := by decide +revert

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem q5_bad_list_at10_nil : q5BadListAt 10 = [] := by decide +revert

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem q5_bad_list_at11_nil : q5BadListAt 11 = [] := by decide +revert

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem q5_bad_list_at12_nil : q5BadListAt 12 = [] := by decide +revert

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem q5_bad_list_at13_nil : q5BadListAt 13 = [] := by decide +revert

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem q5_bad_list_at14_nil : q5BadListAt 14 = [] := by decide +revert

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem q5_bad_list_at15_nil : q5BadListAt 15 = [] := by decide +revert

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem q5_bad_list_at16_nil : q5BadListAt 16 = [] := by decide +revert

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem q5_bad_list_at17_nil : q5BadListAt 17 = [] := by decide +revert

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem q5_bad_list_at18_nil : q5BadListAt 18 = [] := by decide +revert

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem q5_bad_list_at19_nil : q5BadListAt 19 = [] := by decide +revert

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem q5_bad_list_at20_nil : q5BadListAt 20 = [] := by decide +revert

theorem q5_bad_list_at_nil (a : Fin 21) : q5BadListAt a = [] := by
  fin_cases a <;>
    simp [q5_bad_list_at0_nil, q5_bad_list_at1_nil, q5_bad_list_at2_nil,
      q5_bad_list_at3_nil, q5_bad_list_at4_nil, q5_bad_list_at5_nil,
      q5_bad_list_at6_nil, q5_bad_list_at7_nil, q5_bad_list_at8_nil,
      q5_bad_list_at9_nil, q5_bad_list_at10_nil, q5_bad_list_at11_nil,
      q5_bad_list_at12_nil, q5_bad_list_at13_nil, q5_bad_list_at14_nil,
      q5_bad_list_at15_nil, q5_bad_list_at16_nil, q5_bad_list_at17_nil,
      q5_bad_list_at18_nil, q5_bad_list_at19_nil, q5_bad_list_at20_nil]

theorem q5_no_rainbow_sorted :
    ∀ a b c d e : Fin 21, a < b → b < c → c < d → d < e →
      ¬ (q5EdgeColors a b c d e).Nodup := by
  intro a b c d e hab hbc hcd hde hrainbow
  have hp : ((((a, b), c), d), e) ∈ q5FiveListAt a := by
    simp [q5FiveListAt, hab, hbc, hcd, hde]
  have hm : ((((a, b), c), d), e) ∈ q5BadListAt a :=
    List.mem_filter.mpr ⟨hp, by
      have hcolors : (q5TupleColors ((((a, b), c), d), e)).Nodup := by
        simpa [q5TupleColors] using hrainbow
      simp [hcolors]⟩
  rw [q5_bad_list_at_nil a] at hm
  exact List.not_mem_nil hm

set_option maxHeartbeats 0 in
theorem q5_no_rainbow :
    ¬ HasRainbowCopy (SimpleGraph.completeGraph (Fin 5)) q5Coloring := by
  classical
  rintro ⟨f, hf⟩
  let s : Finset (Fin 21) := Finset.univ.image f
  have hs_card : s.card = 5 := by
    dsimp [s]
    apply (Finset.card_image_iff).2
    intro x hx y hy hxy
    exact f.injective hxy
  let g : Fin 5 ↪ Fin 21 := (s.orderEmbOfFin hs_card).toEmbedding
  have hg_mem (i : Fin 5) : g i ∈ s := by
    exact Finset.orderEmbOfFin_mem s hs_card i
  have hmem_image (i : Fin 5) : g i ∈ Finset.univ.image f := by
    simpa [s] using hg_mem i
  let p : Fin 5 → Fin 5 := fun i =>
    Classical.choose (Finset.mem_image.mp (hmem_image i))
  have hp_spec (i : Fin 5) : f (p i) = g i := by
    dsimp [p]
    exact (Classical.choose_spec (Finset.mem_image.mp (hmem_image i))).2
  let pEmb : Fin 5 ↪ Fin 5 := {
    toFun := p
    inj' := by
      intro i j hij
      apply g.injective
      rw [← hp_spec i, ← hp_spec j, hij]
  }
  have hdiff {a b c d : Fin 5}
      (hab : a ≠ b) (hcd : c ≠ d)
      (hnot : ¬ SameUndirectedEdge a b c d) :
      q5Coloring.color (g a) (g b) ≠ q5Coloring.color (g c) (g d) := by
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
  have hcolors : (q5EdgeColors (g 0) (g 1) (g 2) (g 3) (g 4)).Nodup := by
    simp only [q5EdgeColors, List.nodup_cons, List.not_mem_nil, List.mem_cons,
      not_or, not_false_eq_true, true_and]
    repeat' constructor
    all_goals apply hdiff <;> simp [SameUndirectedEdge]
  exact q5_no_rainbow_sorted (g 0) (g 1) (g 2) (g 3) (g 4)
    ((s.orderEmbOfFin hs_card).lt_iff_lt.mpr (by decide))
    ((s.orderEmbOfFin hs_card).lt_iff_lt.mpr (by decide))
    ((s.orderEmbOfFin hs_card).lt_iff_lt.mpr (by decide))
    ((s.orderEmbOfFin hs_card).lt_iff_lt.mpr (by decide)) hcolors

theorem q5_finite_base :
    HasBalancedCounterexampleAt (SimpleGraph.completeGraph (Fin 5)) 21 := by
  have hEdge : edgeCount (SimpleGraph.completeGraph (Fin 5)) = 10 := by
    rw [edgeCount_completeGraph_fin]
    decide
  unfold HasBalancedCounterexampleAt
  rw [hEdge]
  refine ⟨by norm_num, q5Coloring, q5_balanced, q5_no_rainbow⟩

#print axioms q5_finite_base

end Erdos811
