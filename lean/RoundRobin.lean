import Erdos811Definitions

/-!
# The standard odd-order 1-factorization

For an odd integer `m`, the usual round-robin factorization of `K_(m+1)`
uses the vertices `Z_m ∪ {∞}` and the colors `Z_m`:

* `c(i,j) = i + j (mod m)` for two finite vertices;
* `c(∞,i) = 2 i (mod m)`.

The definition below is deliberately independent of the later rainbow-free
certificates.  It gives a common, kernel-checkable object for the q = 6, 7,
10, and 11 literature cases.  The finite balance checks are kept as explicit
theorems, so a failed certificate cannot be hidden in a final dispatcher.
-/

namespace Erdos811

def roundRobinColoring (m : ℕ) (hm : 0 < m) :
    CompleteEdgeColoring (Fin (m + 1)) (Fin m) where
  color p q :=
    if hp : p.val = m then
      ⟨(2 * q.val) % m, Nat.mod_lt _ hm⟩
    else if hq : q.val = m then
      ⟨(2 * p.val) % m, Nat.mod_lt _ hm⟩
    else
      ⟨(p.val + q.val) % m, Nat.mod_lt _ hm⟩
  color_symm p q := by
    by_cases hp : p.val = m
    · by_cases hq : q.val = m
      · simp [hp, hq]
      · simp [hp, hq]
    · by_cases hq : q.val = m
      · simp [hp, hq]
      · simp [hp, hq, Nat.add_comm]

def q6RoundRobinColoring :
    CompleteEdgeColoring (Fin 16) (Fin 15) :=
  roundRobinColoring 15 (by norm_num)

def q7RoundRobinColoring :
    CompleteEdgeColoring (Fin 22) (Fin 21) :=
  roundRobinColoring 21 (by norm_num)

def q10RoundRobinColoring :
    CompleteEdgeColoring (Fin 46) (Fin 45) :=
  roundRobinColoring 45 (by norm_num)

def q11RoundRobinColoring :
    CompleteEdgeColoring (Fin 56) (Fin 55) :=
  roundRobinColoring 55 (by norm_num)

/- The four balance statements are finite kernel computations.  They do not
   assert rainbow-freeness; that is a separate certificate obligation. -/
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem q6_roundRobin_balanced : q6RoundRobinColoring.IsBalanced := by
  change ∀ v : Fin 16, ∀ c : Fin 15,
    q6RoundRobinColoring.colorDegree v c = Fintype.card (Fin 16) / Fintype.card (Fin 15)
  decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem q7_roundRobin_balanced : q7RoundRobinColoring.IsBalanced := by
  change ∀ v : Fin 22, ∀ c : Fin 21,
    q7RoundRobinColoring.colorDegree v c = Fintype.card (Fin 22) / Fintype.card (Fin 21)
  decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem q10_roundRobin_balanced : q10RoundRobinColoring.IsBalanced := by
  change ∀ v : Fin 46, ∀ c : Fin 45,
    q10RoundRobinColoring.colorDegree v c = Fintype.card (Fin 46) / Fintype.card (Fin 45)
  decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem q11_roundRobin_balanced : q11RoundRobinColoring.IsBalanced := by
  change ∀ v : Fin 56, ∀ c : Fin 55,
    q11RoundRobinColoring.colorDegree v c = Fintype.card (Fin 56) / Fintype.card (Fin 55)
  decide

theorem q6_roundRobin_order :
    16 % edgeCount (SimpleGraph.completeGraph (Fin 6)) = 1 := by
  rw [edgeCount_completeGraph_fin]
  decide

theorem q7_roundRobin_order :
    22 % edgeCount (SimpleGraph.completeGraph (Fin 7)) = 1 := by
  rw [edgeCount_completeGraph_fin]
  decide

theorem q10_roundRobin_order :
    46 % edgeCount (SimpleGraph.completeGraph (Fin 10)) = 1 := by
  rw [edgeCount_completeGraph_fin]
  decide

theorem q11_roundRobin_order :
    56 % edgeCount (SimpleGraph.completeGraph (Fin 11)) = 1 := by
  rw [edgeCount_completeGraph_fin]
  decide

def q6EdgeColors (a b c d e f : Fin 16) : List (Fin 15) :=
  [q6RoundRobinColoring.color a b, q6RoundRobinColoring.color a c,
   q6RoundRobinColoring.color a d, q6RoundRobinColoring.color a e,
   q6RoundRobinColoring.color a f, q6RoundRobinColoring.color b c,
   q6RoundRobinColoring.color b d, q6RoundRobinColoring.color b e,
   q6RoundRobinColoring.color b f, q6RoundRobinColoring.color c d,
   q6RoundRobinColoring.color c e, q6RoundRobinColoring.color c f,
   q6RoundRobinColoring.color d e, q6RoundRobinColoring.color d f,
   q6RoundRobinColoring.color e f]

/- There are only `binom 16 6 = 8008` sorted six-sets.  Keeping this as a
   kernel `decide` certificate is substantially smaller than an unanchored
   SAT trace and leaves the mathematical round-robin formula visible. -/
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem q6_no_rainbow_sorted :
    ∀ a b c d e f : Fin 16,
      a < b → b < c → c < d → d < e → e < f →
      ¬ (q6EdgeColors a b c d e f).Nodup := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem q6_no_rainbow :
    ¬ HasRainbowCopy (SimpleGraph.completeGraph (Fin 6))
      q6RoundRobinColoring := by
  classical
  rintro ⟨f, hf⟩
  let s : Finset (Fin 16) := Finset.univ.image f
  have hs_card : s.card = 6 := by
    dsimp [s]
    apply (Finset.card_image_iff).2
    intro x hx y hy hxy
    exact f.injective hxy
  let g : Fin 6 ↪ Fin 16 := (s.orderEmbOfFin hs_card).toEmbedding
  have hg_mem (i : Fin 6) : g i ∈ s := by
    exact Finset.orderEmbOfFin_mem s hs_card i
  have hmem_image (i : Fin 6) : g i ∈ Finset.univ.image f := by
    simpa [s] using hg_mem i
  let p : Fin 6 → Fin 6 := fun i =>
    Classical.choose (Finset.mem_image.mp (hmem_image i))
  have hp_spec (i : Fin 6) : f (p i) = g i := by
    dsimp [p]
    exact (Classical.choose_spec (Finset.mem_image.mp (hmem_image i))).2
  let pEmb : Fin 6 ↪ Fin 6 := {
    toFun := p
    inj' := by
      intro i j hij
      apply g.injective
      rw [← hp_spec i, ← hp_spec j, hij]
  }
  have hdiff {a b c d : Fin 6}
      (hab : a ≠ b) (hcd : c ≠ d)
      (hnot : ¬ SameUndirectedEdge a b c d) :
      q6RoundRobinColoring.color (g a) (g b) ≠
        q6RoundRobinColoring.color (g c) (g d) := by
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
  have hcolors :
      (q6EdgeColors (g 0) (g 1) (g 2) (g 3) (g 4) (g 5)).Nodup := by
    simp only [q6EdgeColors, List.nodup_cons, List.not_mem_nil, List.mem_cons,
      not_or, not_false_eq_true, true_and]
    repeat' constructor
    all_goals apply hdiff <;> simp [SameUndirectedEdge]
  exact q6_no_rainbow_sorted (g 0) (g 1) (g 2) (g 3) (g 4) (g 5)
    ((s.orderEmbOfFin hs_card).lt_iff_lt.mpr (by decide))
    ((s.orderEmbOfFin hs_card).lt_iff_lt.mpr (by decide))
    ((s.orderEmbOfFin hs_card).lt_iff_lt.mpr (by decide))
    ((s.orderEmbOfFin hs_card).lt_iff_lt.mpr (by decide))
    ((s.orderEmbOfFin hs_card).lt_iff_lt.mpr (by decide)) hcolors

#print axioms q6_roundRobin_balanced
#print axioms q7_roundRobin_balanced
#print axioms q10_roundRobin_balanced
#print axioms q11_roundRobin_balanced
#print axioms q6_no_rainbow

end Erdos811
