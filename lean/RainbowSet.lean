import Erdos811Definitions

/-!
# Rainbow copies as finite vertex sets

The probabilistic construction counts `q`-subsets of the cyclic vertex set,
whereas the FC predicate is phrased using embeddings `Fin q ↪ V`.  This file
records the exact bridge for complete graphs.  It is deliberately independent
of the particular cyclic colouring, so it can also be reused by the finite
certificate modules.
-/

namespace Erdos811

/- All unoriented edges induced by `S` have pairwise distinct colours. -/
def IsRainbowSet {V C : Type*} (κ : CompleteEdgeColoring V C) (S : Finset V) : Prop :=
    ∀ ⦃a b c d : V⦄,
      a ∈ S → b ∈ S → c ∈ S → d ∈ S →
      a ≠ b → c ≠ d → ¬ SameUndirectedEdge a b c d →
      κ.color a b ≠ κ.color c d

def HasRainbowSet {V C : Type*} (q : ℕ)
    (κ : CompleteEdgeColoring V C) : Prop :=
  ∃ S : Finset V, S.card = q ∧ IsRainbowSet κ S

/- A cardinality version indexed by the finite subtype of q-subsets.  This is
the form used by finite first-moment sums. -/
abbrev QSubset (V : Type*) (q : ℕ) := {S : Finset V // S.card = q}

noncomputable def rainbowQSubsetCount {q : ℕ} {V C : Type*}
    [Fintype V] [DecidableEq V] [DecidableEq C]
    (κ : CompleteEdgeColoring V C) : ℕ := by
  classical
  exact Fintype.card {S : QSubset V q // IsRainbowSet κ S.1}

lemma hasRainbowCopy_completeGraph_iff
    {q : ℕ} {V C : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (κ : CompleteEdgeColoring V C) :
    HasRainbowCopy (SimpleGraph.completeGraph (Fin q)) κ ↔
      HasRainbowSet q κ := by
  constructor
  · rintro ⟨f, hf⟩
    let S : Finset V := Finset.univ.image f
    have hS_card : S.card = q := by
      dsimp [S]
      rw [Finset.card_image_of_injective _ f.injective]
      simp
    refine ⟨S, hS_card, ?_⟩
    intro a b c d ha hb hc hd hab hcd hsame
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hd
    apply hf
    · intro hij
      exact hab (congrArg f hij)
    · intro hkl
      exact hcd (congrArg f hkl)
    · intro hsame'
      apply hsame
      rcases hsame' with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact Or.inl ⟨congrArg f h₁, congrArg f h₂⟩
      · exact Or.inr ⟨congrArg f h₁, congrArg f h₂⟩
  · rintro ⟨S, hS_card, hrain⟩
    let g : Fin q ↪ V := (S.orderEmbOfFin hS_card).toEmbedding
    refine ⟨g, ?_⟩
    intro a b c d hab hcd hsame
    apply hrain
    · exact Finset.orderEmbOfFin_mem S hS_card a
    · exact Finset.orderEmbOfFin_mem S hS_card b
    · exact Finset.orderEmbOfFin_mem S hS_card c
    · exact Finset.orderEmbOfFin_mem S hS_card d
    · simpa [SimpleGraph.completeGraph] using hab
    · simpa [SimpleGraph.completeGraph] using hcd
    · intro hsame'
      apply hsame
      rcases hsame' with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact Or.inl ⟨g.injective h₁, g.injective h₂⟩
      · exact Or.inr ⟨g.injective h₁, g.injective h₂⟩

/- A rainbow embedding remains rainbow after applying a vertex map whose edge
colours are transformed by an injective colour map.  Cyclic translations of
the probabilistic construction are instances of this lemma. -/
lemma translated_rainbow_copy
    {α V C : Type*} (N : ℕ)
    (G : SimpleGraph α) (κ : CompleteEdgeColoring V C)
    (τ : Fin N → V → V)
    (hτ : ∀ t : Fin N, Function.Injective (τ t))
    (shift : Fin N → C → C)
    (hshift : ∀ t : Fin N, Function.Injective (shift t))
    (hcolor : ∀ (t : Fin N) (v w : V), v ≠ w →
      κ.color (τ t v) (τ t w) = shift t (κ.color v w))
    {f : α ↪ V}
    (hf : ∀ ⦃a b c d : α⦄,
      G.Adj a b → G.Adj c d → ¬ SameUndirectedEdge a b c d →
      κ.color (f a) (f b) ≠ κ.color (f c) (f d))
    (t : Fin N) :
    ∀ ⦃a b c d : α⦄,
      G.Adj a b → G.Adj c d → ¬ SameUndirectedEdge a b c d →
      κ.color ((f.trans ⟨τ t, hτ t⟩) a) ((f.trans ⟨τ t, hτ t⟩) b) ≠
        κ.color ((f.trans ⟨τ t, hτ t⟩) c) ((f.trans ⟨τ t, hτ t⟩) d) := by
  intro a b c d hab hcd hsame heq
  apply hf hab hcd hsame
  apply hshift t
  have hab_ne : a ≠ b := by
    intro hab'
    subst b
    exact G.loopless.irrefl a hab
  have hcd_ne : c ≠ d := by
    intro hcd'
    subst d
    exact G.loopless.irrefl c hcd
  have hab' : f a ≠ f b := f.injective.ne hab_ne
  have hcd' : f c ≠ f d := f.injective.ne hcd_ne
  change κ.color (τ t (f a)) (τ t (f b)) =
      κ.color (τ t (f c)) (τ t (f d)) at heq
  rw [hcolor t (f a) (f b) hab', hcolor t (f c) (f d) hcd'] at heq
  exact heq

lemma rainbowQSubsetCount_eq_zero_iff
    {q : ℕ} {V C : Type*} [Fintype V] [DecidableEq V]
    [LinearOrder V] [DecidableEq C]
    (κ : CompleteEdgeColoring V C) :
    rainbowQSubsetCount (q := q) κ = 0 ↔
      ¬ HasRainbowCopy (SimpleGraph.completeGraph (Fin q)) κ := by
  classical
  change Fintype.card {S : QSubset V q // IsRainbowSet κ S.1} = 0 ↔ _
  rw [Fintype.card_eq_zero_iff]
  constructor
  · intro hEmpty hcopy
    obtain ⟨S, hScard, hSrain⟩ :=
      (hasRainbowCopy_completeGraph_iff κ).mp hcopy
    exact hEmpty.false ⟨⟨S, hScard⟩, hSrain⟩
  · intro hno
    constructor
    intro x
    apply hno
    exact (hasRainbowCopy_completeGraph_iff κ).mpr
      ⟨x.1.1, x.1.2, x.2⟩

noncomputable def rainbowSetCount {q : ℕ} {V C : Type*} [Fintype V]
    [DecidableEq V] [DecidableEq C]
    (κ : CompleteEdgeColoring V C) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Finset V)).filter
    (fun S : Finset V => S.card = q ∧ IsRainbowSet κ S)).card

lemma rainbowSetCount_eq_zero_iff
    {q : ℕ} {V C : Type*} [Fintype V] [DecidableEq V]
    [LinearOrder V] [DecidableEq C]
    (κ : CompleteEdgeColoring V C) :
    rainbowSetCount (q := q) κ = 0 ↔
      ¬ HasRainbowCopy (SimpleGraph.completeGraph (Fin q)) κ := by
  classical
  constructor
  · intro hzero hcopy
    obtain ⟨S, hScard, hSrain⟩ :=
      (hasRainbowCopy_completeGraph_iff κ).mp hcopy
    have hmem : S ∈
        (Finset.univ : Finset (Finset V)).filter
          (fun T : Finset V => T.card = q ∧ IsRainbowSet κ T) := by
      simp [hScard, hSrain]
    have hpos : 0 < rainbowSetCount (q := q) κ := by
      unfold rainbowSetCount
      exact Finset.card_pos.mpr ⟨S, hmem⟩
    omega
  · intro hno
    unfold rainbowSetCount
    apply Finset.card_eq_zero.mpr
    ext S
    simp
    intro hmem
    intro hSrain
    apply hno
    apply (hasRainbowCopy_completeGraph_iff κ).mpr
    exact ⟨S, hmem, hSrain⟩

end Erdos811
