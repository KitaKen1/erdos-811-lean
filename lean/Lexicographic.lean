import Erdos811Definitions

/-!
# Lexicographic colouring infrastructure

The definitions here isolate the product operation used to amplify a finite
balanced counterexample.  The preservation lemmas are intentionally separate
from the finite certificates so they can be reused for every `q`.
-/

namespace Erdos811

universe u

/- The lexicographic product of a balanced colouring with itself. -/

def lexColoring {V C : Type*} [DecidableEq V]
    (κ : CompleteEdgeColoring V C) : CompleteEdgeColoring (V × V) C where
  color p q := if p.1 = q.1 then κ.color p.2 q.2 else κ.color p.1 q.1
  color_symm p q := by
    by_cases h : p.1 = q.1
    · simp [h, κ.color_symm]
    · simp [h, Ne.symm h, κ.color_symm]

theorem lexColoring_same_block {V C : Type*} [DecidableEq V]
    (κ : CompleteEdgeColoring V C) (a x y : V) :
    (lexColoring κ).color (a, x) (a, y) = κ.color x y := by
  simp [lexColoring]

theorem lexColoring_cross_block {V C : Type*} [DecidableEq V]
    (κ : CompleteEdgeColoring V C) {a b x y : V} (h : a ≠ b) :
    (lexColoring κ).color (a, x) (b, y) = κ.color a b := by
  simp [lexColoring, h]

/- A rainbow clique in the lexicographic product would already force one in
   the base colouring.  If the first coordinates are neither all equal nor
   all distinct, two cross-block edges have the same base colour. -/
theorem lexColoring_no_rainbow_of_no_rainbow {V C : Type*} (q : ℕ)
    [DecidableEq V] [DecidableEq C]
    (κ : CompleteEdgeColoring V C)
    (hκ : ¬ HasRainbowCopy (SimpleGraph.completeGraph (Fin q)) κ) :
    ¬ HasRainbowCopy (SimpleGraph.completeGraph (Fin q)) (lexColoring κ) := by
  classical
  rintro ⟨f, hf⟩
  let p : Fin q → V := fun i => (f i).1
  by_cases hp : Function.Injective p
  · let g : Fin q ↪ V := { toFun := p, inj' := hp }
    apply hκ
    refine ⟨g, ?_⟩
    intro a b c d hab hcd hnot
    have habp : p a ≠ p b := fun he => hab (hp he)
    have hcdp : p c ≠ p d := fun he => hcd (hp he)
    have hcol := hf hab hcd hnot
    simpa [g, p, lexColoring, habp, hcdp] using hcol
  · obtain ⟨i, j, hpij, hij⟩ := Function.not_injective_iff.mp hp
    by_cases hall : ∀ k : Fin q, p k = p i
    · let g : Fin q ↪ V := {
        toFun := fun k => (f k).2
        inj' := by
          intro k l hkl
          apply f.injective
          apply Prod.ext
          · exact (hall k).trans (hall l).symm
          · exact hkl
      }
      apply hκ
      refine ⟨g, ?_⟩
      intro a b c d hab hcd hnot
      have habp : (f a).1 = (f b).1 := (hall a).trans (hall b).symm
      have hcdp : (f c).1 = (f d).1 := (hall c).trans (hall d).symm
      have hcol := hf hab hcd hnot
      change κ.color (f a).2 (f b).2 ≠ κ.color (f c).2 (f d).2
      simpa [lexColoring, habp, hcdp] using hcol
    · push_neg at hall
      obtain ⟨k, hpk⟩ := hall
      have hik : i ≠ k := by
        intro hik
        apply hpk
        simpa [hik]
      have hjk : j ≠ k := by
        intro hjk
        apply hpk
        rw [← hjk, hpij]
      have hnot : ¬ SameUndirectedEdge i k j k := by
        intro hs
        rcases hs with ⟨hs, _⟩ | ⟨hs, _⟩
        · exact hij hs
        · exact hik hs
      have hcol := hf hik hjk hnot
      have hikp : (f i).1 ≠ (f k).1 := by
        simpa [p] using Ne.symm hpk
      have hjkp : (f j).1 ≠ (f k).1 := by
        intro he
        apply hpk
        change (f k).1 = (f i).1
        rw [← he]
        simpa [p] using hpij.symm
      have hpij' : (f i).1 = (f j).1 := by
        simpa [p] using hpij
      apply hcol
      calc
        (lexColoring κ).color (f i) (f k) =
            κ.color (f i).1 (f k).1 := by
              simp [lexColoring, hikp]
        _ = κ.color (f j).1 (f k).1 := by rw [hpij']
        _ = (lexColoring κ).color (f j) (f k) := by
              symm
              simp [lexColoring, hjkp]

/- The iterated product type and colouring.  `LexPow V k` is the k-fold
   binary product (with `k = 0` as the base type). -/
def LexPow (V : Type u) : ℕ → Type u
  | 0 => V
  | k + 1 => LexPow V k × LexPow V k

instance lexPowDecidableEq {V : Type u} [DecidableEq V] (k : ℕ) :
    DecidableEq (LexPow V k) := by
  induction k with
  | zero =>
      change DecidableEq V
      infer_instance
  | succ k ih =>
      change DecidableEq (LexPow V k × LexPow V k)
      letI : DecidableEq (LexPow V k) := ih
      infer_instance

noncomputable def lexPowColoring {V C : Type*} [DecidableEq V]
    (κ : CompleteEdgeColoring V C) : ∀ k : ℕ,
      CompleteEdgeColoring (LexPow V k) C
  | 0 => by simpa [LexPow] using κ
  | k + 1 => by
      exact lexColoring (lexPowColoring κ k)

theorem lexPow_no_rainbow {V C : Type*} [DecidableEq V] [DecidableEq C]
    (κ : CompleteEdgeColoring V C) (q : ℕ)
    (hκ : ¬ HasRainbowCopy (SimpleGraph.completeGraph (Fin q)) κ) :
    ∀ k : ℕ,
      ¬ HasRainbowCopy (SimpleGraph.completeGraph (Fin q)) (lexPowColoring κ k) := by
  intro k
  induction k with
  | zero =>
      change ¬ HasRainbowCopy (SimpleGraph.completeGraph (Fin q)) κ
      exact hκ
  | succ k ih =>
      classical
      change ¬ HasRainbowCopy (SimpleGraph.completeGraph (Fin q))
        (lexColoring (lexPowColoring κ k))
      exact lexColoring_no_rainbow_of_no_rainbow q (lexPowColoring κ k) ih

theorem lexColoring_colorDegree {V C : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq C] (κ : CompleteEdgeColoring V C) (a x : V) (c : C) :
    (lexColoring κ).colorDegree (a, x) c =
      κ.colorDegree x c + κ.colorDegree a c * Fintype.card V := by
  classical
  let U : Finset (V × V) := Finset.univ.erase (a, x)
  let A : Finset V := (Finset.univ.erase x).filter (fun y => κ.color x y = c)
  let B : Finset V := (Finset.univ.erase a).filter (fun b => κ.color a b = c)
  let S : Finset (V × V) := ({a} ×ˢ A)
  let T : Finset (V × V) := (B ×ˢ Finset.univ)
  have hsplit : U.filter (fun p => (lexColoring κ).color (a, x) p = c) = S ∪ T := by
    ext p
    rcases p with ⟨b, y⟩
    by_cases hba : b = a
    · subst b
      simp [U, A, B, S, T, lexColoring]
    · simp [U, A, B, S, T, lexColoring, hba, Ne.symm hba]
  rw [show (lexColoring κ).colorDegree (a, x) c =
      (U.filter (fun p => (lexColoring κ).color (a, x) p = c)).card by
        rfl]
  rw [hsplit, Finset.card_union_of_disjoint]
  · simp [S, T, A, B, CompleteEdgeColoring.colorDegree]
  · refine Finset.disjoint_left.2 ?_
    intro p hpS hpT
    rcases p with ⟨b, y⟩
    have hbS : b ∈ ({a} : Finset V) := (Finset.mem_product.mp hpS).1
    have hbT : b ∈ B := (Finset.mem_product.mp hpT).1
    have hba : b = a := by simpa using hbS
    have hbn : b ≠ a := by
      exact (Finset.mem_erase.mp (Finset.mem_filter.mp hbT).1).1
    exact hbn hba

/- The quotient identity needed by the balanced lexicographic lift.  The
   strict inequality `1 < c` records that the remainder `1` in
   `(d*c+1)^2` is smaller than the number of colours. -/
lemma div_sq_succ (d c : ℕ) (hc : 1 < c) :
    ((d * c + 1) * (d * c + 1)) / c = d + d * (d * c + 1) := by
  have hc0 : 0 < c := by omega
  apply Nat.div_eq_of_lt_le
  · nlinarith
  · nlinarith

lemma div_mul_succ (d c : ℕ) (hc : 1 < c) :
    (d * c + 1) / c = d := by
  have hc0 : 0 < c := by omega
  apply Nat.div_eq_of_lt_le
  · nlinarith
  · nlinarith

theorem lexColoring_isBalanced_of_degree {V C : Type*} [Fintype V]
    [DecidableEq V] [Fintype C] [DecidableEq C]
    (κ : CompleteEdgeColoring V C) (d : ℕ)
    (hdeg : ∀ v c, κ.colorDegree v c = d)
    (hcard : Fintype.card V = d * Fintype.card C + 1)
    (hc : 1 < Fintype.card C) :
    (lexColoring κ).IsBalanced := by
  intro p c
  rcases p with ⟨a, x⟩
  rw [lexColoring_colorDegree, hdeg, hdeg]
  simp only [Fintype.card_prod]
  rw [hcard]
  exact (div_sq_succ d (Fintype.card C) hc).symm

theorem lexColoring_isBalanced_of_balanced {V C : Type*} [Fintype V]
    [DecidableEq V] [Fintype C] [DecidableEq C]
    (κ : CompleteEdgeColoring V C) (d : ℕ)
    (hbal : κ.IsBalanced)
    (hcard : Fintype.card V = d * Fintype.card C + 1)
    (hc : 1 < Fintype.card C) :
    (lexColoring κ).IsBalanced := by
  apply lexColoring_isBalanced_of_degree κ d
  · intro v c
    rw [hbal v c, hcard]
    exact div_mul_succ d (Fintype.card C) hc
  · exact hcard
  · exact hc

end Erdos811
