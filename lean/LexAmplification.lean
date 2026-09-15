import Lexicographic
import Mathlib.Data.Nat.Log

/-!
# Reindexing and amplification on canonical `Fin` hosts

`Lexicographic.lean` proves preservation on the iterated product type.  The
Formal-Conjectures target, however, uses `Fin n` as the host type.  This file
supplies the finite equivalence step and the elementary unboundedness argument
needed to turn one finite base into arbitrarily large examples.
-/

namespace Erdos811

noncomputable section

@[instance_reducible] noncomputable def lexPowFintype {V : Type*} [Fintype V] :
    (k : ℕ) → Fintype (LexPow V k)
  | 0 => inferInstanceAs (Fintype V)
  | k + 1 => by
      letI : Fintype (LexPow V k) := lexPowFintype k
      exact inferInstanceAs (Fintype (LexPow V k × LexPow V k))

local instance lexPowFintypeInstance {V : Type*} [Fintype V] (k : ℕ) :
    Fintype (LexPow V k) := lexPowFintype k

noncomputable def reindexColoring {V W C : Type*}
    (e : V ≃ W) (κ : CompleteEdgeColoring V C) :
    CompleteEdgeColoring W C where
  color x y := κ.color (e.symm x) (e.symm y)
  color_symm x y := by
    simp [κ.color_symm]

lemma reindexColoring_colorDegree {V W C : Type*}
    [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] [DecidableEq C]
    (e : V ≃ W) (κ : CompleteEdgeColoring V C) (w : W) (c : C) :
    (reindexColoring e κ).colorDegree w c =
      κ.colorDegree (e.symm w) c := by
  classical
  let s : Finset W :=
    (Finset.univ.erase w).filter
      (fun y => (reindexColoring e κ).color w y = c)
  let t : Finset V :=
    (Finset.univ.erase (e.symm w)).filter
      (fun x => κ.color (e.symm w) x = c)
  change s.card = t.card
  refine Finset.card_bij (s := s) (t := t) (fun y _ => e.symm y) ?_ ?_ ?_
  · intro y hy
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_erase.mpr
      constructor
      · intro hxy
        exact (Finset.mem_erase.mp (Finset.mem_filter.mp hy).1).1
          (e.symm.injective hxy)
      · simp
    · simpa [reindexColoring] using (Finset.mem_filter.mp hy).2
  · intro y₁ hy₁ y₂ hy₂ hxy
    exact e.symm.injective hxy
  · intro x hx
    refine ⟨e x, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_erase.mpr
        constructor
        · intro hxe
          apply (Finset.mem_erase.mp (Finset.mem_filter.mp hx).1).1
          apply e.injective
          simpa [hxe]
        · simp
      · simpa [reindexColoring] using (Finset.mem_filter.mp hx).2
    · simp

theorem reindexColoring_isBalanced {V W C : Type*}
    [Fintype V] [Fintype W] [Fintype C]
    [DecidableEq V] [DecidableEq W] [DecidableEq C]
    (e : V ≃ W) (κ : CompleteEdgeColoring V C)
    (hκ : κ.IsBalanced) :
    (reindexColoring e κ).IsBalanced := by
  have hcard : Fintype.card V = Fintype.card W := Fintype.card_congr e
  intro w c
  rw [reindexColoring_colorDegree]
  simpa [hcard] using hκ (e.symm w) c

theorem reindexColoring_no_rainbow {α V W C : Type*}
    (G : SimpleGraph α) [DecidableEq V]
    (e : V ≃ W) (κ : CompleteEdgeColoring V C)
    (hκ : ¬ HasRainbowCopy G κ) :
    ¬ HasRainbowCopy G (reindexColoring e κ) := by
  classical
  rintro ⟨f, hf⟩
  apply hκ
  let g : α ↪ V := {
    toFun := fun a => e.symm (f a)
    inj' := by
      intro a b hab
      apply f.injective
      exact e.symm.injective hab
  }
  refine ⟨g, ?_⟩
  intro a b c d hab hcd hnot
  have hcol := hf hab hcd hnot
  change κ.color (e.symm (f a)) (e.symm (f b)) ≠
    κ.color (e.symm (f c)) (e.symm (f d))
  simpa [reindexColoring] using hcol

lemma card_lexPow (V : Type*) [Fintype V] (k : ℕ) :
    Fintype.card (LexPow V k) = (Fintype.card V) ^ (2 ^ k) := by
  induction k with
  | zero =>
      have hcard : Fintype.card (LexPow V 0) = Fintype.card V :=
        Fintype.card_congr (Equiv.refl V)
      simpa [LexPow] using hcard
  | succ k ih =>
      calc
        Fintype.card (LexPow V (k + 1)) =
            (Fintype.card (LexPow V k)) *
              (Fintype.card (LexPow V k)) := by
                change Fintype.card (LexPow V k × LexPow V k) = _
                rw [Fintype.card_prod]
        _ = (Fintype.card V ^ (2 ^ k)) *
              (Fintype.card V ^ (2 ^ k)) := by rw [ih]
        _ = Fintype.card V ^ (2 ^ k + 2 ^ k) := by
              rw [Nat.pow_add]
        _ = Fintype.card V ^ (2 ^ (k + 1)) := by
              congr 1
              rw [pow_succ]
              omega

lemma card_lexPow_fin (n k : ℕ) :
    Fintype.card (LexPow (Fin n) k) = n ^ (2 ^ k) := by
  simpa using card_lexPow (Fin n) k

lemma pow_mod_eq_one_of_mod_eq_one (n m r : ℕ) (hm : 1 < m)
    (hmod : n % m = 1) : n ^ r % m = 1 := by
  induction r with
  | zero =>
      simp only [pow_zero]
      exact Nat.mod_eq_of_lt (by omega)
  | succ r ih =>
      rw [pow_succ, Nat.mul_mod, ih, hmod]
      simp [Nat.mod_eq_of_lt hm]

lemma lexPow_card_mod (n m k : ℕ) (hm : 1 < m) (hmod : n % m = 1) :
    (Fintype.card (LexPow (Fin n) k)) % m = 1 := by
  rw [card_lexPow_fin]
  exact pow_mod_eq_one_of_mod_eq_one n m (2 ^ k) hm hmod

lemma lexPow_card_ge (n k : ℕ) (hn : 2 ≤ n) :
    n ≤ Fintype.card (LexPow (Fin n) k) := by
  rw [card_lexPow_fin]
  have hbase : n ≤ n ^ (2 ^ k) := by
    have hnpos : n > 0 := by omega
    have hexp : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    simpa using (Nat.pow_le_pow_right hnpos hexp)
  exact hbase

theorem lexPowColoring_isBalanced_of_balanced
    {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
    (κ : CompleteEdgeColoring V C) (hκ : κ.IsBalanced)
    (hmod : Fintype.card V % Fintype.card C = 1)
    (hc : 1 < Fintype.card C) :
    ∀ k : ℕ, (lexPowColoring κ k).IsBalanced := by
  intro k
  induction k with
  | zero =>
      have hF : lexPowFintypeInstance (V := V) 0 =
          (inferInstance : Fintype V) := Subsingleton.elim _ _
      have hD : lexPowDecidableEq (V := V) 0 =
          (inferInstance : DecidableEq V) := Subsingleton.elim _ _
      cases hF
      cases hD
      change @CompleteEdgeColoring.IsBalanced V C
        (lexPowFintypeInstance (V := V) 0)
        (fun a b => lexPowDecidableEq (V := V) 0 a b)
        _ _ κ
      convert hκ using 1 <;> try rfl <;> apply Subsingleton.elim
  | succ k ih =>
      let d : ℕ := Fintype.card (LexPow V k) / Fintype.card C
      have hmodk : Fintype.card (LexPow V k) % Fintype.card C = 1 := by
        rw [card_lexPow]
        exact pow_mod_eq_one_of_mod_eq_one
          (Fintype.card V) (Fintype.card C) (2 ^ k) hc hmod
      have hcard : Fintype.card (LexPow V k) =
          d * Fintype.card C + 1 := by
        dsimp [d]
        calc
          Fintype.card (LexPow V k) =
              Fintype.card (LexPow V k) % Fintype.card C +
                Fintype.card C * (Fintype.card (LexPow V k) /
                  Fintype.card C) :=
            (Nat.mod_add_div _ _).symm
          _ = 1 + Fintype.card C *
                (Fintype.card (LexPow V k) / Fintype.card C) := by
            rw [hmodk]
          _ = Fintype.card (LexPow V k) / Fintype.card C *
                Fintype.card C + 1 := by
            ac_rfl
      exact lexColoring_isBalanced_of_balanced
        (lexPowColoring κ k) d ih hcard hc

theorem hasArbitrarilyLarge_of_finite_base
    (q n : ℕ)
    (hmod : n % edgeCount (SimpleGraph.completeGraph (Fin q)) = 1)
    (κ : CompleteEdgeColoring (Fin n)
      (Fin (edgeCount (SimpleGraph.completeGraph (Fin q)))))
    (hbal : κ.IsBalanced)
    (hno : ¬ HasRainbowCopy (SimpleGraph.completeGraph (Fin q)) κ)
    (hn : 2 ≤ n)
    (hm : 1 < edgeCount (SimpleGraph.completeGraph (Fin q))) :
    HasArbitrarilyLargeBalancedCounterexamples
      (SimpleGraph.completeGraph (Fin q)) := by
  intro n₀
  let k : ℕ := Nat.clog n n₀
  have hkbase : n₀ ≤ n ^ k := by
    exact Nat.le_pow_clog (by omega) _
  let V := LexPow (Fin n) k
  have hcard_ge : n₀ ≤ Fintype.card V := by
    calc
      n₀ ≤ n ^ k := hkbase
      _ ≤ Fintype.card V := by
        dsimp [V]
        rw [card_lexPow_fin]
        apply Nat.pow_le_pow_right (by omega)
        have hpow : k ≤ 2 ^ k := by
          induction k with
          | zero => simp
          | succ k ih =>
              rw [pow_succ]
              have htwo : 1 ≤ 2 ^ k := Nat.one_le_two_pow
              omega
        exact hpow
  let Gq := SimpleGraph.completeGraph (Fin q)
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let κV : CompleteEdgeColoring V (Fin (edgeCount Gq)) :=
    lexPowColoring κ k
  let κ' : CompleteEdgeColoring (Fin (Fintype.card V)) (Fin (edgeCount Gq)) :=
    reindexColoring e κV
  refine ⟨Fintype.card V, hcard_ge, ?_⟩
  constructor
  · simpa [V, Gq] using lexPow_card_mod n (edgeCount Gq) k hm hmod
  · refine ⟨κ', ?_, ?_⟩
    · simpa [κ', κV] using reindexColoring_isBalanced e κV
        (lexPowColoring_isBalanced_of_balanced κ hbal (by simpa using hmod)
          (by simpa using hm) k)
    · simpa [κ', κV, Gq] using reindexColoring_no_rainbow Gq e κV
        (lexPow_no_rainbow κ q hno k)

#print axioms hasArbitrarilyLarge_of_finite_base

end
end Erdos811
