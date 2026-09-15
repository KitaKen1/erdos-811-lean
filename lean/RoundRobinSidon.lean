import RoundRobin
import WeakSidon
import Mathlib.Data.ZMod.Basic

/-!
# Additive bridge for the round-robin colouring

This file connects equality of sums in `ZMod m` with equality of finite-edge
colours.  It is the small semantic bridge needed to replace the concrete
search certificates for `q = 6, 7, 10, 11` by the weak-Sidon count.
-/

namespace Erdos811

def roundRobinResidue {m : ℕ} (v : Fin (m + 1)) : ZMod m := v.val

lemma roundRobinColor_eq_of_finite_sum_eq {m : ℕ} (hm : 0 < m)
    {a b c d : Fin (m + 1)}
    (ha : a.val ≠ m) (hb : b.val ≠ m)
    (hc : c.val ≠ m) (hd : d.val ≠ m)
    (hsum : roundRobinResidue a + roundRobinResidue b =
      roundRobinResidue c + roundRobinResidue d) :
    (roundRobinColoring m hm).color a b =
      (roundRobinColoring m hm).color c d := by
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  apply Fin.ext
  simp only [roundRobinColoring, ha, hb, hc, hd, ↓reduceDIte]
  have hval := congrArg ZMod.val hsum
  simpa [roundRobinResidue, ZMod.val_add, ZMod.val_natCast] using hval

lemma roundRobinColor_finite_eq_infinity_of_threeAP {m : ℕ} (hm : 0 < m)
    {a b c top : Fin (m + 1)}
    (ha : a.val ≠ m) (hb : b.val ≠ m) (hc : c.val ≠ m)
    (htop : top.val = m)
    (hAP : roundRobinResidue b + roundRobinResidue c =
      2 • roundRobinResidue a) :
    (roundRobinColoring m hm).color b c =
      (roundRobinColoring m hm).color top a := by
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  apply Fin.ext
  simp only [roundRobinColoring, hb, hc, htop, ↓reduceDIte]
  have hval := congrArg ZMod.val hAP
  simpa [roundRobinResidue, ZMod.val_add, ZMod.val_natCast, two_nsmul,
    two_mul] using hval

private def finiteIndices {q m : ℕ} (f : Fin q ↪ Fin (m + 1)) : Finset (Fin q) :=
  Finset.univ.filter fun i => (f i).val ≠ m

private def roundRobinResidueSet {q m : ℕ}
    (f : Fin q ↪ Fin (m + 1)) : Finset (ZMod m) :=
  (finiteIndices f).image fun i => roundRobinResidue (f i)

private lemma roundRobinResidue_injective_on_finiteIndices {q m : ℕ} (hm : 0 < m)
    (f : Fin q ↪ Fin (m + 1)) :
    Set.InjOn (fun i => roundRobinResidue (f i)) (↑(finiteIndices f) : Set (Fin q)) := by
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  intro i hi j hj hij
  apply f.injective
  apply Fin.ext
  have hiNe : (f i).val ≠ m := (Finset.mem_filter.mp hi).2
  have hjNe : (f j).val ≠ m := (Finset.mem_filter.mp hj).2
  have hiLt : (f i).val < m := by omega
  have hjLt : (f j).val < m := by omega
  have hval := congrArg ZMod.val hij
  simpa [roundRobinResidue, ZMod.val_natCast_of_lt hiLt,
    ZMod.val_natCast_of_lt hjLt] using hval

private lemma card_roundRobinResidueSet_eq_card_finiteIndices {q m : ℕ} (hm : 0 < m)
    (f : Fin q ↪ Fin (m + 1)) :
    (roundRobinResidueSet f).card = (finiteIndices f).card := by
  unfold roundRobinResidueSet
  apply Finset.card_image_iff.mpr
  intro i hi j hj hij
  exact roundRobinResidue_injective_on_finiteIndices hm f hi hj hij

theorem no_roundRobin_rainbow_embedding_of_sidon_bounds {q m : ℕ} (hm : 0 < m)
    (hTwo : Function.Injective fun x : ZMod m => 2 • x)
    (hNoTop : ¬q * (q - 3) ≤ m - 1)
    (hWithTop : ¬(q - 1) * (q - 2) ≤ m - 1)
    (f : Fin q ↪ Fin (m + 1))
    (hRainbow : ∀ ⦃a b c d : Fin q⦄,
      a ≠ b → c ≠ d → ¬SameUndirectedEdge a b c d →
        (roundRobinColoring m hm).color (f a) (f b) ≠
          (roundRobinColoring m hm).color (f c) (f d)) : False := by
  classical
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  letI : LinearOrder (ZMod m) :=
    LinearOrder.lift' ZMod.val (ZMod.val_injective m)
  let A : Finset (ZMod m) := roundRobinResidueSet f
  have hAcard : A.card = (finiteIndices f).card := by
    simpa [A] using card_roundRobinResidueSet_eq_card_finiteIndices hm f
  have hWeak : IsWeakTwoSidon A := by
    intro x y z w hx hy hz hw hxy hzw hsum
    change x ∈ roundRobinResidueSet f at hx
    change y ∈ roundRobinResidueSet f at hy
    change z ∈ roundRobinResidueSet f at hz
    change w ∈ roundRobinResidueSet f at hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hw
    have hfi : (f i).val ≠ m := (Finset.mem_filter.mp hi).2
    have hfj : (f j).val ≠ m := (Finset.mem_filter.mp hj).2
    have hfk : (f k).val ≠ m := (Finset.mem_filter.mp hk).2
    have hfl : (f l).val ≠ m := (Finset.mem_filter.mp hl).2
    have hij : i ≠ j := by
      intro hij
      subst j
      exact hxy rfl
    have hkl : k ≠ l := by
      intro hkl
      subst l
      exact hzw rfl
    by_cases hedges : SameUndirectedEdge i j k l
    · rcases hedges with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    · exfalso
      exact (hRainbow hij hkl hedges)
        (roundRobinColor_eq_of_finite_sum_eq hm hfi hfj hfk hfl hsum)
  by_cases htop : ∃ i : Fin q, (f i).val = m
  · obtain ⟨iTop, hiTop⟩ := htop
    have htopIff (i : Fin q) : (f i).val = m ↔ i = iTop := by
      constructor
      · intro hi
        apply f.injective
        apply Fin.ext
        simpa [hiTop] using hi
      · rintro rfl
        exact hiTop
    have hindices : finiteIndices f = Finset.univ.erase iTop := by
      ext i
      simp only [finiteIndices, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_erase]
      constructor
      · intro hi
        exact ⟨fun hii => hi ((htopIff i).mpr hii), True.intro⟩
      · intro hi
        exact fun him => hi.1 ((htopIff i).mp him)
    have hcard : A.card = q - 1 := by
      rw [hAcard, hindices, Finset.card_erase_of_mem (Finset.mem_univ iTop)]
      simp
    have hAP : IsThreeAPFree A := by
      intro x y z hx hy hz hyz hprog
      change x ∈ roundRobinResidueSet f at hx
      change y ∈ roundRobinResidueSet f at hy
      change z ∈ roundRobinResidueSet f at hz
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
      have hfi : (f i).val ≠ m := (Finset.mem_filter.mp hi).2
      have hfj : (f j).val ≠ m := (Finset.mem_filter.mp hj).2
      have hfk : (f k).val ≠ m := (Finset.mem_filter.mp hk).2
      have hjk : j ≠ k := by
        intro hjk
        subst k
        exact hyz rfl
      have hTopi : iTop ≠ i := by
        intro hEq
        subst i
        exact hfi hiTop
      have hjTop : j ≠ iTop := by
        intro hEq
        subst j
        exact hfj hiTop
      have hkTop : k ≠ iTop := by
        intro hEq
        subst k
        exact hfk hiTop
      have hedges : ¬SameUndirectedEdge j k iTop i := by
        simp [SameUndirectedEdge, hjTop, hkTop]
      exact (hRainbow hjk hTopi hedges)
        (roundRobinColor_finite_eq_infinity_of_threeAP hm hfi hfj hfk hiTop hprog)
    have hbound := threeAPFree_weakTwoSidon_card_mul_sub_one_le A hWeak hAP hTwo
    rw [hcard] at hbound
    rw [ZMod.card] at hbound
    apply hWithTop
    simpa [Nat.sub_sub] using hbound
  · have hfinite (i : Fin q) : (f i).val ≠ m := by
      intro hi
      exact htop ⟨i, hi⟩
    have hindices : finiteIndices f = Finset.univ := by
      ext i
      simp [finiteIndices, hfinite i]
    have hcard : A.card = q := by
      rw [hAcard, hindices]
      simp
    have hbound := weakTwoSidon_card_mul_sub_three_le A hWeak hTwo
    rw [hcard] at hbound
    rw [ZMod.card] at hbound
    exact hNoTop hbound

end Erdos811
