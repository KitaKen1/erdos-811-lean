import Mathlib

namespace Erdos811

lemma testBit_one_shiftLeft_iff (c i : Nat) :
    (1 <<< c).testBit i = decide (i = c) := by
  rw [Nat.testBit_shiftLeft]
  by_cases hic : i < c
  · have hne : ¬ i = c := by omega
    simp [Nat.not_le.mpr hic, hne]
  · have hge : c ≤ i := Nat.le_of_not_gt hic
    by_cases hzero : i - c = 0
    · have hle : i ≤ c := Nat.sub_eq_zero_iff_le.mp hzero
      have heq : i = c := Nat.le_antisymm hle hge
      simp [hge, hzero, heq]
    · simp only [Nat.testBit_eq_decide_div_mod_eq]
      have hpow : 1 < 2 ^ (i - c) := Nat.one_lt_two_pow hzero
      have hdiv : 1 / 2 ^ (i - c) = 0 := Nat.div_eq_of_lt hpow
      have hne : ¬ i = c := by
        intro heq
        apply hzero
        simp [heq]
      simp [hge, hdiv, hne]

lemma nat_land_one_shiftLeft_eq_zero_of_testBit_false {m c : Nat}
    (h : m.testBit c = false) : m.land (1 <<< c) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (m &&& (1 <<< c)).testBit i = (0 : Nat).testBit i
  rw [Nat.testBit_land, Nat.testBit_shiftLeft]
  by_cases hic : i < c
  · simp [hic]
  · have hge : c ≤ i := Nat.le_of_not_gt hic
    by_cases hio : i = c
    · subst i
      simp [h]
    · have hsub : 0 < i - c := Nat.sub_pos_of_lt (Nat.lt_of_le_of_ne hge (Ne.symm hio))
      simp only [Nat.testBit_eq_decide_div_mod_eq]
      have hpow : 1 < 2 ^ (i - c) := by
        exact Nat.one_lt_two_pow hsub.ne'
      have hdiv : 1 / 2 ^ (i - c) = 0 := Nat.div_eq_of_lt hpow
      simp [hge, hdiv]

lemma nat_land_lor_shiftLeft_eq_zero {m c d : Nat}
    (hm : m.land (1 <<< d) = 0) (hcd : c ≠ d) :
    (m.lor (1 <<< c)).land (1 <<< d) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  change Nat.testBit ((m ||| (1 <<< c)) &&& (1 <<< d)) i = Nat.testBit 0 i
  rw [Nat.testBit_land, Nat.testBit_lor]
  have hmd : m.testBit d = false := by
    have := congrArg (fun z : Nat => z.testBit d) hm
    simpa [Nat.testBit_land, Nat.testBit_shiftLeft] using this
  by_cases hid : i = d
  · subst i
    have hcbit : (1 <<< c).testBit d = false := by
      rw [testBit_one_shiftLeft_iff]
      simp [Ne.symm hcd]
    have hdbit : (1 <<< d).testBit d = true := by
      rw [testBit_one_shiftLeft_iff]
      simp
    simp [hmd, hcbit, hdbit]
  · have hmask : (1 <<< d).testBit i = false := by
      rw [testBit_one_shiftLeft_iff]
      simp [hid]
    simp [hmask]

end Erdos811
