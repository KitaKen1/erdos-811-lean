import Erdos811Definitions
import Mathlib.Data.ZMod.Basic

/-!
# Canonical unoriented differences in an odd cyclic group

For an odd modulus, every nonzero residue has exactly one representative whose
numeric value is smaller than that of its negative.  The subtype below is a
concrete, quotient-free model of the unoriented difference classes used by the
q≥12 pairing construction.
-/

namespace Erdos811

def CanonicalDiff (N : ℕ) :=
  {d : ZMod N // d ≠ 0 ∧ d.val < (-d).val}

noncomputable instance zmodFintype (N : ℕ) [NeZero N] : Fintype (ZMod N) :=
  Fintype.ofEquiv (Fin N) (ZMod.finEquiv N).toEquiv

noncomputable instance canonicalDiffFintype {N : ℕ} [NeZero N] :
    Fintype (CanonicalDiff N) :=
  Fintype.subtype
    ((Finset.univ : Finset (ZMod N)).filter
      (fun d => d ≠ 0 ∧ d.val < (-d).val)) (by simp)

noncomputable instance canonicalDiffDecidableEq {N : ℕ} [NeZero N] :
    DecidableEq (CanonicalDiff N) := Classical.decEq _

lemma canonicalDiff_val_pos {N : ℕ} [NeZero N]
    (d : CanonicalDiff N) : 0 < d.1.val := by
  exact ZMod.val_pos.mpr d.2.1

lemma canonicalDiff_val_neg {N : ℕ} [NeZero N]
    (hOdd : Odd N) (d : CanonicalDiff N) :
    (-d.1).val = N - d.1.val := by
  letI : NeZero d.1 := ⟨d.2.1⟩
  exact ZMod.val_neg_of_ne_zero d.1

lemma canonicalDiff_val_lt_half {N : ℕ} [NeZero N]
    (hOdd : Odd N) (d : CanonicalDiff N) :
    d.1.val - 1 < (N - 1) / 2 := by
  let r : ℕ := Classical.choose hOdd
  have hr : N = 2 * r + 1 := Classical.choose_spec hOdd
  have hneg := canonicalDiff_val_neg hOdd d
  have hlt := d.2.2
  have hval : d.1.val < N := ZMod.val_lt d.1
  have hhalf : (N - 1) / 2 = r := by omega
  rw [hneg] at hlt
  have hbound : 2 * d.1.val < 2 * r + 1 := by omega
  have hdpos : 0 < d.1.val := canonicalDiff_val_pos d
  calc
    d.1.val - 1 < r := by omega
    _ = (N - 1) / 2 := hhalf.symm

lemma canonicalDiff_val_ne_neg {N : ℕ} [NeZero N]
    (hOdd : Odd N) {d : ZMod N} (hd : d ≠ 0) :
    d.val ≠ (-d).val := by
  let r : ℕ := Classical.choose hOdd
  have hr : N = 2 * r + 1 := Classical.choose_spec hOdd
  intro heq
  have hneg : (-d).val = N - d.val := by
    letI : NeZero d := ⟨hd⟩
    exact ZMod.val_neg_of_ne_zero d
  have hval : d.val < N := ZMod.val_lt d
  omega

noncomputable def canonicalDiff (N : ℕ) [NeZero N]
    (hOdd : Odd N) (d : ZMod N) (hd : d ≠ 0) : CanonicalDiff N := by
  by_cases hlt : d.val < (-d).val
  · exact ⟨d, hd, hlt⟩
  · have hle : (-d).val ≤ d.val := Nat.le_of_not_gt hlt
    have hneq : (-d).val ≠ d.val := by
      intro heq
      exact canonicalDiff_val_ne_neg hOdd hd heq.symm
    have hlt' : (-d).val < d.val := lt_of_le_of_ne hle hneq
    refine ⟨-d, ?_, ?_⟩
    exact neg_ne_zero.mpr hd
    simpa only [neg_neg] using hlt'

lemma canonicalDiff_self {N : ℕ} [NeZero N]
    (hOdd : Odd N) (d : CanonicalDiff N) :
    canonicalDiff N hOdd d.1 d.2.1 = d := by
  apply Subtype.ext
  simp [canonicalDiff, d.2.2]

lemma canonicalDiff_neg {N : ℕ} [NeZero N]
    (hOdd : Odd N) {d : ZMod N} (hd : d ≠ 0) :
    canonicalDiff N hOdd (-d) (neg_ne_zero.mpr hd) =
      canonicalDiff N hOdd d hd := by
  apply Subtype.ext
  by_cases hlt : d.val < (-d).val
  · have hnot : ¬ (-d).val < d.val := by
      exact Nat.not_lt_of_ge (Nat.le_of_lt hlt)
    simp [canonicalDiff, hlt, hnot, neg_neg]
  · have hle : (-d).val ≤ d.val := Nat.le_of_not_gt hlt
    have hneq : (-d).val ≠ d.val := by
      intro heq
      exact canonicalDiff_val_ne_neg hOdd hd heq.symm
    have hlt' : (-d).val < d.val := lt_of_le_of_ne hle hneq
    simp [canonicalDiff, hlt, hlt', neg_neg]

lemma canonicalDiff_eq_iff {N : ℕ} [NeZero N]
    (hOdd : Odd N) {d : ZMod N} (hd : d ≠ 0)
    {e : CanonicalDiff N} :
    canonicalDiff N hOdd d hd = e ↔ d = e.1 ∨ d = -e.1 := by
  constructor
  · intro h
    by_cases hlt : d.val < (-d).val
    · left
      have hval := congrArg Subtype.val h
      simp [canonicalDiff, hlt] at hval
      exact hval
    · right
      have hval := congrArg Subtype.val h
      simp [canonicalDiff, hlt] at hval
      simpa using congrArg Neg.neg hval
  · rintro (rfl | hde)
    · exact canonicalDiff_self hOdd e
    · subst d
      calc
        canonicalDiff N hOdd (-e.1) _ =
            canonicalDiff N hOdd e.1 _ :=
          canonicalDiff_neg hOdd (by simpa using e.2.1)
        _ = e := canonicalDiff_self hOdd e

noncomputable def canonicalDiffEquivFin (N : ℕ) [NeZero N]
    (hOdd : Odd N) : CanonicalDiff N ≃ Fin ((N - 1) / 2) := by
  let f : CanonicalDiff N → Fin ((N - 1) / 2) := fun d =>
    ⟨d.1.val - 1, canonicalDiff_val_lt_half hOdd d⟩
  let g : Fin ((N - 1) / 2) → CanonicalDiff N := fun k => by
    let r : ℕ := Classical.choose hOdd
    have hr : N = 2 * r + 1 := Classical.choose_spec hOdd
    have hhalf : (N - 1) / 2 = r := by omega
    have hN : N = 2 * r + 1 := hr
    have hk : k.val < r := by simpa [hhalf] using k.isLt
    have hpos : 0 < k.val + 1 := by omega
    have hltN : k.val + 1 < N := by omega
    have hcastval : ((k.val + 1 : ℕ) : ZMod N).val = k.val + 1 := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hltN]
    have hcastne : ((k.val + 1 : ℕ) : ZMod N) ≠ 0 := by
      intro hz
      have hz' := congrArg ZMod.val hz
      rw [hcastval] at hz'
      have hz'' : k.val + 1 = 0 := by simpa using hz'
      omega
    have hneg : (-((k.val + 1 : ℕ) : ZMod N)).val =
        N - (k.val + 1) := by
      letI : NeZero ((k.val + 1 : ℕ) : ZMod N) := ⟨hcastne⟩
      rw [ZMod.val_neg_of_ne_zero, hcastval]
    have hlt : (k.val + 1 : ℕ) < N - (k.val + 1) := by omega
    have hcastval' : ((k.val : ZMod N) + 1).val = k.val + 1 := by
      simpa only [Nat.cast_add, Nat.cast_one] using hcastval
    have hneg' : (-(k.val : ZMod N) - 1).val =
        N - (k.val + 1) := by
      simpa [sub_eq_add_neg, Nat.cast_add, Nat.cast_one, add_comm] using hneg
    have hcastne' : (k.val : ZMod N) + 1 ≠ 0 := by
      simpa only [Nat.cast_add, Nat.cast_one] using hcastne
    have hlt' : ((k.val : ZMod N) + 1).val <
        (-(k.val : ZMod N) - 1).val := by
      rw [hcastval', hneg']
      exact hlt
    exact ⟨(k.val : ZMod N) + 1, hcastne', by
      simpa [sub_eq_add_neg, neg_add, add_comm] using hlt'⟩
  refine {
    toFun := f
    invFun := g
    left_inv := ?_
    right_inv := ?_ }
  · intro d
    apply Subtype.ext
    dsimp [f, g]
    have hdpos : 0 < d.1.val := canonicalDiff_val_pos d
    change ((d.1.val - 1 : ℕ) : ZMod N) + 1 = d.1
    calc
      ((d.1.val - 1 : ℕ) : ZMod N) + 1 =
          ((d.1.val - 1 + 1 : ℕ) : ZMod N) := by
            simp [Nat.cast_add]
      _ = (d.1.val : ZMod N) := by
        rw [show d.1.val - 1 + 1 = d.1.val by omega]
      _ = d.1 := ZMod.natCast_zmod_val d.1
  · intro k
    apply Fin.ext
    dsimp [f, g]
    let r : ℕ := Classical.choose hOdd
    have hr : N = 2 * r + 1 := Classical.choose_spec hOdd
    have hhalf : (N - 1) / 2 = r := by omega
    have hltN : k.val + 1 < N := by omega
    have hcastvalNat : ((k.val + 1 : ℕ) : ZMod N).val = k.val + 1 := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hltN]
    have hcastval : ((k.val : ZMod N) + 1).val = k.val + 1 := by
      simpa only [Nat.cast_add, Nat.cast_one] using hcastvalNat
    rw [hcastval]
    omega

lemma card_canonicalDiff {N : ℕ} [NeZero N] (hOdd : Odd N) :
    Fintype.card (CanonicalDiff N) = (N - 1) / 2 := by
  simpa using Fintype.card_congr (canonicalDiffEquivFin N hOdd)

/- The unit difference class.  We keep it as a named term so that the
   diagonal branch of the complete coloring has a canonical value. -/
noncomputable def canonicalOne {N : ℕ} [NeZero N]
    (hOdd : Odd N) (hN3 : 3 ≤ N) : CanonicalDiff N := by
  have hN1 : N ≠ 1 := by omega
  have hval : (1 : ZMod N).val = 1 := ZMod.val_one'' hN1
  have hne : (1 : ZMod N) ≠ 0 := by
    intro hz
    have hz' := congrArg ZMod.val hz
    rw [hval] at hz'
    simp at hz'
  exact canonicalDiff N hOdd (1 : ZMod N) hne

/- The natural cyclic coloring: a nonzero difference is identified with its
   unoriented canonical representative.  The diagonal is assigned an
   arbitrary fixed color because complete edge-colorings in the project are
   total on `V × V`. -/
noncomputable def cyclicDifferenceColoringZMod {N : ℕ} [NeZero N]
    (hOdd : Odd N) (hN3 : 3 ≤ N) :
    CompleteEdgeColoring (ZMod N) (CanonicalDiff N) := by
  classical
  let one : CanonicalDiff N := canonicalOne hOdd hN3
  refine {
    color := fun x y => if hxy : x = y then one else
      canonicalDiff N hOdd (y - x) (sub_ne_zero.mpr (Ne.symm hxy))
    color_symm := ?_ }
  intro x y
  by_cases hxy : x = y
  · simp [hxy]
  · have hyx : ¬ y = x := Ne.symm hxy
    simp [hxy, hyx]
    have hd : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
    simpa [neg_sub] using (canonicalDiff_neg hOdd hd).symm

lemma cyclicDifferenceColoringZMod_color_of_ne
    {N : ℕ} [NeZero N] (hOdd : Odd N) (hN3 : 3 ≤ N)
    {x y : ZMod N} (hxy : x ≠ y) :
    (cyclicDifferenceColoringZMod hOdd hN3).color x y =
      canonicalDiff N hOdd (y - x) (sub_ne_zero.mpr (Ne.symm hxy)) := by
  simp [cyclicDifferenceColoringZMod, hxy]

lemma cyclicDifferenceColoringZMod_colorDegree
    {N : ℕ} [NeZero N] (hOdd : Odd N) (hN3 : 3 ≤ N)
    (x : ZMod N) (d : CanonicalDiff N) :
    (cyclicDifferenceColoringZMod hOdd hN3).colorDegree x d = 2 := by
  classical
  have hplus : x + d.1 ≠ x := by
    intro h
    apply d.2.1
    have hz := congrArg (fun z : ZMod N => z - x) h
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hz
  have hminus : x - d.1 ≠ x := by
    intro h
    apply d.2.1
    have hz : -d.1 = 0 := by
      have hz' := congrArg (fun z : ZMod N => z - x) h
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hz'
    exact neg_eq_zero.mp hz
  have hpair : x + d.1 ≠ x - d.1 := by
    intro h
    have heq : d.1 = -d.1 := by
      have hz := congrArg (fun z : ZMod N => z - x) h
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hz
    have hsum : d.1 + d.1 = 0 := by
      calc
        d.1 + d.1 = d.1 + (-d.1) := congrArg (fun z => d.1 + z) heq
        _ = 0 := add_neg_cancel d.1
    exact d.2.1 ((ZMod.add_self_eq_zero_iff_eq_zero hOdd).mp hsum)
  let s : Finset (ZMod N) :=
    ((Finset.univ.erase x).filter
      (fun y => (cyclicDifferenceColoringZMod hOdd hN3).color x y = d))
  have hs : s = {x + d.1, x - d.1} := by
    ext y
    simp only [s, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
      true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hyx, _⟩, hcol⟩
      have hcol' :
          canonicalDiff N hOdd (y - x) (sub_ne_zero.mpr hyx) = d := by
        calc
          canonicalDiff N hOdd (y - x) (sub_ne_zero.mpr hyx) =
              (cyclicDifferenceColoringZMod hOdd hN3).color x y :=
            (cyclicDifferenceColoringZMod_color_of_ne hOdd hN3
              (Ne.symm hyx)).symm
          _ = d := hcol
      rcases (canonicalDiff_eq_iff hOdd
        (sub_ne_zero.mpr hyx)).mp hcol' with h | h
      · left
        have h' := eq_add_of_sub_eq h
        simpa [sub_eq_add_neg, add_comm] using h'
      · right
        have h' := eq_add_of_sub_eq h
        simpa [sub_eq_add_neg, add_comm] using h'
    · intro hy
      rcases hy with rfl | rfl
      · refine ⟨⟨hplus, trivial⟩, ?_⟩
        rw [cyclicDifferenceColoringZMod_color_of_ne hOdd hN3 (Ne.symm hplus)]
        apply (canonicalDiff_eq_iff hOdd
          (sub_ne_zero.mpr hplus)).2
        left
        simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
      · refine ⟨⟨hminus, trivial⟩, ?_⟩
        rw [cyclicDifferenceColoringZMod_color_of_ne hOdd hN3 (Ne.symm hminus)]
        apply (canonicalDiff_eq_iff hOdd
          (sub_ne_zero.mpr hminus)).2
        right
        simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
  change s.card = 2
  rw [hs]
  simp [hplus, hminus, hpair]

lemma cyclicDifferenceColoringZMod_translate
    {N : ℕ} [NeZero N] (hOdd : Odd N) (hN3 : 3 ≤ N)
    (t x y : ZMod N) :
    (cyclicDifferenceColoringZMod hOdd hN3).color (t + x) (t + y) =
      (cyclicDifferenceColoringZMod hOdd hN3).color x y := by
  by_cases hxy : x = y
  · subst y
    simp [cyclicDifferenceColoringZMod]
  · have hxy' : t + x ≠ t + y := by
      intro h
      exact hxy (add_left_cancel h)
    have hleft := cyclicDifferenceColoringZMod_color_of_ne hOdd hN3 hxy'
    have hright := cyclicDifferenceColoringZMod_color_of_ne hOdd hN3 hxy
    calc
      (cyclicDifferenceColoringZMod hOdd hN3).color (t + x) (t + y) =
          canonicalDiff N hOdd ((t + y) - (t + x)) _ := hleft
      _ = canonicalDiff N hOdd (y - x) _ := by
        congr 1
        abel
      _ = (cyclicDifferenceColoringZMod hOdd hN3).color x y := hright.symm

noncomputable def cyclicDifferenceColoringFin {N : ℕ} [NeZero N]
    (hOdd : Odd N) (hN3 : 3 ≤ N) :
    CompleteEdgeColoring (Fin N) (Fin ((N - 1) / 2)) := by
  let vz : Fin N ≃ ZMod N := ZMod.finEquiv N
  let cd : CanonicalDiff N ≃ Fin ((N - 1) / 2) :=
    canonicalDiffEquivFin N hOdd
  let κz := cyclicDifferenceColoringZMod hOdd hN3
  refine {
    color := fun x y => cd (κz.color (vz x) (vz y))
    color_symm := ?_ }
  intro x y
  simp [κz, cd, vz, CompleteEdgeColoring.color_symm]

def CompleteEdgeColoring.pullbackEquiv
    {V C V' C' : Type*} (eV : V' ≃ V) (eC : C' ≃ C)
    (κ : CompleteEdgeColoring V C) : CompleteEdgeColoring V' C' where
  color v w := eC.symm (κ.color (eV v) (eV w))
  color_symm v w := by simp [κ.color_symm]

lemma CompleteEdgeColoring.colorDegree_pullbackEquiv
    {V C V' C' : Type*} [Fintype V] [Fintype C]
    [Fintype V'] [Fintype C'] [DecidableEq V] [DecidableEq C]
    [DecidableEq V'] [DecidableEq C']
    (eV : V' ≃ V) (eC : C' ≃ C) (κ : CompleteEdgeColoring V C)
    (v : V') (c : C') :
    (CompleteEdgeColoring.pullbackEquiv eV eC κ).colorDegree v c =
      κ.colorDegree (eV v) (eC c) := by
  classical
  let s' : Finset V' :=
    ((Finset.univ.erase v).filter
      (fun w => (CompleteEdgeColoring.pullbackEquiv eV eC κ).color v w = c))
  let s : Finset V :=
    ((Finset.univ.erase (eV v)).filter
      (fun w => κ.color (eV v) w = eC c))
  have hs : s'.card = s.card := by
    apply Finset.card_bij (fun w _ => eV w)
    · intro w hw
      have hw' := Finset.mem_filter.mp hw
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · simp only [Finset.mem_erase, Finset.mem_univ, and_true]
        intro h
        exact (Finset.mem_erase.mp hw'.1).1 (eV.injective h)
      · have hc := congrArg eC hw'.2
        simpa [CompleteEdgeColoring.pullbackEquiv] using hc
    · intro w₁ hw₁ w₂ hw₂ heq
      exact eV.injective heq
    · intro z hz
      have hz' := Finset.mem_filter.mp hz
      refine ⟨eV.symm z, ?_, eV.apply_symm_apply z⟩
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · simp only [Finset.mem_erase, Finset.mem_univ, and_true]
        intro h
        apply (Finset.mem_erase.mp hz'.1).1
        simpa using congrArg eV h
      · have hc := congrArg eC.symm hz'.2
        simpa [CompleteEdgeColoring.pullbackEquiv] using hc
  change s'.card = s.card
  exact hs

lemma cyclicDifferenceColoringFin_colorDegree
    {N : ℕ} [NeZero N] (hOdd : Odd N) (hN3 : 3 ≤ N)
    (x : Fin N) (c : Fin ((N - 1) / 2)) :
    (cyclicDifferenceColoringFin hOdd hN3).colorDegree x c = 2 := by
  let vz : Fin N ≃ ZMod N := ZMod.finEquiv N
  let cd : CanonicalDiff N ≃ Fin ((N - 1) / 2) :=
    canonicalDiffEquivFin N hOdd
  let κz := cyclicDifferenceColoringZMod hOdd hN3
  let κf := CompleteEdgeColoring.pullbackEquiv vz cd.symm κz
  have hdeg : κf.colorDegree x c = κz.colorDegree (vz x) (cd.symm c) := by
    exact CompleteEdgeColoring.colorDegree_pullbackEquiv vz cd.symm κz x c
  have hz := cyclicDifferenceColoringZMod_colorDegree hOdd hN3
    (vz x) (cd.symm c)
  simpa [cyclicDifferenceColoringFin, κf, vz, cd, κz,
    CompleteEdgeColoring.pullbackEquiv] using hdeg.trans hz

end Erdos811
