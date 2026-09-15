import Erdos811Definitions
import CyclicDifference
import LexAmplification
import ProbabilisticPairing
import RainbowSet

/-!
# q ≥ 12 probabilistic pairing bound

This file records the exact rational checkpoint, the fixed-set pairing count,
the free cyclic translation orbit, and the finite first-moment extraction. The
resulting witness theorem is used by the FC-side all-cliques target. The
`36*q / 2^q` tail bound is retained as a readable arithmetic checkpoint.
-/

namespace Erdos811

noncomputable section
local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/- Unordered non-diagonal pairs of q vertices.  This is the finite index type
   used to enumerate the `q.choose 2` edge differences of a q-set. -/
abbrev CyclicEdgePair (q : ℕ) := {z : Sym2 (Fin q) // ¬ z.IsDiag}

noncomputable def cyclicEdgePairEquivFin (q : ℕ) :
    Fin (q.choose 2) ≃ CyclicEdgePair q :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin]
    simpa using (Sym2.card_subtype_not_diag (α := Fin q)).symm)

/- The colour of an unordered edge of `Fin q`, after embedding its endpoints
   into a vertex set.  The `Sym2.lift` makes the choice of orientation
   irrelevant. -/
def edgeColorLift {α V C : Type*}
    (κ : CompleteEdgeColoring V C) (v : α ↪ V) : Sym2 α → C :=
  Sym2.lift ⟨fun a b => κ.color (v a) (v b), by
    intro a b
    exact κ.color_symm (v a) (v b)⟩

@[simp] lemma edgeColorLift_mk {α V C : Type*}
    (κ : CompleteEdgeColoring V C) (v : α ↪ V)
    (a b : α) : edgeColorLift κ v s(a, b) = κ.color (v a) (v b) :=
  rfl

lemma edgeColorLift_injective_on_nondiag_of_rainbow
    {q : ℕ} {V C : Type*} [DecidableEq V] [DecidableEq C]
    (κ : CompleteEdgeColoring V C) (v : Fin q ↪ V)
    (S : Finset V) (hv : ∀ a : Fin q, v a ∈ S)
    (hS : IsRainbowSet κ S) :
    Function.Injective (fun z : CyclicEdgePair q =>
      edgeColorLift κ v z.1) := by
  intro z w hcol
  by_cases hzw : z = w
  · exact hzw
  rcases z with ⟨z, hz⟩
  rcases w with ⟨w, hw⟩
  obtain ⟨⟨a, b⟩, rfl⟩ := Sym2.mk_surjective z
  obtain ⟨⟨c, d⟩, rfl⟩ := Sym2.mk_surjective w
  have hsym2 : s(a, b) ≠ s(c, d) := by
    intro h
    apply hzw
    apply Subtype.ext
    exact h
  have hab : a ≠ b := by
    intro hab
    apply hz
    simpa [hab] using (Sym2.mk_isDiag_iff (x := a) (y := b)).2 hab
  have hcd : c ≠ d := by
    intro hcd
    apply hw
    simpa [hcd] using (Sym2.mk_isDiag_iff (x := c) (y := d)).2 hcd
  have habV : v a ≠ v b := v.injective.ne hab
  have hcdV : v c ≠ v d := v.injective.ne hcd
  have hsame : ¬ SameUndirectedEdge (v a) (v b) (v c) (v d) := by
    intro hs
    apply hsym2
    rcases hs with ⟨hac, hbd⟩ | ⟨had, hbc⟩
    · rw [Sym2.eq_iff]
      left
      exact ⟨v.injective hac, v.injective hbd⟩
    · rw [Sym2.eq_iff]
      right
      exact ⟨v.injective had, v.injective hbc⟩
  have hne := hS (hv a) (hv b) (hv c) (hv d) habV hcdV hsame
  apply False.elim
  apply hne
  simpa [edgeColorLift] using hcol

lemma edgeColorLift_injective_of_factor
    {q : ℕ} {V D C : Type*} [DecidableEq V] [DecidableEq C]
    (κbase : CompleteEdgeColoring V D)
    (κfinal : CompleteEdgeColoring V C)
    (v : Fin q ↪ V) (S : Finset V) (hv : ∀ a : Fin q, v a ∈ S)
    (hS : IsRainbowSet κfinal S)
    (hfactor : ∀ z w : Sym2 (Fin q),
      edgeColorLift κbase v z = edgeColorLift κbase v w →
      edgeColorLift κfinal v z = edgeColorLift κfinal v w) :
    Function.Injective (fun z : CyclicEdgePair q =>
      edgeColorLift κbase v z.1) := by
  intro z w hzw
  by_cases h : z = w
  · exact h
  apply edgeColorLift_injective_on_nondiag_of_rainbow κfinal v S hv hS
  exact hfactor z.1 w.1 hzw

lemma card_qSubset {V : Type*} [Fintype V] (q : ℕ) :
    Fintype.card (QSubset V q) = Nat.choose (Fintype.card V) q := by
  simpa [QSubset] using (Fintype.card_finset_len (α := V) q)

/- Finite double counting: summing the number of bad q-subsets over all
samples equals summing, over q-subsets, the number of samples in which that
subset is bad.  This is the exact finite first-moment identity used by the
probabilistic construction. -/
lemma sum_filter_card_comm
    {Ω A : Type*} [Fintype Ω] [Fintype A]
    (bad : Ω → A → Prop) :
    (∑ ω : Ω,
      ((Finset.univ : Finset A).filter (bad ω)).card) =
      (∑ a : A,
        ((Finset.univ : Finset Ω).filter (fun ω => bad ω a)).card) := by
  classical
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]

lemma sum_filter_card_le
    {Ω A : Type*} [Fintype Ω] [Fintype A]
    (bad : Ω → A → Prop) (B : ℕ)
    (hbound : ∀ a : A,
      ((Finset.univ : Finset Ω).filter (fun ω => bad ω a)).card ≤ B) :
    (∑ ω : Ω,
      ((Finset.univ : Finset A).filter (bad ω)).card) ≤
      Fintype.card A * B := by
  classical
  rw [sum_filter_card_comm bad]
  calc
    (∑ a : A,
        ((Finset.univ : Finset Ω).filter (fun ω => bad ω a)).card) ≤
        ∑ _a : A, B := by
      exact Finset.sum_le_sum (fun a _ => hbound a)
    _ = Fintype.card A * B := by simp

def expectedBadOrbit (q : ℕ) : ℚ :=
  ((Nat.choose (2 * q * (q - 1) + 1) q : ℚ) /
      (2 * q * (q - 1) + 1)) *
    ((2 : ℚ) ^ (Nat.choose q 2) /
      (Nat.choose (2 * Nat.choose q 2) (Nat.choose q 2)))

/- A deliberately coarse rational majorant.  The first factor uses
   `choose_le_pow_div`, and the second uses the elementary central-binomial
   lower bound from Mathlib.  It is still strong enough at q=12 and has a
   simple geometric tail estimate. -/
def crudeExpectedBound (q : ℕ) : ℚ :=
  (((2 * q * (q - 1) + 1 : ℕ) : ℚ) ^ (q - 1) /
      (q.factorial : ℚ)) *
    ((q.choose 2 : ℚ) / (2 : ℚ) ^ (q.choose 2))

lemma choose_two_succ (q : ℕ) :
    (q + 1).choose 2 = q.choose 2 + q := by
  simpa [Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_comm]

lemma crudeExpectedBound_succ_eq (q : ℕ) (hq : 12 ≤ q) :
    crudeExpectedBound (q + 1) = crudeExpectedBound q *
      ((((2 * (q + 1) * q + 1 : ℕ) : ℚ) ^ q /
          ((2 * q * (q - 1) + 1 : ℕ) : ℚ) ^ (q - 1)) *
        (((q + 1).choose 2 : ℚ) /
          (q.choose 2 : ℚ)) /
        (((q + 1 : ℕ) : ℚ) * (2 : ℚ) ^ q)) := by
  have hq1 : 1 ≤ q := by omega
  have hm0 : q.choose 2 ≠ 0 := by
    exact (Nat.choose_pos (by omega : 2 ≤ q)).ne'
  have hqfac0 : (q.factorial : ℚ) ≠ 0 := by positivity
  have hN0 : ((2 * q * (q - 1) + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hNsucc0 : ((2 * (q + 1) * q + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hpow0 : (2 : ℚ) ^ q ≠ 0 := by positivity
  rw [crudeExpectedBound, crudeExpectedBound, choose_two_succ,
    Nat.factorial_succ, pow_add]
  rw [show q + 1 - 1 = q by omega]
  field_simp [hN0, hNsucc0, hqfac0, hm0, hpow0]
  norm_num [Nat.cast_add, Nat.cast_mul]
  ring

lemma crude_tail_lt_one :
    ∀ q : ℕ, 12 ≤ q →
      (21 : ℚ) / 10 * q * ((3 : ℚ) / 4) ^ q < 1 := by
  intro q hq
  induction q, hq using Nat.le_induction with
  | base => norm_num
  | succ q hq ih =>
      have hq3 : 3 ≤ q := by omega
      have hfac : ((q + 1 : ℕ) : ℚ) * ((3 : ℚ) / 4) ≤ q := by
        have hq3' : (3 : ℚ) ≤ q := by exact_mod_cast hq3
        rw [show ((q + 1 : ℕ) : ℚ) = (q : ℚ) + 1 by norm_num]
        nlinarith
      have hnonneg : 0 ≤ (21 : ℚ) / 10 * ((3 : ℚ) / 4) ^ q := by positivity
      calc
        (21 : ℚ) / 10 * ((q + 1 : ℕ) : ℚ) * ((3 : ℚ) / 4) ^ (q + 1) =
            ((21 : ℚ) / 10 * ((3 : ℚ) / 4) ^ q) *
              (((q + 1 : ℕ) : ℚ) * ((3 : ℚ) / 4)) := by
                rw [pow_succ]
                ring
        _ ≤ ((21 : ℚ) / 10 * ((3 : ℚ) / 4) ^ q) * q := by
              exact mul_le_mul_of_nonneg_left hfac hnonneg
        _ < 1 := by simpa [mul_comm, mul_left_comm, mul_assoc] using ih

lemma crude_N_ratio_le_three_halves (q : ℕ) (hq : 12 ≤ q) :
    (((2 * (q + 1) * q + 1 : ℕ) : ℚ) /
      ((2 * q * (q - 1) + 1 : ℕ) : ℚ)) ≤ (3 : ℚ) / 2 := by
  have hNpos : 0 < ((2 * q * (q - 1) + 1 : ℕ) : ℚ) := by positivity
  apply (div_le_iff₀ hNpos).2
  have hq' : (12 : ℚ) ≤ q := by exact_mod_cast hq
  have hcast : ((q - 1 : ℕ) : ℚ) = (q : ℚ) - 1 := by
    simp [Nat.cast_sub (by omega : 1 ≤ q)]
  norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_sub, hcast]
  nlinarith [sq_nonneg ((q : ℚ) - 5)]

lemma crude_m_ratio_div_succ (q : ℕ) (hq : 12 ≤ q) :
    (((q + 1).choose 2 : ℚ) / (q.choose 2 : ℚ)) /
      ((q + 1 : ℕ) : ℚ) = 1 / ((q - 1 : ℕ) : ℚ) := by
  have hq2 : 2 ≤ q := by omega
  have hm0 : (q.choose 2 : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hq2).ne'
  have hqm1 : (q - 1 : ℕ) ≠ 0 := by omega
  have hrelNat : (q + 1).choose 2 * (q - 1) =
      q.choose 2 * (q + 1) := by
    have hdouble : q.choose 2 * 2 = q * (q - 1) := by
      rw [Nat.choose_two_right]
      exact Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self q)
    have hms := choose_two_succ q
    calc
      (q + 1).choose 2 * (q - 1) =
          (q.choose 2 + q) * (q - 1) := by rw [hms]
      _ = q.choose 2 * (q - 1) + q * (q - 1) := by ring
      _ = q.choose 2 * (q - 1) + q.choose 2 * 2 := by rw [hdouble]
      _ = q.choose 2 * (q + 1) := by
        calc
          q.choose 2 * (q - 1) + q.choose 2 * 2 =
              q.choose 2 * ((q - 1) + 2) := by ring
          _ = q.choose 2 * (q + 1) := by
            congr 1
            omega
  have hrel : ((q + 1).choose 2 : ℚ) * ((q - 1 : ℕ) : ℚ) =
      (q.choose 2 : ℚ) * (q + 1) := by
    exact_mod_cast hrelNat
  field_simp [hm0, hqm1]
  have hcastSucc : ((q + 1 : ℕ) : ℚ) = (q : ℚ) + 1 := by norm_num
  simpa [hcastSucc] using hrel

lemma crudeExpectedBound_succ_ratio_le (q : ℕ) (hq : 12 ≤ q) :
    ((((2 * (q + 1) * q + 1 : ℕ) : ℚ) ^ q /
          ((2 * q * (q - 1) + 1 : ℕ) : ℚ) ^ (q - 1)) *
        (((q + 1).choose 2 : ℚ) /
          (q.choose 2 : ℚ)) /
        (((q + 1 : ℕ) : ℚ) * (2 : ℚ) ^ q)) ≤
      (21 : ℚ) / 10 * q * ((3 : ℚ) / 4) ^ q := by
  have hq1 : 1 ≤ q := by omega
  have hq3 : 3 ≤ q := by omega
  have hNpos : 0 < ((2 * q * (q - 1) + 1 : ℕ) : ℚ) := by positivity
  have hN0 : ((2 * q * (q - 1) + 1 : ℕ) : ℚ) ≠ 0 := hNpos.ne'
  have hNratio := crude_N_ratio_le_three_halves q hq
  have hratio :
      (((2 * (q + 1) * q + 1 : ℕ) : ℚ) /
        ((2 * q * (q - 1) + 1 : ℕ) : ℚ)) ^ q ≤
        ((3 : ℚ) / 2) ^ q := by
    exact pow_le_pow_left₀ (by positivity) hNratio q
  have hqpredpos : 0 < ((q - 1 : ℕ) : ℚ) := by
    exact_mod_cast (show 0 < q - 1 by omega)
  have hpoly :
      ((2 * q * (q - 1) + 1 : ℕ) : ℚ) /
          ((q - 1 : ℕ) : ℚ) ≤ (21 : ℚ) / 10 * q := by
    apply (div_le_iff₀ hqpredpos).2
    have hq' : (12 : ℚ) ≤ q := by exact_mod_cast hq
    have hqminus : (11 : ℚ) ≤ (q : ℚ) - 1 := by linarith
    have hprod : (132 : ℚ) ≤ (q : ℚ) * ((q : ℚ) - 1) := by
      have hp := mul_le_mul hq' hqminus (by norm_num : (0 : ℚ) ≤ 12)
        (by positivity : (0 : ℚ) ≤ q)
      norm_num at hp ⊢
      exact hp
    have hcast : ((q - 1 : ℕ) : ℚ) = (q : ℚ) - 1 := by
      simp [Nat.cast_sub (by omega : 1 ≤ q)]
    rw [hcast]
    norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_sub, hcast]
    nlinarith [hprod]
  have hmratio := crude_m_ratio_div_succ q hq
  have hpowratio :
      (((2 * (q + 1) * q + 1 : ℕ) : ℚ) ^ q /
        ((2 * q * (q - 1) + 1 : ℕ) : ℚ) ^ (q - 1)) =
        ((2 * q * (q - 1) + 1 : ℕ) : ℚ) *
          ((((2 * (q + 1) * q + 1 : ℕ) : ℚ) /
            ((2 * q * (q - 1) + 1 : ℕ) : ℚ)) ^ q) := by
    rw [div_pow]
    field_simp [hN0]
    calc
      _ = _ ^ ((q - 1) + 1) := by congr 1 <;> omega
      _ = _ := by rw [pow_succ]
  have hprod :
      ((2 * q * (q - 1) + 1 : ℕ) : ℚ) /
          ((q - 1 : ℕ) : ℚ) *
        ((((2 * (q + 1) * q + 1 : ℕ) : ℚ) /
          ((2 * q * (q - 1) + 1 : ℕ) : ℚ)) ^ q) ≤
      (21 : ℚ) / 10 * q * ((3 : ℚ) / 2) ^ q := by
    exact mul_le_mul hpoly hratio (by positivity) (by positivity)
  have hmratio' :
      (((q + 1).choose 2 : ℚ) / (q.choose 2 : ℚ)) /
          (((q + 1 : ℕ) : ℚ) * (2 : ℚ) ^ q) =
        (1 / ((q - 1 : ℕ) : ℚ)) / (2 : ℚ) ^ q := by
    have hm0 : (q.choose 2 : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega : 2 ≤ q)).ne'
    have hqsucc0 : ((q + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have hpow0 : (2 : ℚ) ^ q ≠ 0 := by positivity
    calc
      (((q + 1).choose 2 : ℚ) / (q.choose 2 : ℚ)) /
          (((q + 1 : ℕ) : ℚ) * (2 : ℚ) ^ q) =
          ((((q + 1).choose 2 : ℚ) / (q.choose 2 : ℚ)) /
            ((q + 1 : ℕ) : ℚ)) / (2 : ℚ) ^ q := by
              field_simp [hm0, hqsucc0, hpow0]
      _ = (1 / ((q - 1 : ℕ) : ℚ)) / (2 : ℚ) ^ q := by
        simpa using congrArg (fun x : ℚ => x / (2 : ℚ) ^ q) hmratio
  calc
    ((((2 * (q + 1) * q + 1 : ℕ) : ℚ) ^ q /
          ((2 * q * (q - 1) + 1 : ℕ) : ℚ) ^ (q - 1)) *
        (((q + 1).choose 2 : ℚ) /
          (q.choose 2 : ℚ)) /
        (((q + 1 : ℕ) : ℚ) * (2 : ℚ) ^ q)) =
        (((2 * q * (q - 1) + 1 : ℕ) : ℚ) /
          ((q - 1 : ℕ) : ℚ) *
          ((((2 * (q + 1) * q + 1 : ℕ) : ℚ) /
            ((2 * q * (q - 1) + 1 : ℕ) : ℚ)) ^ q)) /
          (2 : ℚ) ^ q := by
      rw [hpowratio, mul_div_assoc, hmratio']
      have hqsucc0 : ((q + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      have hpow0 : (2 : ℚ) ^ q ≠ 0 := by positivity
      field_simp [hN0, hqpredpos.ne', hqsucc0, hpow0]
    _ ≤ ((21 : ℚ) / 10 * q * ((3 : ℚ) / 2) ^ q) /
          (2 : ℚ) ^ q := by
      exact div_le_div_of_nonneg_right hprod (by positivity)
    _ = (21 : ℚ) / 10 * q * ((3 : ℚ) / 4) ^ q := by
      have hpowdiv : ((3 : ℚ) / 2) ^ q / (2 : ℚ) ^ q =
          ((3 : ℚ) / 4) ^ q := by
        rw [← div_pow]
        congr 1
        norm_num
      calc
        (21 : ℚ) / 10 * q * ((3 : ℚ) / 2) ^ q / (2 : ℚ) ^ q =
            ((21 : ℚ) / 10 * q) *
              (((3 : ℚ) / 2) ^ q / (2 : ℚ) ^ q) := by ring
        _ = (21 : ℚ) / 10 * q * ((3 : ℚ) / 4) ^ q := by rw [hpowdiv]

lemma crudeExpectedBound_succ_le (q : ℕ) (hq : 12 ≤ q) :
    crudeExpectedBound (q + 1) ≤ crudeExpectedBound q *
      ((21 : ℚ) / 10 * q * ((3 : ℚ) / 4) ^ q) := by
  rw [crudeExpectedBound_succ_eq q hq]
  have hcrude : 0 ≤ crudeExpectedBound q := by
    unfold crudeExpectedBound
    positivity
  exact mul_le_mul_of_nonneg_left
    (crudeExpectedBound_succ_ratio_le q hq) hcrude

lemma expectedBadOrbit_le_crudeExpectedBound (q : ℕ) (hq : 12 ≤ q) :
    expectedBadOrbit q ≤ crudeExpectedBound q := by
  let N : ℕ := 2 * q * (q - 1) + 1
  let m : ℕ := q.choose 2
  have hq1 : 1 ≤ q := by omega
  have hNpos : 0 < (N : ℚ) := by
    dsimp [N]
    positivity
  have hfacpos : 0 < (q.factorial : ℚ) := by positivity
  have hchooseNat := Nat.choose_le_pow_div (α := ℚ) q N
  have hchoose : (N.choose q : ℚ) ≤
      (N : ℚ) ^ q / (q.factorial : ℚ) := by
    exact_mod_cast hchooseNat
  have hfirst : (N.choose q : ℚ) / N ≤
      (N : ℚ) ^ (q - 1) / (q.factorial : ℚ) := by
    have hdiv := div_le_div_of_nonneg_right hchoose (le_of_lt hNpos)
    have hpow : (N : ℚ) ^ q = (N : ℚ) ^ (q - 1) * N := by
      rw [show q = (q - 1) + 1 by omega, pow_succ]
      congr 1
    dsimp [N] at hdiv ⊢
    calc
      (N.choose q : ℚ) / N ≤
          ((N : ℚ) ^ q / (q.factorial : ℚ)) / N := hdiv
      _ = (N : ℚ) ^ (q - 1) / (q.factorial : ℚ) := by
        rw [hpow]
        field_simp
  have hm4 : 4 ≤ m := by
    dsimp [m]
    rw [Nat.choose_two_right]
    have hq8 : 8 ≤ q := by omega
    have hq1' : 1 ≤ q - 1 := by omega
    apply (Nat.le_div_iff_mul_le (by decide)).2
    simpa [Nat.mul_comm] using Nat.mul_le_mul hq8 hq1'
  have hcentralNat := Nat.four_pow_lt_mul_centralBinom m hm4
  have hcentral : (4 : ℚ) ^ m <
      (m : ℚ) * (Nat.choose (2 * m) m : ℚ) := by
    exact_mod_cast hcentralNat
  have hmpowpos : 0 < (2 : ℚ) ^ m := by positivity
  have hcentpos : 0 < (Nat.choose (2 * m) m : ℚ) := by
    exact_mod_cast (Nat.choose_pos (by omega : m ≤ 2 * m))
  have hsecond : (2 : ℚ) ^ m / (Nat.choose (2 * m) m : ℚ) ≤
      (m : ℚ) / (2 : ℚ) ^ m := by
    apply (div_le_iff₀ hcentpos).2
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hmpowpos).2
    have hpow4 : (4 : ℚ) ^ m = (2 : ℚ) ^ m * (2 : ℚ) ^ m := by
      rw [show (4 : ℚ) = 2 * 2 by norm_num, mul_pow]
    rw [← hpow4]
    exact hcentral.le
  have hprod := mul_le_mul hfirst hsecond (by positivity) (by positivity)
  have hcast : ((q - 1 : ℕ) : ℚ) = (q : ℚ) - 1 := by
    simp [Nat.cast_sub (by omega : 1 ≤ q)]
  simpa [expectedBadOrbit, crudeExpectedBound, N, m, hcast] using hprod

lemma probabilistic_order_mod_edgeCount (q : ℕ) (hq : 4 ≤ q) :
    (2 * q * (q - 1) + 1) %
        edgeCount (SimpleGraph.completeGraph (Fin q)) = 1 := by
  rw [edgeCount_completeGraph_fin, Nat.choose_two_right]
  have hq1 : 3 ≤ q - 1 := by omega
  have hprod6 : 6 ≤ q * (q - 1) := by
    nlinarith
  have hprod : 2 ≤ q * (q - 1) := by
    have hmul := Nat.mul_le_mul hq hq1
    omega
  have hpos : 0 < q * (q - 1) / 2 := Nat.div_pos hprod (by decide)
  have hdouble : q * (q - 1) / 2 * 2 = q * (q - 1) :=
    Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self q)
  have hfour : 2 * q * (q - 1) = 4 * (q * (q - 1) / 2) := by
    calc
      2 * q * (q - 1) = 2 * (q * (q - 1)) := by ring
      _ = 2 * (q * (q - 1) / 2 * 2) := by rw [hdouble]
      _ = 4 * (q * (q - 1) / 2) := by ring
  rw [hfour]
  have hm : 1 < q * (q - 1) / 2 := by omega
  simp [Nat.add_mod, Nat.mul_mod, hpos.ne', Nat.mod_eq_of_lt hm]

def HasProbabilisticPairingWitness (q : ℕ) : Prop :=
  ∃ κ : CompleteEdgeColoring
      (Fin (2 * q * (q - 1) + 1))
      (Fin (edgeCount (SimpleGraph.completeGraph (Fin q)))),
    κ.IsBalanced ∧
      ¬ HasRainbowCopy (SimpleGraph.completeGraph (Fin q)) κ

lemma probabilistic_order_odd (q : ℕ) :
    Odd (2 * q * (q - 1) + 1) := by
  refine ⟨q * (q - 1), ?_⟩
  ring

lemma probabilistic_difference_class_count (q : ℕ) :
    ((2 * q * (q - 1) + 1 - 1) / 2) = 2 * (q.choose 2) := by
  rw [Nat.choose_two_right]
  have hdiv := Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self q)
  have hmul : 2 * q * (q - 1) = 2 * (q * (q - 1)) := by ring
  have harg : 2 * q * (q - 1) + 1 - 1 =
      2 * (q * (q - 1)) := by rw [hmul]; omega
  calc
    (2 * q * (q - 1) + 1 - 1) / 2 =
        (2 * (q * (q - 1))) / 2 := by rw [harg]
    _ = q * (q - 1) := Nat.mul_div_cancel_left _ (by decide)
    _ = 2 * (q * (q - 1) / 2) := by
      simpa [Nat.mul_comm] using hdiv.symm

noncomputable def cyclicBaseColoring (q : ℕ) (hq : 12 ≤ q) :
    CompleteEdgeColoring
      (Fin (2 * q * (q - 1) + 1))
      (Fin ((q.choose 2) * 2)) := by
  let hOdd : Odd (2 * q * (q - 1) + 1) := probabilistic_order_odd q
  have hq1 : 1 ≤ q - 1 := by omega
  have hN3 : 3 ≤ 2 * q * (q - 1) + 1 := by nlinarith
  let hhalf : (2 * q * (q - 1) + 1 - 1) / 2 =
      (q.choose 2) * 2 := by
    calc
      (2 * q * (q - 1) + 1 - 1) / 2 = 2 * (q.choose 2) :=
        probabilistic_difference_class_count q
      _ = (q.choose 2) * 2 := by ring
  let eC : Fin ((2 * q * (q - 1) + 1 - 1) / 2) ≃
      Fin ((q.choose 2) * 2) := finCongr hhalf
  exact CompleteEdgeColoring.pullbackEquiv (Equiv.refl _) eC.symm
    (cyclicDifferenceColoringFin hOdd hN3)

lemma cyclicBaseColoring_colorDegree (q : ℕ) (hq : 12 ≤ q)
    (x : Fin (2 * q * (q - 1) + 1)) (d : Fin ((q.choose 2) * 2)) :
    (cyclicBaseColoring q hq).colorDegree x d = 2 := by
  let hOdd : Odd (2 * q * (q - 1) + 1) := probabilistic_order_odd q
  have hq1 : 1 ≤ q - 1 := by omega
  have hN3 : 3 ≤ 2 * q * (q - 1) + 1 := by nlinarith
  let hhalf : (2 * q * (q - 1) + 1 - 1) / 2 =
      (q.choose 2) * 2 := by
    calc
      (2 * q * (q - 1) + 1 - 1) / 2 = 2 * (q.choose 2) :=
        probabilistic_difference_class_count q
      _ = (q.choose 2) * 2 := by ring
  let eC : Fin ((2 * q * (q - 1) + 1 - 1) / 2) ≃
      Fin ((q.choose 2) * 2) := finCongr hhalf
  let κf := CompleteEdgeColoring.pullbackEquiv (Equiv.refl _) eC.symm
    (cyclicDifferenceColoringFin hOdd hN3)
  have hdeg : κf.colorDegree x d =
      (cyclicDifferenceColoringFin hOdd hN3).colorDegree x (eC.symm d) := by
    exact CompleteEdgeColoring.colorDegree_pullbackEquiv
      (Equiv.refl _) eC.symm (cyclicDifferenceColoringFin hOdd hN3) x d
  have hz := cyclicDifferenceColoringFin_colorDegree hOdd hN3 x (eC.symm d)
  simpa [cyclicBaseColoring, κf, hOdd, hN3, hhalf, eC,
    CompleteEdgeColoring.pullbackEquiv] using hdeg.trans hz

noncomputable def cyclicPairingSample (q : ℕ) (hq : 12 ≤ q)
    (σ : Equiv.Perm (Fin ((q.choose 2) * 2))) :
    CompleteEdgeColoring
      (Fin (2 * q * (q - 1) + 1)) (Fin (q.choose 2)) :=
  permutationPairingColoring (q.choose 2) (cyclicBaseColoring q hq) σ

lemma cyclicPairingSample_edgeColorLift_eq
    (q : ℕ) (hq : 12 ≤ q)
    (v : Fin q ↪ Fin (2 * q * (q - 1) + 1))
    (σ : Equiv.Perm (Fin ((q.choose 2) * 2)))
    (z : Sym2 (Fin q)) :
    edgeColorLift (cyclicPairingSample q hq σ) v z =
      (permutationPairingMap (q.choose 2) σ).color
        (edgeColorLift (cyclicBaseColoring q hq) v z) := by
  refine Sym2.inductionOn z ?_
  intro a b
  rfl

def cyclicBaseEdgeClass
    (q : ℕ) (hq : 12 ≤ q)
    (v : Fin q ↪ Fin (2 * q * (q - 1) + 1))
    (z : CyclicEdgePair q) : Fin ((q.choose 2) * 2) :=
  edgeColorLift (cyclicBaseColoring q hq) v z.1

noncomputable def cyclicBaseEdgeEmbedding
    (q : ℕ) (hq : 12 ≤ q)
    (v : Fin q ↪ Fin (2 * q * (q - 1) + 1))
    (hbase : Function.Injective (cyclicBaseEdgeClass q hq v)) :
    Fin (q.choose 2) ↪ Fin ((q.choose 2) * 2) :=
  ⟨fun i => cyclicBaseEdgeClass q hq v (cyclicEdgePairEquivFin q i),
    hbase.comp (cyclicEdgePairEquivFin q).injective⟩

lemma cyclicBaseEdgeEmbedding_pairSeparated_of_rainbow
    (q : ℕ) (hq : 12 ≤ q)
    (v : Fin q ↪ Fin (2 * q * (q - 1) + 1))
    (S : Finset (Fin (2 * q * (q - 1) + 1)))
    (hv : ∀ a : Fin q, v a ∈ S)
    (hbase : Function.Injective (cyclicBaseEdgeClass q hq v))
    (σ : Equiv.Perm (Fin ((q.choose 2) * 2)))
    (hS : IsRainbowSet (cyclicPairingSample q hq σ) S) :
    PairSeparated (q.choose 2)
      (cyclicBaseEdgeEmbedding q hq v hbase) σ := by
  change Function.Injective (fun i : Fin (q.choose 2) =>
    (permutationPairingMap (q.choose 2) σ).color
      ((cyclicBaseEdgeEmbedding q hq v hbase) i)
  )
  have hfinal : Function.Injective (fun z : CyclicEdgePair q =>
      edgeColorLift (cyclicPairingSample q hq σ) v z.1) :=
    edgeColorLift_injective_on_nondiag_of_rainbow
      (cyclicPairingSample q hq σ) v S hv hS
  intro i j hij
  have hz : edgeColorLift (cyclicPairingSample q hq σ) v
      (cyclicEdgePairEquivFin q i).1 =
      edgeColorLift (cyclicPairingSample q hq σ) v
        (cyclicEdgePairEquivFin q j).1 := by
    rw [cyclicPairingSample_edgeColorLift_eq,
      cyclicPairingSample_edgeColorLift_eq]
    exact hij
  exact (cyclicEdgePairEquivFin q).injective (hfinal hz)

lemma cyclicBaseEdgeClass_injective_of_rainbow
    (q : ℕ) (hq : 12 ≤ q)
    (v : Fin q ↪ Fin (2 * q * (q - 1) + 1))
    (S : Finset (Fin (2 * q * (q - 1) + 1)))
    (hv : ∀ a : Fin q, v a ∈ S)
    (σ : Equiv.Perm (Fin ((q.choose 2) * 2)))
    (hS : IsRainbowSet (cyclicPairingSample q hq σ) S) :
    Function.Injective (cyclicBaseEdgeClass q hq v) := by
  apply edgeColorLift_injective_of_factor
    (cyclicBaseColoring q hq) (cyclicPairingSample q hq σ)
    v S hv hS
  intro z w hzw
  rw [cyclicPairingSample_edgeColorLift_eq,
    cyclicPairingSample_edgeColorLift_eq, hzw]

noncomputable def cyclicTranslateFin {N : ℕ} [NeZero N]
    (t : Fin N) (x : Fin N) : Fin N :=
  (ZMod.finEquiv N).symm
    ((ZMod.finEquiv N t) + (ZMod.finEquiv N x))

lemma cyclicTranslateFin_injective {N : ℕ} [NeZero N]
    (t : Fin N) : Function.Injective (cyclicTranslateFin t) := by
  intro x y h
  apply (ZMod.finEquiv N).injective
  have hz := congrArg (fun z : Fin N => (ZMod.finEquiv N) z) h
  simpa [cyclicTranslateFin] using hz

lemma cyclicBaseColoring_translate (q : ℕ) (hq : 12 ≤ q)
    (t x y : Fin (2 * q * (q - 1) + 1)) :
    (cyclicBaseColoring q hq).color (cyclicTranslateFin t x)
      (cyclicTranslateFin t y) =
      (cyclicBaseColoring q hq).color x y := by
  let hOdd : Odd (2 * q * (q - 1) + 1) := probabilistic_order_odd q
  have hq1 : 1 ≤ q - 1 := by omega
  have hN3 : 3 ≤ 2 * q * (q - 1) + 1 := by nlinarith
  let hhalf : (2 * q * (q - 1) + 1 - 1) / 2 =
      (q.choose 2) * 2 := by
    calc
      (2 * q * (q - 1) + 1 - 1) / 2 = 2 * (q.choose 2) :=
        probabilistic_difference_class_count q
      _ = (q.choose 2) * 2 := by ring
  let eC : Fin ((2 * q * (q - 1) + 1 - 1) / 2) ≃
      Fin ((q.choose 2) * 2) := finCongr hhalf
  let cd : CanonicalDiff (2 * q * (q - 1) + 1) ≃
      Fin ((2 * q * (q - 1) + 1 - 1) / 2) :=
    canonicalDiffEquivFin _ hOdd
  let vz : Fin (2 * q * (q - 1) + 1) ≃
      ZMod (2 * q * (q - 1) + 1) :=
    (ZMod.finEquiv (2 * q * (q - 1) + 1)).toEquiv
  have hz := cyclicDifferenceColoringZMod_translate hOdd hN3
    (vz t) (vz x) (vz y)
  have hzd := congrArg cd hz
  simpa [cyclicBaseColoring, cyclicDifferenceColoringFin,
    CompleteEdgeColoring.pullbackEquiv, cyclicTranslateFin,
    hOdd, hN3, hhalf, eC, cd, vz] using congrArg eC hzd

lemma cyclicPairingSample_translate (q : ℕ) (hq : 12 ≤ q)
    (σ : Equiv.Perm (Fin ((q.choose 2) * 2)))
    (t x y : Fin (2 * q * (q - 1) + 1)) :
    (cyclicPairingSample q hq σ).color (cyclicTranslateFin t x)
      (cyclicTranslateFin t y) =
    (cyclicPairingSample q hq σ).color x y := by
  unfold cyclicPairingSample permutationPairingColoring pairedColoring
  change (permutationPairingMap (q.choose 2) σ).color
      ((cyclicBaseColoring q hq).color (cyclicTranslateFin t x)
        (cyclicTranslateFin t y)) =
    (permutationPairingMap (q.choose 2) σ).color
      ((cyclicBaseColoring q hq).color x y)
  rw [cyclicBaseColoring_translate q hq t x y]

/- Translating every vertex of a finite set preserves the rainbow property.
This is the set-level form needed to turn one rainbow q-set into its whole
translation orbit. -/
lemma cyclicPairingSample_translate_isRainbowSet
    (q : ℕ) (hq : 12 ≤ q)
    (σ : Equiv.Perm (Fin ((q.choose 2) * 2)))
    (t : Fin (2 * q * (q - 1) + 1))
    (S : Finset (Fin (2 * q * (q - 1) + 1)))
    (hS : IsRainbowSet (cyclicPairingSample q hq σ) S) :
    IsRainbowSet (cyclicPairingSample q hq σ)
      (S.map ⟨cyclicTranslateFin t, cyclicTranslateFin_injective t⟩) := by
  intro a b c d ha hb hc hd hab hcd hsame heq
  obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_map.mp ha
  obtain ⟨b₀, hb₀, rfl⟩ := Finset.mem_map.mp hb
  obtain ⟨c₀, hc₀, rfl⟩ := Finset.mem_map.mp hc
  obtain ⟨d₀, hd₀, rfl⟩ := Finset.mem_map.mp hd
  have hab₀ : a₀ ≠ b₀ := by
    intro h
    apply hab
    exact congrArg (cyclicTranslateFin t) h
  have hcd₀ : c₀ ≠ d₀ := by
    intro h
    apply hcd
    exact congrArg (cyclicTranslateFin t) h
  have hsame₀ : ¬ SameUndirectedEdge a₀ b₀ c₀ d₀ := by
    intro h
    apply hsame
    rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨congrArg (cyclicTranslateFin t) h₁,
        congrArg (cyclicTranslateFin t) h₂⟩
    · exact Or.inr ⟨congrArg (cyclicTranslateFin t) h₁,
        congrArg (cyclicTranslateFin t) h₂⟩
  apply hS ha₀ hb₀ hc₀ hd₀ hab₀ hcd₀ hsame₀
  calc
    (cyclicPairingSample q hq σ).color a₀ b₀ =
        (cyclicPairingSample q hq σ).color
          (cyclicTranslateFin t a₀) (cyclicTranslateFin t b₀) := by
      symm
      exact cyclicPairingSample_translate q hq σ t a₀ b₀
    _ = (cyclicPairingSample q hq σ).color
        (cyclicTranslateFin t c₀) (cyclicTranslateFin t d₀) := heq
    _ = (cyclicPairingSample q hq σ).color c₀ d₀ :=
      cyclicPairingSample_translate q hq σ t c₀ d₀

lemma cyclicTranslateFinset_card
    {N : ℕ} [NeZero N] (t : Fin N)
    (S : Finset (Fin N)) :
    (S.map ⟨cyclicTranslateFin t, cyclicTranslateFin_injective t⟩).card = S.card := by
  exact Finset.card_map _

noncomputable def cyclicTranslateQSubset
    (q : ℕ) (hq : 12 ≤ q) (t : Fin (2 * q * (q - 1) + 1)) :
    QSubset (Fin (2 * q * (q - 1) + 1)) q →
      QSubset (Fin (2 * q * (q - 1) + 1)) q := fun S =>
    ⟨S.1.map ⟨cyclicTranslateFin t, cyclicTranslateFin_injective t⟩,
      by
        rw [cyclicTranslateFinset_card]
        exact S.2⟩

lemma cyclicTranslateQSubset_isRainbow
    (q : ℕ) (hq : 12 ≤ q)
    (σ : Equiv.Perm (Fin ((q.choose 2) * 2)))
    (t : Fin (2 * q * (q - 1) + 1))
    (S : QSubset (Fin (2 * q * (q - 1) + 1)) q)
    (hS : IsRainbowSet (cyclicPairingSample q hq σ) S.1) :
    IsRainbowSet (cyclicPairingSample q hq σ)
      ((cyclicTranslateQSubset q hq t S).1) := by
  exact cyclicPairingSample_translate_isRainbowSet q hq σ t S.1 hS

abbrev CyclicRainbowQSubset (q : ℕ) (hq : 12 ≤ q)
    (σ : Equiv.Perm (Fin ((q.choose 2) * 2))) :=
  {S : QSubset (Fin (2 * q * (q - 1) + 1)) q //
    IsRainbowSet (cyclicPairingSample q hq σ) S.1}

/- Abstract orbit-count instantiation.  The only arithmetic/group-theoretic
   input still needed is freeness of translations on a rainbow q-set. -/
lemma cyclicRainbowQSubsetCount_ge_of_translation_free
    (q : ℕ) (hq : 12 ≤ q)
    (σ : Equiv.Perm (Fin ((q.choose 2) * 2)))
    (hfree : ∀ S : CyclicRainbowQSubset q hq σ,
      Function.Injective (fun t : Fin (2 * q * (q - 1) + 1) =>
        cyclicTranslateQSubset q hq t S.1)) :
    ∀ S : CyclicRainbowQSubset q hq σ,
      2 * q * (q - 1) + 1 ≤
        rainbowQSubsetCount (q := q) (cyclicPairingSample q hq σ) := by
  intro S
  letI : Fintype (CyclicRainbowQSubset q hq σ) :=
    Fintype.subtype
      ((Finset.univ : Finset (QSubset (Fin (2 * q * (q - 1) + 1)) q)).filter
        (fun T => IsRainbowSet (cyclicPairingSample q hq σ) T.1)) (by simp)
  let orbit : Fin (2 * q * (q - 1) + 1) → CyclicRainbowQSubset q hq σ := fun t =>
    ⟨cyclicTranslateQSubset q hq t S.1,
      cyclicTranslateQSubset_isRainbow q hq σ t S.1 S.2⟩
  have horbit : Function.Injective orbit := by
    intro t u htu
    apply hfree S
    exact congrArg Subtype.val htu
  have hcard := Fintype.card_le_of_injective orbit horbit
  have hcard' : 2 * q * (q - 1) + 1 ≤
      rainbowQSubsetCount (q := q) (cyclicPairingSample q hq σ) := by
    simpa [rainbowQSubsetCount] using hcard
  exact hcard'

lemma cyclicRainbowQSubsetCount_zero_or_ge_of_translation_free
    (q : ℕ) (hq : 12 ≤ q)
    (σ : Equiv.Perm (Fin ((q.choose 2) * 2)))
    (hfree : ∀ S : CyclicRainbowQSubset q hq σ,
      Function.Injective (fun t : Fin (2 * q * (q - 1) + 1) =>
        cyclicTranslateQSubset q hq t S.1)) :
    rainbowQSubsetCount (q := q) (cyclicPairingSample q hq σ) = 0 ∨
      2 * q * (q - 1) + 1 ≤
        rainbowQSubsetCount (q := q) (cyclicPairingSample q hq σ) := by
  classical
  letI : Fintype (CyclicRainbowQSubset q hq σ) :=
    Fintype.subtype
      ((Finset.univ : Finset (QSubset (Fin (2 * q * (q - 1) + 1)) q)).filter
        (fun T => IsRainbowSet (cyclicPairingSample q hq σ) T.1)) (by simp)
  by_cases hz : rainbowQSubsetCount (q := q)
      (cyclicPairingSample q hq σ) = 0
  · exact Or.inl hz
  · right
    have hpos : 0 < rainbowQSubsetCount (q := q)
        (cyclicPairingSample q hq σ) := Nat.pos_of_ne_zero hz
    have hne : Nonempty (CyclicRainbowQSubset q hq σ) := by
      apply Fintype.card_pos_iff.mp
      simpa [rainbowQSubsetCount] using hpos
    obtain ⟨S⟩ := hne
    exact cyclicRainbowQSubsetCount_ge_of_translation_free q hq σ hfree S

lemma cyclicTranslateQSubset_injective
    (q : ℕ) (hq : 12 ≤ q) (t : Fin (2 * q * (q - 1) + 1)) :
    Function.Injective (cyclicTranslateQSubset q hq t) := by
  intro S T hST
  apply Subtype.ext
  apply Finset.map_injective
  exact congrArg Subtype.val hST

lemma cyclic_vertex_coprime (q : ℕ) :
    Nat.Coprime q (2 * q * (q - 1) + 1) := by
  have h := (Nat.coprime_add_mul_left_right q 1 (2 * (q - 1))).2 (by simp)
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.add_comm] using h

lemma cyclicTranslateQSubset_injective_on_fixed
    (q : ℕ) (hq : 12 ≤ q)
    (S : QSubset (Fin (2 * q * (q - 1) + 1)) q)
    (hcop : Nat.Coprime q (2 * q * (q - 1) + 1)) :
    Function.Injective (fun t : Fin (2 * q * (q - 1) + 1) =>
      cyclicTranslateQSubset q hq t S) := by
  intro t u htu
  let N := 2 * q * (q - 1) + 1
  let vz : Fin N ≃ ZMod N := ZMod.finEquiv N
  let et : Fin N ↪ Fin N :=
    ⟨cyclicTranslateFin t, cyclicTranslateFin_injective t⟩
  let eu : Fin N ↪ Fin N :=
    ⟨cyclicTranslateFin u, cyclicTranslateFin_injective u⟩
  have hmap : S.1.map et = S.1.map eu := by
    simpa [et, eu, cyclicTranslateQSubset] using congrArg Subtype.val htu
  have hsum :
      (∑ x ∈ S.1.map et, vz x) = (∑ x ∈ S.1.map eu, vz x) := by
    exact congrArg (fun T : Finset (Fin N) => ∑ x ∈ T, vz x) hmap
  have hsum' :
      (∑ x ∈ S.1, (vz t + vz x)) =
        (∑ x ∈ S.1, (vz u + vz x)) := by
    have hsum_map :
        (∑ x ∈ S.1, vz (et x)) =
          (∑ x ∈ S.1, vz (eu x)) := by
      simpa only [Finset.sum_map] using hsum
    simpa [et, eu, vz, cyclicTranslateFin] using hsum_map
  have hmul : (q : ZMod N) * vz t = (q : ZMod N) * vz u := by
    simpa [Finset.sum_add_distrib, S.2, N, vz, nsmul_eq_mul] using hsum'
  have hvz : vz t = vz u :=
    (ZMod.unitOfCoprime q hcop).isUnit.mul_left_cancel hmul
  exact vz.injective hvz

lemma cyclicTranslateQSubset_injective_on_fixed_auto
    (q : ℕ) (hq : 12 ≤ q)
    (S : QSubset (Fin (2 * q * (q - 1) + 1)) q) :
    Function.Injective (fun t : Fin (2 * q * (q - 1) + 1) =>
      cyclicTranslateQSubset q hq t S) := by
  exact cyclicTranslateQSubset_injective_on_fixed q hq S (cyclic_vertex_coprime q)

lemma cyclicRainbowQSubsetCount_zero_or_ge_auto
    (q : ℕ) (hq : 12 ≤ q)
    (σ : Equiv.Perm (Fin ((q.choose 2) * 2))) :
    rainbowQSubsetCount (q := q) (cyclicPairingSample q hq σ) = 0 ∨
      2 * q * (q - 1) + 1 ≤
        rainbowQSubsetCount (q := q) (cyclicPairingSample q hq σ) := by
  apply cyclicRainbowQSubsetCount_zero_or_ge_of_translation_free q hq σ
  intro S
  exact cyclicTranslateQSubset_injective_on_fixed_auto q hq S.1

lemma probabilistic_vertex_order_as_four_mul_choose (q : ℕ) :
    2 * q * (q - 1) + 1 = 4 * (q.choose 2) + 1 := by
  rw [Nat.choose_two_right]
  have hdiv := Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self q)
  have hprod : q * (q - 1) = 2 * (q * (q - 1) / 2) := by
    simpa [Nat.mul_comm] using hdiv.symm
  calc
    2 * q * (q - 1) + 1 = 2 * (q * (q - 1)) + 1 := by ring
    _ = 2 * (2 * (q * (q - 1) / 2)) + 1 := by
      exact congrArg (fun z : ℕ => 2 * z + 1) hprod
    _ = 4 * (q * (q - 1) / 2) + 1 := by ring

lemma probabilistic_vertex_color_ratio (q : ℕ) (hq : 12 ≤ q) :
    Fintype.card (Fin (2 * q * (q - 1) + 1)) / (q.choose 2) = 4 := by
  have hm2 : 2 ≤ q.choose 2 := by
    rw [Nat.choose_two_right]
    apply (Nat.le_div_iff_mul_le (by decide)).2
    have hq4 : 4 ≤ q := by omega
    have hq1 : 1 ≤ q - 1 := by omega
    simpa using (Nat.mul_le_mul hq4 hq1)
  rw [Fintype.card_fin, probabilistic_vertex_order_as_four_mul_choose]
  apply Nat.div_eq_of_lt_le
  · omega
  · nlinarith

lemma cyclicPairingSample_isBalanced (q : ℕ) (hq : 12 ≤ q)
    (σ : Equiv.Perm (Fin ((q.choose 2) * 2))) :
    (cyclicPairingSample q hq σ).IsBalanced := by
  unfold cyclicPairingSample
  apply permutationPairingColoring_isBalanced (q.choose 2)
    (cyclicBaseColoring q hq)
    (cyclicBaseColoring_colorDegree q hq)
  exact probabilistic_vertex_color_ratio q hq

lemma cyclicPairingSample_isBalanced_for_edgeCount (q : ℕ) (hq : 12 ≤ q)
    (σ : Equiv.Perm (Fin ((q.choose 2) * 2))) :
    (cyclicPairingSample q hq σ).IsBalanced :=
  cyclicPairingSample_isBalanced q hq σ

/- The fixed-set counting interface.  Once an edge-class embedding `e` and
   the rainbow-to-`PairSeparated` implication are supplied, the generic
   pairing count immediately bounds the number of permutation samples making
   the fixed q-set rainbow. -/
lemma card_rainbow_permutations_le_of_pairSeparated
    (q : ℕ) (hq : 12 ≤ q)
    (S : QSubset (Fin (2 * q * (q - 1) + 1)) q)
    (e : Fin (q.choose 2) ↪ Fin ((q.choose 2) * 2))
    [Fintype {σ : Equiv.Perm (Fin ((q.choose 2) * 2)) //
      IsRainbowSet (cyclicPairingSample q hq σ) S.1}]
    (hrainbow : ∀ σ,
      IsRainbowSet (cyclicPairingSample q hq σ) S.1 →
        PairSeparated (q.choose 2) e σ) :
    Fintype.card {σ : Equiv.Perm (Fin ((q.choose 2) * 2)) //
      IsRainbowSet (cyclicPairingSample q hq σ) S.1} ≤
      2 ^ (q.choose 2) * Nat.factorial (q.choose 2) *
        Nat.factorial (q.choose 2) := by
  exact card_permutation_subtype_le_of_pairSeparated
    (q.choose 2) e
    (fun σ => IsRainbowSet (cyclicPairingSample q hq σ) S.1)
    hrainbow

/- If a fixed q-set has any rainbow sample, its unpermuted edge classes are
   injective.  Consequently one can choose a single edge-class embedding for
   the whole fixed-set sample count; the empty case is handled separately. -/
lemma card_rainbow_permutations_le
    (q : ℕ) (hq : 12 ≤ q)
    (S : QSubset (Fin (2 * q * (q - 1) + 1)) q)
    [Fintype {σ : Equiv.Perm (Fin ((q.choose 2) * 2)) //
      IsRainbowSet (cyclicPairingSample q hq σ) S.1}] :
    Fintype.card {σ : Equiv.Perm (Fin ((q.choose 2) * 2)) //
      IsRainbowSet (cyclicPairingSample q hq σ) S.1} ≤
      2 ^ (q.choose 2) * Nat.factorial (q.choose 2) *
        Nat.factorial (q.choose 2) := by
  classical
  let v : Fin q ↪ Fin (2 * q * (q - 1) + 1) :=
    S.1.orderEmbOfFin S.2 |>.toEmbedding
  have hv : ∀ a : Fin q, v a ∈ S.1 := by
    intro a
    exact Finset.orderEmbOfFin_mem S.1 S.2 a
  by_cases hex : ∃ σ : Equiv.Perm (Fin ((q.choose 2) * 2)),
      IsRainbowSet (cyclicPairingSample q hq σ) S.1
  · obtain ⟨σ₀, hσ₀⟩ := hex
    have hbase : Function.Injective (cyclicBaseEdgeClass q hq v) :=
      cyclicBaseEdgeClass_injective_of_rainbow q hq v S.1 hv σ₀ hσ₀
    let e := cyclicBaseEdgeEmbedding q hq v hbase
    apply card_rainbow_permutations_le_of_pairSeparated q hq S e
    intro σ hσ
    exact cyclicBaseEdgeEmbedding_pairSeparated_of_rainbow
      q hq v S.1 hv hbase σ hσ
  · have hzero : Fintype.card {σ : Equiv.Perm (Fin ((q.choose 2) * 2)) //
      IsRainbowSet (cyclicPairingSample q hq σ) S.1} = 0 := by
      rw [Fintype.card_eq_zero_iff]
      exact ⟨fun x => hex ⟨x.1, x.2⟩⟩
    simp [hzero]

lemma sum_rainbowQSubsetCount_le_of_filter_bound
    (q : ℕ) (hq : 12 ≤ q) (B : ℕ)
    (hbound : ∀ S : QSubset (Fin (2 * q * (q - 1) + 1)) q,
      ((Finset.univ : Finset (Equiv.Perm (Fin ((q.choose 2) * 2)))).filter
        (fun σ => IsRainbowSet (cyclicPairingSample q hq σ) S.1)).card ≤ B) :
    (∑ σ : Equiv.Perm (Fin ((q.choose 2) * 2)),
      rainbowQSubsetCount (q := q) (cyclicPairingSample q hq σ)) ≤
      Fintype.card (QSubset (Fin (2 * q * (q - 1) + 1)) q) * B := by
  classical
  let Ω := Equiv.Perm (Fin ((q.choose 2) * 2))
  let A := QSubset (Fin (2 * q * (q - 1) + 1)) q
  let bad : Ω → A → Prop := fun σ S =>
    IsRainbowSet (cyclicPairingSample q hq σ) S.1
  have hcomm := sum_filter_card_comm bad
  calc
    (∑ σ : Ω, rainbowQSubsetCount (q := q)
      (cyclicPairingSample q hq σ)) =
        ∑ σ : Ω, ((Finset.univ : Finset A).filter (bad σ)).card := by
      apply Finset.sum_congr rfl
      intro σ hσ
      change Fintype.card {S : QSubset (Fin (2 * q * (q - 1) + 1)) q //
        IsRainbowSet (cyclicPairingSample q hq σ) S.1} = _
      rw [Fintype.card_subtype]
    _ = ∑ S : A, ((Finset.univ : Finset Ω).filter
        (fun σ => bad σ S)).card := hcomm
    _ ≤ Fintype.card A * B := by
      calc
        (∑ S : A, ((Finset.univ : Finset Ω).filter
            (fun σ => bad σ S)).card) ≤ ∑ _S : A, B := by
          exact Finset.sum_le_sum (fun S _ => hbound S)
        _ = Fintype.card A * B := by simp

lemma sum_rainbowQSubsetCount_le
    (q : ℕ) (hq : 12 ≤ q) :
    (∑ σ : Equiv.Perm (Fin ((q.choose 2) * 2)),
      rainbowQSubsetCount (q := q) (cyclicPairingSample q hq σ)) ≤
      Fintype.card (QSubset (Fin (2 * q * (q - 1) + 1)) q) *
        (2 ^ (q.choose 2) * Nat.factorial (q.choose 2) *
          Nat.factorial (q.choose 2)) := by
  apply sum_rainbowQSubsetCount_le_of_filter_bound q hq _
  intro S
  letI : Fintype {σ : Equiv.Perm (Fin ((q.choose 2) * 2)) //
      IsRainbowSet (cyclicPairingSample q hq σ) S.1} :=
    Fintype.subtype
      ((Finset.univ : Finset (Equiv.Perm (Fin ((q.choose 2) * 2)))).filter
        (fun σ => IsRainbowSet (cyclicPairingSample q hq σ) S.1)) (by simp)
  have hcard := card_rainbow_permutations_le q hq S
  simpa [Fintype.card_subtype] using hcard

lemma cyclicPairingSample_no_rainbow_of_zero
    (q : ℕ) (hq : 12 ≤ q)
    (σ : Equiv.Perm (Fin ((q.choose 2) * 2)))
    (hzero : rainbowQSubsetCount (q := q)
      (cyclicPairingSample q hq σ) = 0) :
    ¬ HasRainbowCopy (SimpleGraph.completeGraph (Fin q))
      (cyclicPairingSample q hq σ) := by
  exact (rainbowQSubsetCount_eq_zero_iff
    (cyclicPairingSample q hq σ)).mp hzero

lemma probabilistic_witness_to_finite_base (q : ℕ) (hq : 4 ≤ q)
    (h : HasProbabilisticPairingWitness q) :
    HasBalancedCounterexampleAt (SimpleGraph.completeGraph (Fin q))
      (2 * q * (q - 1) + 1) := by
  refine ⟨probabilistic_order_mod_edgeCount q hq, ?_⟩
  simpa [HasProbabilisticPairingWitness] using h

lemma probabilistic_witness_to_arbitrarily_large (q : ℕ) (hq : 4 ≤ q)
    (h : HasProbabilisticPairingWitness q) :
    HasArbitrarilyLargeBalancedCounterexamples
      (SimpleGraph.completeGraph (Fin q)) := by
  rcases h with ⟨κ, hκ, hno⟩
  refine hasArbitrarilyLarge_of_finite_base q
    (2 * q * (q - 1) + 1)
    (probabilistic_order_mod_edgeCount q hq) κ hκ hno ?_ ?_
  · have hq0 : q ≠ 0 := by omega
    have hq10 : q - 1 ≠ 0 := by omega
    have hprod0 : 2 * q * (q - 1) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (by decide) hq0) hq10
    have hposprod : 0 < 2 * q * (q - 1) := Nat.pos_of_ne_zero hprod0
    omega
  · rw [edgeCount_completeGraph_fin, Nat.choose_two_right]
    have hq1 : 3 ≤ q - 1 := by omega
    have hprod : 6 ≤ q * (q - 1) := by
      nlinarith
    omega

#print axioms probabilistic_witness_to_arbitrarily_large

lemma exists_not_mem_of_card_lt_univ {Ω : Type*} [Fintype Ω]
    (bad : Finset Ω) (hbad : bad.card < Fintype.card Ω) :
    ∃ x : Ω, x ∉ bad := by
  by_contra h
  push_neg at h
  have hsub : (Finset.univ : Finset Ω) ⊆ bad := by
    intro x hx
    exact h x
  have hle : Fintype.card Ω ≤ bad.card := by
    simpa using Finset.card_le_card hsub
  exact (Nat.not_lt_of_ge hle) hbad

/-- Finite first-moment extraction.  This is the exact finite-probability step
used after the orbit count: if the total number of bad witnesses is smaller
than the number of samples, one sample has no bad witness. -/
lemma exists_zero_of_sum_lt_card {Ω : Type*} [Fintype Ω]
    (badCount : Ω → ℕ)
    (hcount : (∑ ω : Ω, badCount ω) < Fintype.card Ω) :
    ∃ ω : Ω, badCount ω = 0 := by
  by_contra hzero
  push_neg at hzero
  have hone : ∀ ω : Ω, 1 ≤ badCount ω := by
    intro ω
    exact Nat.one_le_iff_ne_zero.mpr (hzero ω)
  have hsum : (∑ _ω : Ω, 1) ≤ ∑ ω : Ω, badCount ω := by
    exact Finset.sum_le_sum (fun ω _ => hone ω)
  have hcard : Fintype.card Ω ≤ ∑ ω : Ω, badCount ω := by
    simpa using hsum
  exact (Nat.not_lt_of_ge hcard) hcount

/-- A convenient orbit-count interface.  The concrete random-pairing proof
supplies `badCount`; this lemma keeps the existence argument independent of
the chosen finite sample representation. -/
lemma exists_good_sample_of_expected_bad_lt_one
    {Ω : Type*} [Fintype Ω]
    (badCount : Ω → ℕ)
    (hcount : (∑ ω : Ω, badCount ω) < Fintype.card Ω) :
    ∃ ω : Ω, badCount ω = 0 :=
  exists_zero_of_sum_lt_card badCount hcount

lemma exists_cyclicPairingSample_no_rainbow
    (q : ℕ) (hq : 12 ≤ q)
    (hcount :
      (∑ σ : Equiv.Perm (Fin ((q.choose 2) * 2)),
        rainbowQSubsetCount (q := q) (cyclicPairingSample q hq σ)) <
        Fintype.card (Equiv.Perm (Fin ((q.choose 2) * 2)))) :
    ∃ σ : Equiv.Perm (Fin ((q.choose 2) * 2)),
      (cyclicPairingSample q hq σ).IsBalanced ∧
        ¬ HasRainbowCopy (SimpleGraph.completeGraph (Fin q))
          (cyclicPairingSample q hq σ) := by
  let badCount : Equiv.Perm (Fin ((q.choose 2) * 2)) → ℕ := fun σ =>
    rainbowQSubsetCount (q := q) (cyclicPairingSample q hq σ)
  obtain ⟨σ, hσ⟩ := exists_good_sample_of_expected_bad_lt_one badCount (by
    simpa [badCount] using hcount)
  refine ⟨σ, cyclicPairingSample_isBalanced q hq σ, ?_⟩
  exact cyclicPairingSample_no_rainbow_of_zero q hq σ (by simpa [badCount] using hσ)

lemma probabilistic_pairing_witness_of_first_moment
    (q : ℕ) (hq : 12 ≤ q)
    (hcount :
      (∑ σ : Equiv.Perm (Fin ((q.choose 2) * 2)),
        rainbowQSubsetCount (q := q) (cyclicPairingSample q hq σ)) <
        Fintype.card (Equiv.Perm (Fin ((q.choose 2) * 2)))) :
    HasProbabilisticPairingWitness q := by
  obtain ⟨σ, hbal, hno⟩ := exists_cyclicPairingSample_no_rainbow q hq hcount
  unfold HasProbabilisticPairingWitness
  rw [edgeCount_completeGraph_fin]
  exact ⟨cyclicPairingSample q hq σ, hbal, hno⟩

lemma exists_cyclicPairingSample_no_rainbow_of_numeric_bound
    (q : ℕ) (hq : 12 ≤ q)
    (hnumeric :
      Fintype.card (QSubset (Fin (2 * q * (q - 1) + 1)) q) *
          (2 ^ (q.choose 2) * Nat.factorial (q.choose 2) *
            Nat.factorial (q.choose 2)) <
        Fintype.card (Equiv.Perm (Fin ((q.choose 2) * 2)))) :
    ∃ σ : Equiv.Perm (Fin ((q.choose 2) * 2)),
      (cyclicPairingSample q hq σ).IsBalanced ∧
        ¬ HasRainbowCopy (SimpleGraph.completeGraph (Fin q))
          (cyclicPairingSample q hq σ) := by
  apply exists_cyclicPairingSample_no_rainbow q hq
  exact (sum_rainbowQSubsetCount_le q hq).trans_lt hnumeric

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem q12_numeric_orbit_bound :
    Fintype.card (QSubset (Fin (2 * 12 * (12 - 1) + 1)) 12) *
        (2 ^ ((12 : ℕ).choose 2) * Nat.factorial ((12 : ℕ).choose 2) *
          Nat.factorial ((12 : ℕ).choose 2)) <
      (2 * 12 * (12 - 1) + 1) *
        Fintype.card (Equiv.Perm (Fin (((12 : ℕ).choose 2) * 2))) := by
  norm_num [card_qSubset, Fintype.card_perm, Nat.choose]

/-! The same extraction with the orbit lower bound made explicit.  This is the
finite combinatorial interface used by the eventual random-pairing
instantiation: a nonempty bad translation orbit contributes at least `N` to
`badCount`, while the total first moment is strictly smaller than `N` times
the number of samples. -/
lemma exists_balanced_no_rainbow_of_orbit_bound
    {α V C Ω : Type*} [Fintype Ω]
    [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
    (G : SimpleGraph α) (sample : Ω → CompleteEdgeColoring V C)
    (hbalanced : ∀ ω : Ω, (sample ω).IsBalanced)
    (badCount : Ω → ℕ)
    (hzero : ∀ ω : Ω,
      badCount ω = 0 ↔ ¬ HasRainbowCopy G (sample ω))
    (N : ℕ) (hN : 0 < N)
    (horbit : ∀ ω : Ω, badCount ω = 0 ∨ N ≤ badCount ω)
    (hcount : (∑ ω : Ω, badCount ω) < N * Fintype.card Ω) :
    ∃ ω : Ω, (sample ω).IsBalanced ∧ ¬ HasRainbowCopy G (sample ω) := by
  obtain ⟨ω, hω⟩ := exists_zero_of_sum_lt_mul_card N hN badCount horbit hcount
  exact ⟨ω, hbalanced ω, (hzero ω).mp hω⟩

/- The q=12 numerical checkpoint now closes the finite extraction step.  The
   orbit lower bound is supplied by the cyclic translation action above, so
   the first-moment estimate produces an actual pairing witness. -/
theorem q12_probabilistic_pairing_witness :
    HasProbabilisticPairingWitness 12 := by
  have hq : 12 ≤ (12 : ℕ) := by norm_num
  let N : ℕ := 2 * 12 * (12 - 1) + 1
  let Ω := Equiv.Perm (Fin (((12 : ℕ).choose 2) * 2))
  let badCount : Ω → ℕ := fun σ =>
    rainbowQSubsetCount (q := 12) (cyclicPairingSample 12 hq σ)
  have hsum :
      (∑ σ : Ω, badCount σ) ≤
        Fintype.card (QSubset (Fin N) 12) *
          (2 ^ ((12 : ℕ).choose 2) *
            Nat.factorial ((12 : ℕ).choose 2) *
            Nat.factorial ((12 : ℕ).choose 2)) := by
    simpa [badCount, Ω, N] using sum_rainbowQSubsetCount_le 12 hq
  have hcount :
      (∑ σ : Ω, badCount σ) < N * Fintype.card Ω := by
    have hnum := q12_numeric_orbit_bound
    exact hsum.trans_lt (by simpa [Ω, N] using hnum)
  have hzero : ∀ σ : Ω,
      badCount σ = 0 ↔
        ¬ HasRainbowCopy (SimpleGraph.completeGraph (Fin 12))
          (cyclicPairingSample 12 hq σ) := by
    intro σ
    exact rainbowQSubsetCount_eq_zero_iff
      (cyclicPairingSample 12 hq σ)
  have hN : 0 < N := by simp [N]
  have horbit : ∀ σ : Ω, badCount σ = 0 ∨ N ≤ badCount σ := by
    intro σ
    simpa [badCount, N] using
      (cyclicRainbowQSubsetCount_zero_or_ge_auto 12 hq σ)
  obtain ⟨σ, hbal, hno⟩ :=
    exists_balanced_no_rainbow_of_orbit_bound
      (G := SimpleGraph.completeGraph (Fin 12))
      (sample := fun σ : Ω => cyclicPairingSample 12 hq σ)
      (hbalanced := by
        intro σ
        exact cyclicPairingSample_isBalanced 12 hq σ)
      badCount hzero N hN horbit hcount
  unfold HasProbabilisticPairingWitness
  rw [edgeCount_completeGraph_fin]
  exact ⟨cyclicPairingSample 12 hq σ, hbal, hno⟩

lemma orbit_card_lower_bound
    {Ω : Type*} [Fintype Ω] (N : ℕ) (hN : 0 < N)
    (badCount : Ω → ℕ)
    (hbad : ∀ ω : Ω, badCount ω ≠ 0 → N ≤ badCount ω) :
    ∀ ω : Ω, badCount ω = 0 ∨ N ≤ badCount ω := by
  intro ω
  by_cases hz : badCount ω = 0
  · exact Or.inl hz
  · exact Or.inr (hbad ω hz)

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem q12_expectedBadOrbit_lt_one : expectedBadOrbit 12 < 1 := by
  norm_num [expectedBadOrbit, Nat.choose]

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem q12_expectedBadOrbit_lt_three_twentieths :
    expectedBadOrbit 12 < (3 : ℚ) / 20 := by
  norm_num [expectedBadOrbit, Nat.choose]

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem q12_crudeExpectedBound_lt_one : crudeExpectedBound 12 < 1 := by
  norm_num [crudeExpectedBound, Nat.choose]

theorem crudeExpectedBound_lt_one :
    ∀ q : ℕ, 12 ≤ q → crudeExpectedBound q < 1 := by
  intro q hq
  induction q, hq using Nat.le_induction with
  | base => exact q12_crudeExpectedBound_lt_one
  | succ q hq ih =>
      have hstep := crudeExpectedBound_succ_le q hq
      have htail := crude_tail_lt_one q hq
      have hcrude_pos : 0 < crudeExpectedBound q := by
        unfold crudeExpectedBound
        have hmpos : 0 < (q.choose 2 : ℚ) := by
          exact_mod_cast (Nat.choose_pos (by omega : 2 ≤ q))
        positivity
      have hmul : crudeExpectedBound q *
          ((21 : ℚ) / 10 * q * ((3 : ℚ) / 4) ^ q) <
          crudeExpectedBound q := by
        have h := mul_lt_mul_of_pos_left htail hcrude_pos
        simpa using h
      exact lt_of_le_of_lt hstep (hmul.trans ih)

theorem expectedBadOrbit_lt_one :
    ∀ q : ℕ, 12 ≤ q → expectedBadOrbit q < 1 := by
  intro q hq
  exact (expectedBadOrbit_le_crudeExpectedBound q hq).trans_lt
    (crudeExpectedBound_lt_one q hq)

lemma numeric_orbit_bound_of_expectedBadOrbit_lt_one
    (q : ℕ) (hq : 12 ≤ q) (hE : expectedBadOrbit q < 1) :
    Fintype.card (QSubset (Fin (2 * q * (q - 1) + 1)) q) *
        (2 ^ (q.choose 2) * Nat.factorial (q.choose 2) *
          Nat.factorial (q.choose 2)) <
      (2 * q * (q - 1) + 1) *
        Fintype.card (Equiv.Perm (Fin ((q.choose 2) * 2))) := by
  let N : ℕ := 2 * q * (q - 1) + 1
  let m : ℕ := q.choose 2
  have hNpos : (0 : ℚ) < N := by
    dsimp [N]
    positivity
  have hCpos : (0 : ℚ) < Nat.choose (2 * m) m := by
    exact_mod_cast (Nat.choose_pos (by omega : m ≤ 2 * m))
  have hNraw : (0 : ℚ) <
      ((2 * q * (q - 1) + 1 : ℕ) : ℚ) := by positivity
  have hCraw : (0 : ℚ) <
      Nat.choose (2 * q.choose 2) (q.choose 2) := by
    exact_mod_cast (Nat.choose_pos (by omega : q.choose 2 ≤ 2 * q.choose 2))
  have hcancel (A B X Y : ℚ) (hX : X ≠ 0) (hY : Y ≠ 0) :
      A * B = (A / X) * (B / Y) * (X * Y) := by
    field_simp [hX, hY]
  have hqpos : 0 < q := by omega
  have hEqRaw :
      (Nat.choose (2 * q * (q - 1) + 1) q : ℚ) *
          (2 : ℚ) ^ (q.choose 2) =
        expectedBadOrbit q *
          (((2 * q * (q - 1) + 1 : ℕ) : ℚ) *
            (Nat.choose (2 * q.choose 2) (q.choose 2) : ℚ)) := by
    simpa [expectedBadOrbit, Nat.cast_sub (by omega : 1 ≤ q)] using
      hcancel
        (Nat.choose (2 * q * (q - 1) + 1) q : ℚ)
        ((2 : ℚ) ^ (q.choose 2))
        (((2 * q * (q - 1) + 1 : ℕ) : ℚ))
        (Nat.choose (2 * q.choose 2) (q.choose 2) : ℚ)
        hNraw.ne' hCraw.ne'
  have hEq :
      (N.choose q : ℚ) * (2 : ℚ) ^ m =
        expectedBadOrbit q *
          ((N : ℚ) * (Nat.choose (2 * m) m : ℚ)) := by
    simpa [N, m] using hEqRaw
  have hstrictQ :
      (N.choose q : ℚ) * (2 : ℚ) ^ m <
        (N : ℚ) * (Nat.choose (2 * m) m : ℚ) := by
    calc
      (N.choose q : ℚ) * (2 : ℚ) ^ m =
          expectedBadOrbit q *
            ((N : ℚ) * (Nat.choose (2 * m) m : ℚ)) := hEq
      _ < 1 * ((N : ℚ) * (Nat.choose (2 * m) m : ℚ)) := by
        exact mul_lt_mul_of_pos_right hE (mul_pos hNpos hCpos)
      _ = (N : ℚ) * (Nat.choose (2 * m) m : ℚ) := by ring
  have hstrict : N.choose q * 2 ^ m < N * Nat.choose (2 * m) m := by
    exact_mod_cast hstrictQ
  have hfac : Nat.choose (2 * m) m * Nat.factorial m *
      Nat.factorial m = Nat.factorial (2 * m) := by
    simpa [show 2 * m - m = m by omega] using
      (Nat.choose_mul_factorial_mul_factorial
        (n := 2 * m) (k := m) (by omega : m ≤ 2 * m))
  have hmult := Nat.mul_lt_mul_of_pos_right hstrict (Nat.factorial_pos m)
  have hmult2 := Nat.mul_lt_mul_of_pos_right hmult (Nat.factorial_pos m)
  have hmult3 :
      N.choose q * (2 ^ m * (Nat.factorial m * Nat.factorial m)) <
        N * Nat.factorial (2 * m) := by
    calc
      N.choose q * (2 ^ m * (Nat.factorial m * Nat.factorial m)) <
          N * (Nat.choose (2 * m) m * Nat.factorial m * Nat.factorial m) := by
            simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmult2
      _ = N * Nat.factorial (2 * m) := by rw [hfac]
  simpa [card_qSubset, Fintype.card_perm, N, m,
    Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmult3

/- The coarse rational first-moment estimate is strong enough, together with
   the free cyclic translation orbit, to produce a witness uniformly for every
   q ≥ 12. -/
lemma probabilistic_pairing_witness_of_expectedBadOrbit_lt_one
    (q : ℕ) (hq : 12 ≤ q) :
    HasProbabilisticPairingWitness q := by
  let N : ℕ := 2 * q * (q - 1) + 1
  let Ω := Equiv.Perm (Fin ((q.choose 2) * 2))
  let badCount : Ω → ℕ := fun σ =>
    rainbowQSubsetCount (q := q) (cyclicPairingSample q hq σ)
  have hsum :
      (∑ σ : Ω, badCount σ) ≤
        Fintype.card (QSubset (Fin N) q) *
          (2 ^ (q.choose 2) * Nat.factorial (q.choose 2) *
            Nat.factorial (q.choose 2)) := by
    simpa [badCount, Ω, N] using sum_rainbowQSubsetCount_le q hq
  have hnum := numeric_orbit_bound_of_expectedBadOrbit_lt_one q hq
    (expectedBadOrbit_lt_one q hq)
  have hcount :
      (∑ σ : Ω, badCount σ) < N * Fintype.card Ω := by
    exact hsum.trans_lt (by simpa [Ω, N] using hnum)
  have hzero : ∀ σ : Ω,
      badCount σ = 0 ↔
        ¬ HasRainbowCopy (SimpleGraph.completeGraph (Fin q))
          (cyclicPairingSample q hq σ) := by
    intro σ
    exact rainbowQSubsetCount_eq_zero_iff
      (cyclicPairingSample q hq σ)
  have hN : 0 < N := by
    simp [N]
  have horbit : ∀ σ : Ω, badCount σ = 0 ∨ N ≤ badCount σ := by
    intro σ
    simpa [badCount, N] using
      (cyclicRainbowQSubsetCount_zero_or_ge_auto q hq σ)
  obtain ⟨σ, hbal, hno⟩ :=
    exists_balanced_no_rainbow_of_orbit_bound
      (G := SimpleGraph.completeGraph (Fin q))
      (sample := fun σ : Ω => cyclicPairingSample q hq σ)
      (hbalanced := by
        intro σ
        exact cyclicPairingSample_isBalanced q hq σ)
      badCount hzero N hN horbit hcount
  unfold HasProbabilisticPairingWitness
  rw [edgeCount_completeGraph_fin]
  exact ⟨cyclicPairingSample q hq σ, hbal, hno⟩

lemma two_pow_gt_36_mul_of_ge_13 :
    ∀ q : ℕ, 13 ≤ q → 36 * q < 2 ^ q := by
  intro q hq
  induction q, hq using Nat.le_induction with
  | base => norm_num
  | succ q hq ih =>
      have hpow : 36 ≤ 2 ^ q := by
        have hqpos : 1 ≤ q := by omega
        have hmul : 36 ≤ 36 * q := by nlinarith
        omega
      rw [pow_succ]
      nlinarith

theorem ratio_36q_two_pow_lt_one :
    ∀ q : ℕ, 13 ≤ q → (36 : ℚ) * q / 2 ^ q < 1 := by
  intro q hq
  have hnat : 36 * q < 2 ^ q := two_pow_gt_36_mul_of_ge_13 q hq
  have hpowpos : (0 : ℚ) < 2 ^ q := by positivity
  apply (div_lt_iff₀ hpowpos).2
  have hrat : (36 : ℚ) * q < (2 : ℚ) ^ q := by
    exact_mod_cast hnat
  simpa using hrat

#print axioms q12_expectedBadOrbit_lt_one

end
end Erdos811
