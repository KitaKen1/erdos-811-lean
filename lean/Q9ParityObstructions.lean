import Q9EdgePairs

/-!
Arithmetic consequences of the q=9 colour-sum identity.

The search certificate supplies the identity that the 36 edge colours are
exactly `0, ..., 35`, hence their natural representatives sum to `630`.
These lemmas isolate the small modular step used in the paper proof: the
infinity branch forces zero odd finite vertices, while the finite branch can
only have four or five odd vertices.
-/

namespace Erdos811

lemma q9_mod9_subtraction (s c : Nat) (hc : c ≤ 9 * s)
    (h : (9 * s - c) % 36 = 18) : c % 9 = 0 := by
  have h9 : (9 * s - c) % 9 = 0 := by
    have hmod := congrArg (fun n : Nat => n % 9) h
    simpa [Nat.mod_mod_of_dvd _ (by norm_num : 9 ∣ 36)] using hmod
  have hN := Nat.mod_add_div (9 * s - c) 9
  have hC := Nat.mod_add_div c 9
  have hcancel := Nat.sub_add_cancel hc
  omega

lemma q9_infty_parity_candidates (r s : Nat) (hr : r ≤ 7)
    (hc : r + r.choose 2 ≤ 9 * s)
    (h : (9 * s - r - r.choose 2) % 36 = 18) : r = 0 := by
  have hmod : (r + r.choose 2) % 9 = 0 := by
    apply q9_mod9_subtraction s (r + r.choose 2) hc
    rw [← Nat.sub_sub]
    exact h
  interval_cases r <;> norm_num [Nat.choose] at hmod
  all_goals rfl

lemma q9_infty_zmod_candidate (r s : Nat) (hr : r ≤ 7)
    (hc : r + r.choose 2 ≤ 9 * s)
    (h : (9 : ZMod 36) * s - r - (Nat.choose r 2 : ZMod 36) = 18) : r = 0 := by
  have hcast : ((9 * s - r - Nat.choose r 2 : Nat) : ZMod 36) =
      (9 : ZMod 36) * s - r - (Nat.choose r 2 : ZMod 36) := by
    rw [Nat.sub_sub]
    rw [Nat.cast_sub]
    · simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add]
      ring
    · omega
  have hmod : (9 * s - r - Nat.choose r 2) % 36 = 18 := by
    apply (ZMod.natCast_eq_natCast_iff' (9 * s - r - Nat.choose r 2) 18 36).mp
    rw [hcast]
    exact h
  exact q9_infty_parity_candidates r s hr hc hmod

lemma q9_mod4_subtraction (s c : Nat) (hc : c ≤ 8 * s)
    (h : (8 * s - c) % 36 = 18) : c % 4 = 2 := by
  have h4 : (8 * s - c) % 4 = 2 := by
    have hmod := congrArg (fun n : Nat => n % 4) h
    simpa [Nat.mod_mod_of_dvd _ (by norm_num : 4 ∣ 36)] using hmod
  have hN := Nat.mod_add_div (8 * s - c) 4
  have hC := Nat.mod_add_div c 4
  have hcancel := Nat.sub_add_cancel hc
  omega

lemma q9_no_infty_parity_candidates (r s : Nat) (hr : r ≤ 8)
    (hc : r.choose 2 ≤ 8 * s)
    (h : (8 * s - r.choose 2) % 36 = 18) : r = 4 ∨ r = 5 := by
  have hmod : r.choose 2 % 4 = 2 := q9_mod4_subtraction s (r.choose 2) hc h
  interval_cases r <;> norm_num [Nat.choose] at hmod
  all_goals omega

lemma q9_no_infty_zmod_candidate (r s : Nat) (hr : r ≤ 8)
    (hc : r.choose 2 ≤ 8 * s)
    (h : (8 : ZMod 36) * s - (Nat.choose r 2 : ZMod 36) = 18) :
    r = 4 ∨ r = 5 := by
  have hcast : ((8 * s - Nat.choose r 2 : Nat) : ZMod 36) =
      (8 : ZMod 36) * s - (Nat.choose r 2 : ZMod 36) := by
    rw [Nat.cast_sub]
    · simp only [Nat.cast_mul, Nat.cast_ofNat]
    · exact hc
  have hmod : (8 * s - Nat.choose r 2) % 36 = 18 := by
    apply (ZMod.natCast_eq_natCast_iff' (8 * s - Nat.choose r 2) 18 36).mp
    rw [hcast]
    exact h
  exact q9_no_infty_parity_candidates r s hr hc hmod

def q9EdgePairs8 : Finset (Fin 8 × Fin 8) :=
  (Finset.univ.product Finset.univ).filter (fun p => p.1 < p.2)

lemma q9EdgePairs8_card : q9EdgePairs8.card = 28 := by
  decide

lemma q9_sum_pair_linear (f : Fin 8 → ZMod 36) :
    ∑ p : {p // p ∈ q9EdgePairs8}, (f p.1.1 + f p.1.2) =
      7 * ∑ i : Fin 8, f i := by
  classical
  have hsum := Finset.sum_subtype (F := inferInstance)
    (p := fun p : Fin 8 × Fin 8 => p ∈ q9EdgePairs8)
    q9EdgePairs8 (fun x => Iff.rfl)
      (fun p : Fin 8 × Fin 8 => f p.1 + f p.2)
  rw [← hsum]
  simp [q9EdgePairs8, Fintype.sum_prod_type, Fin.sum_univ_succ, Finset.sum_filter]
  ring

set_option maxHeartbeats 0 in
lemma q9_pair_bit_sum_choose (e : Fin 8 → Nat) (he : ∀ i, e i = 0 ∨ e i = 1) :
    (∑ p : {p // p ∈ q9EdgePairs8},
      ((e p.1.1 * e p.1.2 : Nat) : ZMod 36)) =
      (Nat.choose (∑ i : Fin 8, e i) 2 : ZMod 36) := by
  have h0 := he (0 : Fin 8)
  have h1 := he (1 : Fin 8)
  have h2 := he (2 : Fin 8)
  have h3 := he (3 : Fin 8)
  have h4 := he (4 : Fin 8)
  have h5 := he (5 : Fin 8)
  have h6 := he (6 : Fin 8)
  have h7 := he (7 : Fin 8)
  have hsum := Finset.sum_subtype (F := inferInstance)
    (p := fun p : Fin 8 × Fin 8 => p ∈ q9EdgePairs8)
    q9EdgePairs8 (fun x => Iff.rfl)
      (fun p : Fin 8 × Fin 8 => ((e p.1 * e p.2 : Nat) : ZMod 36))
  rw [← hsum]
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
    rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
    rcases h4 with h4 | h4 <;> rcases h5 with h5 | h5 <;>
    rcases h6 with h6 | h6 <;> rcases h7 with h7 | h7 <;>
    simp [q9EdgePairs8, Fintype.sum_prod_type, Fin.sum_univ_succ,
      Finset.sum_filter, h0, h1, h2, h3, h4, h5, h6, h7] <;>
    norm_num [Nat.choose]

set_option maxHeartbeats 0 in
lemma q9_pair_odd_fin2_le16 (b : Fin 8 → Fin 2) :
    (Finset.filter
      (fun p : {p // p ∈ q9EdgePairs8} =>
        (b p.1.1).val ≠ (b p.1.2).val)
      Finset.univ).card ≤ 16 := by
  fin_cases b <;> decide

set_option maxHeartbeats 0 in
lemma q9_even_finite_odd_le16 (x : Fin 8 → Nat)
    (hx : ∀ i, x i < 72) (heven : ∀ i, x i % 2 = 0) :
    (Finset.filter
      (fun p : {p // p ∈ q9EdgePairs8} =>
        q9EdgeColorFast (x p.1.1) (x p.1.2) % 2 = 1)
      Finset.univ).card ≤ 16 := by
  let b : Fin 8 → Fin 2 := fun i => ⟨(x i / 2) % 2, by omega⟩
  have hcolor (i j : Fin 8) :
      q9EdgeColorFast (x i) (x j) % 2 =
        ((b i).val + (b j).val) % 2 := by
    rw [q9_edge_formula_nat (hx i) (hx j)]
    have hei := heven i
    have hej := heven j
    have hxi : (x i + 1) / 2 = x i / 2 := by omega
    have hyi : (x j + 1) / 2 = x j / 2 := by omega
    rw [hxi, hyi]
    dsimp [b]
    simp [hei, hej]
  have hfilter :
      (Finset.filter
        (fun p : {p // p ∈ q9EdgePairs8} =>
          q9EdgeColorFast (x p.1.1) (x p.1.2) % 2 = 1)
        Finset.univ) =
      (Finset.filter
        (fun p : {p // p ∈ q9EdgePairs8} =>
          (b p.1.1).val ≠ (b p.1.2).val)
        Finset.univ) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcolor]
    omega
  rw [hfilter]
  exact q9_pair_odd_fin2_le16 b

lemma q9_finite_edge_sum_zmod (x : Fin 8 → Nat) (hx : ∀ i, x i < 72) :
    ∑ p : {p // p ∈ q9EdgePairs8},
      ((q9EdgeColorFast (x p.1.1) (x p.1.2) : Nat) : ZMod 36) =
      7 * ∑ i : Fin 8, (((x i + 1) / 2 : Nat) : ZMod 36) -
        ∑ p : {p // p ∈ q9EdgePairs8},
          ((x p.1.1 % 2 : Nat) : ZMod 36) *
            ((x p.1.2 % 2 : Nat) : ZMod 36) := by
  classical
  simp_rw [q9_edge_formula_zmod (hx _) (hx _)]
  rw [Finset.sum_sub_distrib]
  have hlin := q9_sum_pair_linear
    (fun i : Fin 8 => (((x i + 1) / 2 : Nat) : ZMod 36))
  simpa using hlin

lemma q9_infty_edge_sum_zmod (x : Fin 8 → Nat) :
    ∑ i : Fin 8, ((q9EdgeColorFast 72 (x i) : Nat) : ZMod 36) =
      ∑ i : Fin 8, ((x i % 36 : Nat) : ZMod 36) := by
  simp_rw [q9_infty_edge_formula_nat]

set_option maxHeartbeats 0 in
lemma q9_infty_branch_sum_formula (x : Fin 8 → Nat) (hx : ∀ i, x i < 72) :
    (∑ p : {p // p ∈ q9EdgePairs8},
      ((q9EdgeColorFast (x p.1.1) (x p.1.2) : Nat) : ZMod 36)) +
      ∑ i : Fin 8, ((q9EdgeColorFast 72 (x i) : Nat) : ZMod 36) =
      9 * ∑ i : Fin 8, (((x i + 1) / 2 : Nat) : ZMod 36) -
        ∑ i : Fin 8, ((x i % 2 : Nat) : ZMod 36) -
        (Nat.choose (∑ i : Fin 8, x i % 2) 2 : ZMod 36) := by
  have hfin := q9_finite_edge_sum_zmod x hx
  have hinf := q9_infty_edge_sum_zmod x
  rw [hfin, hinf]
  have hebit : ∀ i : Fin 8, x i % 2 = 0 ∨ x i % 2 = 1 := by
    intro i
    omega
  have hprod :
      (∑ p : {p // p ∈ q9EdgePairs8},
        ((x p.1.1 % 2 : Nat) : ZMod 36) *
          ((x p.1.2 % 2 : Nat) : ZMod 36)) =
        (Nat.choose (∑ i : Fin 8, x i % 2) 2 : ZMod 36) := by
    simpa only [Nat.cast_mul] using q9_pair_bit_sum_choose (fun i => x i % 2) hebit
  rw [hprod]
  have hlin :
      (∑ i : Fin 8, ((x i % 36 : Nat) : ZMod 36)) =
        2 * ∑ i : Fin 8, (((x i + 1) / 2 : Nat) : ZMod 36) -
          ∑ i : Fin 8, ((x i % 2 : Nat) : ZMod 36) := by
    have hpoint (i : Fin 8) :
        ((x i % 36 : Nat) : ZMod 36) =
          2 * (((x i + 1) / 2 : Nat) : ZMod 36) -
            ((x i % 2 : Nat) : ZMod 36) := by
      have hrel : x i = 2 * ((x i + 1) / 2) - (x i % 2) := by omega
      calc
        ((x i % 36 : Nat) : ZMod 36) = ((x i : Nat) : ZMod 36) := by
          rw [ZMod.natCast_mod]
        _ = ((2 * ((x i + 1) / 2) - (x i % 2) : Nat) : ZMod 36) := by
          exact congrArg (fun n : Nat => (n : ZMod 36)) hrel
        _ = 2 * (((x i + 1) / 2 : Nat) : ZMod 36) -
            ((x i % 2 : Nat) : ZMod 36) := by
          rw [Nat.cast_sub]
          · simp only [Nat.cast_mul, Nat.cast_ofNat]
          · omega
    calc
      _ = ∑ i : Fin 8,
          (2 * (((x i + 1) / 2 : Nat) : ZMod 36) -
            ((x i % 2 : Nat) : ZMod 36)) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hpoint i
      _ = 2 * ∑ i : Fin 8, (((x i + 1) / 2 : Nat) : ZMod 36) -
          ∑ i : Fin 8, ((x i % 2 : Nat) : ZMod 36) := by
        rw [Finset.sum_sub_distrib]
        simp only [← Finset.mul_sum]
  rw [hlin]
  ring

lemma q9_split_edges_sum_nat (g : Fin 9 → Fin 73)
    (h8 : (g (8 : Fin 9)).val = 72)
    (hfin : ∀ i : Fin 8, (g i.castSucc).val < 72) :
    (∑ p : {p // p ∈ q9EdgePairs},
      q9EdgeColorFast (g p.1.1).val (g p.1.2).val) =
      (∑ p : {p // p ∈ q9EdgePairs8},
        q9EdgeColorFast (g p.1.1.castSucc).val (g p.1.2.castSucc).val) +
      ∑ i : Fin 8, q9EdgeColorFast 72 (g i.castSucc).val := by
  classical
  have hL := Finset.sum_subtype (F := inferInstance)
    (p := fun p : Fin 9 × Fin 9 => p ∈ q9EdgePairs)
    q9EdgePairs (fun x => Iff.rfl)
      (fun p : Fin 9 × Fin 9 => q9EdgeColorFast (g p.1).val (g p.2).val)
  have hF := Finset.sum_subtype (F := inferInstance)
    (p := fun p : Fin 8 × Fin 8 => p ∈ q9EdgePairs8)
    q9EdgePairs8 (fun x => Iff.rfl)
      (fun p : Fin 8 × Fin 8 => q9EdgeColorFast (g p.1.castSucc).val (g p.2.castSucc).val)
  rw [← hL, ← hF]
  have hg8 : g (8 : Fin 9) = ⟨72, by omega⟩ := Fin.ext h8
  have hfinite_ne : ∀ i : Fin 8, (g i.castSucc).val ≠ 72 := by
    intro i
    exact Nat.ne_of_lt (hfin i)
  have hfinite_ne9 : ∀ i : Fin 9, i.val < 8 → (g i).val ≠ 72 := by
    intro i hi hEq
    have hi8 : ∃ j : Fin 8, j.castSucc = i := by
      refine ⟨⟨i.val, hi⟩, ?_⟩
      apply Fin.ext
      rfl
    rcases hi8 with ⟨j, rfl⟩
    exact hfinite_ne j hEq
  simp [q9EdgePairs, q9EdgePairs8, Fintype.sum_prod_type,
    Finset.sum_filter, Fin.sum_univ_succ, q9EdgeColorFast,
    h8, hg8, hfinite_ne, hfinite_ne9]
  ring

lemma q9_split_edges_sum_zmod (g : Fin 9 → Fin 73)
    (h8 : (g (8 : Fin 9)).val = 72)
    (hfin : ∀ i : Fin 8, (g i.castSucc).val < 72) :
    (∑ p : {p // p ∈ q9EdgePairs},
      ((q9EdgeColorFast (g p.1.1).val (g p.1.2).val : Nat) : ZMod 36)) =
      (∑ p : {p // p ∈ q9EdgePairs8},
        ((q9EdgeColorFast (g p.1.1.castSucc).val
          (g p.1.2.castSucc).val : Nat) : ZMod 36)) +
      ∑ i : Fin 8, ((q9EdgeColorFast 72 (g i.castSucc).val : Nat) : ZMod 36) := by
  rw [← Nat.cast_sum]
  rw [q9_split_edges_sum_nat g h8 hfin]
  simp only [Nat.cast_add, Nat.cast_sum]

set_option maxHeartbeats 0 in
lemma q9_split_sum_general (F : Fin 9 → Fin 9 → Nat) (g : Fin 9 → Fin 73)
    (h8 : (g (8 : Fin 9)).val = 72)
    (hfin : ∀ i : Fin 8, (g i.castSucc).val < 72) :
    (∑ p : {p // p ∈ q9EdgePairs}, F p.1.1 p.1.2) =
      (∑ p : {p // p ∈ q9EdgePairs8}, F p.1.1.castSucc p.1.2.castSucc) +
      ∑ i : Fin 8, F i.castSucc 8 := by
  classical
  have hL := Finset.sum_subtype (F := inferInstance)
    (p := fun p : Fin 9 × Fin 9 => p ∈ q9EdgePairs)
    q9EdgePairs (fun x => Iff.rfl)
      (fun p : Fin 9 × Fin 9 => F p.1 p.2)
  have hF := Finset.sum_subtype (F := inferInstance)
    (p := fun p : Fin 8 × Fin 8 => p ∈ q9EdgePairs8)
    q9EdgePairs8 (fun x => Iff.rfl)
      (fun p : Fin 8 × Fin 8 => F p.1.castSucc p.2.castSucc)
  rw [← hL, ← hF]
  simp [q9EdgePairs, q9EdgePairs8, Fintype.sum_prod_type,
    Finset.sum_filter, Fin.sum_univ_succ]
  ring

set_option maxHeartbeats 0 in
lemma q9_split_sum_general_zmod (F : Fin 9 → Fin 9 → ZMod 36) (g : Fin 9 → Fin 73) :
    (∑ p : {p // p ∈ q9EdgePairs}, F p.1.1 p.1.2) =
      (∑ p : {p // p ∈ q9EdgePairs8}, F p.1.1.castSucc p.1.2.castSucc) +
      ∑ i : Fin 8, F i.castSucc 8 := by
  classical
  have hL := Finset.sum_subtype (F := inferInstance)
    (p := fun p : Fin 9 × Fin 9 => p ∈ q9EdgePairs)
    q9EdgePairs (fun x => Iff.rfl)
      (fun p : Fin 9 × Fin 9 => F p.1 p.2)
  have hF := Finset.sum_subtype (F := inferInstance)
    (p := fun p : Fin 8 × Fin 8 => p ∈ q9EdgePairs8)
    q9EdgePairs8 (fun x => Iff.rfl)
      (fun p : Fin 8 × Fin 8 => F p.1.castSucc p.2.castSucc)
  rw [← hL, ← hF]
  simp [q9EdgePairs, q9EdgePairs8, Fintype.sum_prod_type,
    Finset.sum_filter, Fin.sum_univ_succ]
  ring

set_option maxHeartbeats 0 in
lemma q9_finite_branch_sum_formula
    (g : Fin 9 → Fin 73) (hg : ∀ i : Fin 9, (g i).val < 72) :
    (∑ p : {p // p ∈ q9EdgePairs},
      ((q9EdgeColorFast (g p.1.1).val (g p.1.2).val : Nat) : ZMod 36)) =
      8 * ∑ i : Fin 9, ((((g i).val + 1) / 2 : Nat) : ZMod 36) -
        (Nat.choose (∑ i : Fin 9, (g i).val % 2) 2 : ZMod 36) := by
  let x : Fin 8 → Nat := fun i => (g i.castSucc).val
  let z : Nat := (g (8 : Fin 9)).val
  have hx : ∀ i, x i < 72 := by intro i; exact hg i.castSucc
  have hz : z < 72 := hg 8
  have hfirst := q9_finite_edge_sum_zmod x hx
  have hlast :
      (∑ i : Fin 8,
        ((q9EdgeColorFast (x i) z : Nat) : ZMod 36)) =
      ∑ i : Fin 8,
        ((((x i + 1) / 2 : Nat) : ZMod 36) +
          (((z + 1) / 2 : Nat) : ZMod 36) -
          ((x i % 2 : Nat) : ZMod 36) * ((z % 2 : Nat) : ZMod 36)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [q9_edge_formula_zmod (hx i) hz]
  have hlast' :
      (∑ i : Fin 8,
        ((((x i + 1) / 2 : Nat) : ZMod 36) +
          (((z + 1) / 2 : Nat) : ZMod 36) -
          ((x i % 2 : Nat) : ZMod 36) * ((z % 2 : Nat) : ZMod 36))) =
        (∑ i : Fin 8, (((x i + 1) / 2 : Nat) : ZMod 36)) +
          8 * (((z + 1) / 2 : Nat) : ZMod 36) -
          (∑ i : Fin 8, ((x i % 2 : Nat) : ZMod 36)) *
            ((z % 2 : Nat) : ZMod 36) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [← Finset.sum_mul]
    have hcard : (Finset.univ : Finset (Fin 8)).card = 8 := by decide
    rw [hcard]
    ring
  have hsplit := q9_split_sum_general_zmod
    (fun a b : Fin 9 => ((q9EdgeColorFast (g a).val (g b).val : Nat) : ZMod 36)) g
  rw [hsplit, hfirst, hlast]
  rw [hlast']
  have hsumu :
      (∑ i : Fin 8, (((x i + 1) / 2 : Nat) : ZMod 36)) +
          (((z + 1) / 2 : Nat) : ZMod 36) =
        ∑ i : Fin 9, ((((g i).val + 1) / 2 : Nat) : ZMod 36) := by
    simp [x, z, Fin.sum_univ_succ]
    ring
  have hsume :
      (∑ i : Fin 8, ((x i % 2 : Nat) : ZMod 36)) +
          ((z % 2 : Nat) : ZMod 36) =
        ((∑ i : Fin 9, (g i).val % 2 : Nat) : ZMod 36) := by
    rw [Nat.cast_sum]
    simp [x, z, Fin.sum_univ_succ]
    ring
  have hzbit : z % 2 = 0 ∨ z % 2 = 1 := by omega
  have hrbit : ∀ i : Fin 8, x i % 2 = 0 ∨ x i % 2 = 1 := by intro i; omega
  have hchoose :
      (Nat.choose (∑ i : Fin 8, x i % 2) 2 : ZMod 36) +
        (((∑ i : Fin 8, x i % 2 : Nat) : ZMod 36) * ((z % 2 : Nat) : ZMod 36)) =
      (Nat.choose (∑ i : Fin 9, (g i).val % 2) 2 : ZMod 36) := by
    have hsum_nat : ∑ i : Fin 9, (g i).val % 2 =
        (∑ i : Fin 8, x i % 2) + z % 2 := by
      simp [x, z, Fin.sum_univ_succ, add_assoc, add_left_comm, add_comm]
    rw [hsum_nat]
    rcases hzbit with hzbit | hzbit
    · simp [hzbit]
    · have hn : (∑ i : Fin 8, x i % 2) + 1 =
          Nat.succ (∑ i : Fin 8, x i % 2) := by omega
      have htarget :
          (∑ i : Fin 8, x i % 2) + z % 2 =
            Nat.succ (∑ i : Fin 8, x i % 2) := by
        rw [hzbit]
      rw [htarget, Nat.choose_succ_succ]
      rw [hzbit]
      rw [Nat.choose_one_right]
      simp only [Nat.cast_add, Nat.cast_one, mul_one]
      ring
  have hprod :
      (∑ p : {p // p ∈ q9EdgePairs8},
        ((x p.1.1 % 2 : Nat) : ZMod 36) *
          ((x p.1.2 % 2 : Nat) : ZMod 36)) =
        (Nat.choose (∑ i : Fin 8, x i % 2) 2 : ZMod 36) := by
    simpa only [Nat.cast_mul] using q9_pair_bit_sum_choose
      (fun i : Fin 8 => x i % 2) hrbit
  rw [hprod]
  rw [← hsumu, ← hchoose]
  rw [Nat.cast_sum]
  ring

set_option maxHeartbeats 0 in
lemma q9_split_odd_count (g : Fin 9 → Fin 73)
    (h8 : (g (8 : Fin 9)).val = 72)
    (hfin : ∀ i : Fin 8, (g i.castSucc).val < 72) :
    (Finset.filter
      (fun p : {p // p ∈ q9EdgePairs} =>
        (q9Coloring.color (g p.1.1) (g p.1.2)).val % 2 = 1)
      Finset.univ).card =
      (Finset.filter
        (fun p : {p // p ∈ q9EdgePairs8} =>
          q9EdgeColorFast (g p.1.1.castSucc) (g p.1.2.castSucc).val % 2 = 1)
        Finset.univ).card +
      (Finset.filter
        (fun i : Fin 8 => q9EdgeColorFast 72 (g i.castSucc).val % 2 = 1)
        Finset.univ).card := by
  classical
  let F : Fin 9 → Fin 9 → Nat := fun a b =>
    if (q9Coloring.color (g a) (g b)).val % 2 = 1 then 1 else 0
  have hsplit := q9_split_sum_general F g h8 hfin
  have hcardL :
      (Finset.filter
        (fun p : {p // p ∈ q9EdgePairs} =>
          (q9Coloring.color (g p.1.1) (g p.1.2)).val % 2 = 1)
        Finset.univ).card =
      ∑ p : {p // p ∈ q9EdgePairs}, F p.1.1 p.1.2 := by
    rw [Finset.card_filter]
  have hcardF :
      (Finset.filter
        (fun p : {p // p ∈ q9EdgePairs8} =>
          q9EdgeColorFast (g p.1.1.castSucc) (g p.1.2.castSucc).val % 2 = 1)
        Finset.univ).card =
      ∑ p : {p // p ∈ q9EdgePairs8}, F p.1.1.castSucc p.1.2.castSucc := by
    rw [Finset.card_filter]
    simp [F, q9Color_val_fast]
  have hcardI :
      (Finset.filter
        (fun i : Fin 8 => q9EdgeColorFast 72 (g i.castSucc).val % 2 = 1)
        Finset.univ).card =
      ∑ i : Fin 8, F i.castSucc 8 := by
    have hg8 : g (8 : Fin 9) = ⟨72, by omega⟩ := Fin.ext h8
    have hfinite_ne : ∀ i : Fin 8, (g i.castSucc).val ≠ 72 := by
      intro i
      exact Nat.ne_of_lt (hfin i)
    rw [Finset.card_filter]
    simp [F, q9Color_val_fast, q9EdgeColorFast, hg8, hfinite_ne]
  rw [hcardL, hsplit, ← hcardF, ← hcardI]

lemma q9OddColorCount :
    (Finset.filter (fun c : Fin 36 => c.val % 2 = 1) Finset.univ).card = 18 := by
  decide

lemma q9_injective_oddColor_count {α : Type*} [Fintype α]
    (f : α → Fin 36) (hf : Function.Injective f)
    (hcard : Fintype.card α = 36) :
    (Finset.filter (fun a : α => (f a).val % 2 = 1) Finset.univ).card = 18 := by
  let oddα : Finset α := Finset.filter (fun a : α => (f a).val % 2 = 1) Finset.univ
  let oddC : Finset (Fin 36) := Finset.filter (fun c : Fin 36 => c.val % 2 = 1) Finset.univ
  have himage : Finset.univ.image f = (Finset.univ : Finset (Fin 36)) := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injective _ hf]
    simpa [hcard]
  have hodd_image : oddα.image f = oddC := by
    ext c
    constructor
    · intro hc
      rcases Finset.mem_image.mp hc with ⟨a, ha, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mp ha |>.2⟩
    · intro hc
      have hc_all : c ∈ Finset.univ.image f := by simpa [himage] using hc
      rcases Finset.mem_image.mp hc_all with ⟨a, _, ha⟩
      have hcodd : c.val % 2 = 1 := Finset.mem_filter.mp hc |>.2
      have haodd : (f a).val % 2 = 1 := by simpa [ha] using hcodd
      exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, haodd⟩, ha⟩
  have hcard_odd : oddα.card = oddC.card := by
    rw [← hodd_image]
    exact ((Finset.card_image_iff (s := oddα) (f := f)).mpr (by
      intro a ha b hb hab
      exact hf hab)).symm
  simpa [oddα, oddC] using hcard_odd.trans (by simpa [oddC] using q9OddColorCount)

lemma q9Rainbow_odd_edge_count
    {g : Fin 9 ↪ Fin 73}
    (hf : ∀ ⦃a b c d : Fin 9⦄,
      (SimpleGraph.completeGraph (Fin 9)).Adj a b →
      (SimpleGraph.completeGraph (Fin 9)).Adj c d →
      ¬ SameUndirectedEdge (g a) (g b) (g c) (g d) →
      q9Coloring.color (g a) (g b) ≠ q9Coloring.color (g c) (g d)) :
    (Finset.filter
      (fun p : {p // p ∈ q9EdgePairs} =>
        (q9Coloring.color (g p.1.1) (g p.1.2)).val % 2 = 1)
      Finset.univ).card = 18 := by
  apply q9_injective_oddColor_count
    (fun p : {p // p ∈ q9EdgePairs} =>
      q9Coloring.color (g p.1.1) (g p.1.2))
  · exact q9Rainbow_edge_color_injective hf
  · exact q9EdgePairs_card

lemma q9Rainbow_edge_sum_zmod_18
    {g : Fin 9 ↪ Fin 73}
    (hf : ∀ ⦃a b c d : Fin 9⦄,
      (SimpleGraph.completeGraph (Fin 9)).Adj a b →
      (SimpleGraph.completeGraph (Fin 9)).Adj c d →
      ¬ SameUndirectedEdge (g a) (g b) (g c) (g d) →
      q9Coloring.color (g a) (g b) ≠ q9Coloring.color (g c) (g d)) :
    ∑ p : {p // p ∈ q9EdgePairs},
      ((q9Coloring.color (g p.1.1) (g p.1.2)).val : ZMod 36) = 18 := by
  have hsum := q9Rainbow_edge_color_sum hf
  rw [← Nat.cast_sum]
  rw [hsum]
  decide

set_option maxHeartbeats 0 in
lemma q9_finite_branch_candidate
    {g : Fin 9 ↪ Fin 73}
    (hfin : ∀ i : Fin 9, (g i).val < 72)
    (hf : ∀ ⦃a b c d : Fin 9⦄,
      (SimpleGraph.completeGraph (Fin 9)).Adj a b →
      (SimpleGraph.completeGraph (Fin 9)).Adj c d →
      ¬ SameUndirectedEdge (g a) (g b) (g c) (g d) →
      q9Coloring.color (g a) (g b) ≠ q9Coloring.color (g c) (g d))
    (r s : Nat) (hr : r ≤ 8)
    (hc : r.choose 2 ≤ 8 * s)
    (hs : s = ∑ i : Fin 9, ((g i).val + 1) / 2)
    (hrsum : r = ∑ i : Fin 9, (g i).val % 2) : r = 4 ∨ r = 5 := by
  have hformula := q9_finite_branch_sum_formula (fun i : Fin 9 => g i) hfin
  have heq := q9Rainbow_edge_sum_zmod_18 hf
  simp_rw [q9Color_val_fast] at heq
  have hformula' :
      8 * ∑ i : Fin 9, ((((g i).val + 1) / 2 : Nat) : ZMod 36) -
        (Nat.choose (∑ i : Fin 9, (g i).val % 2) 2 : ZMod 36) = 18 := by
    calc
      _ = ∑ p : {p // p ∈ q9EdgePairs},
          ((q9EdgeColorFast (g p.1.1).val (g p.1.2).val : Nat) : ZMod 36) :=
        hformula.symm
      _ = 18 := heq
  have hsumu :
      (∑ i : Fin 9, ((((g i).val + 1) / 2 : Nat) : ZMod 36)) =
        ((∑ i : Fin 9, ((g i).val + 1) / 2 : Nat) : ZMod 36) := by
    rw [Nat.cast_sum]
  rw [hsumu, ← hs, ← hrsum] at hformula'
  exact q9_no_infty_zmod_candidate r s hr hc hformula'

lemma q9_infty_branch_color_sum_equation
    {g : Fin 9 ↪ Fin 73}
    (h8 : (g (8 : Fin 9)).val = 72)
    (hfin : ∀ i : Fin 8, (g i.castSucc).val < 72)
    (hf : ∀ ⦃a b c d : Fin 9⦄,
      (SimpleGraph.completeGraph (Fin 9)).Adj a b →
      (SimpleGraph.completeGraph (Fin 9)).Adj c d →
      ¬ SameUndirectedEdge (g a) (g b) (g c) (g d) →
      q9Coloring.color (g a) (g b) ≠ q9Coloring.color (g c) (g d)) :
    (∑ p : {p // p ∈ q9EdgePairs8},
      ((q9EdgeColorFast ((g p.1.1.castSucc).val)
        ((g p.1.2.castSucc).val) : Nat) : ZMod 36)) +
      ∑ i : Fin 8,
        ((q9EdgeColorFast 72 ((g i.castSucc).val) : Nat) : ZMod 36) = 18 := by
  have h := q9Rainbow_edge_sum_zmod_18 hf
  simp_rw [q9Color_val_fast] at h
  rw [q9_split_edges_sum_zmod (g := fun i => g i) h8 hfin] at h
  exact h

set_option maxHeartbeats 0 in
lemma q9_infty_branch_candidate
    {g : Fin 9 ↪ Fin 73}
    (h8 : (g (8 : Fin 9)).val = 72)
    (hfin : ∀ i : Fin 8, (g i.castSucc).val < 72)
    (hf : ∀ ⦃a b c d : Fin 9⦄,
      (SimpleGraph.completeGraph (Fin 9)).Adj a b →
      (SimpleGraph.completeGraph (Fin 9)).Adj c d →
      ¬ SameUndirectedEdge (g a) (g b) (g c) (g d) →
      q9Coloring.color (g a) (g b) ≠ q9Coloring.color (g c) (g d))
    (r s : Nat) (hr : r ≤ 7)
    (hc : r + r.choose 2 ≤ 9 * s)
    (hs : s = ∑ i : Fin 8, ((g i.castSucc).val + 1) / 2)
    (hrsum : r = ∑ i : Fin 8, (g i.castSucc).val % 2) : r = 0 := by
  let x : Fin 8 → Nat := fun i => (g i.castSucc).val
  have hx : ∀ i, x i < 72 := by
    intro i
    exact hfin i
  have hformula := q9_infty_branch_sum_formula x hx
  have heq := q9_infty_branch_color_sum_equation h8 hfin hf
  have hformula' :
      9 * ∑ i : Fin 8, (((x i + 1) / 2 : Nat) : ZMod 36) -
        ∑ i : Fin 8, ((x i % 2 : Nat) : ZMod 36) -
        (Nat.choose (∑ i : Fin 8, x i % 2) 2 : ZMod 36) = 18 := by
    calc
      _ = (∑ p : {p // p ∈ q9EdgePairs8},
          ((q9EdgeColorFast (x p.1.1) (x p.1.2) : Nat) : ZMod 36)) +
          ∑ i : Fin 8, ((q9EdgeColorFast 72 (x i) : Nat) : ZMod 36) :=
        hformula.symm
      _ = 18 := by simpa [x] using heq
  have hsumu :
      (∑ i : Fin 8, (((x i + 1) / 2 : Nat) : ZMod 36)) =
        ((∑ i : Fin 8, (x i + 1) / 2 : Nat) : ZMod 36) := by
    rw [Nat.cast_sum]
  have hsume :
      (∑ i : Fin 8, ((x i % 2 : Nat) : ZMod 36)) =
        ((∑ i : Fin 8, x i % 2 : Nat) : ZMod 36) := by
    rw [Nat.cast_sum]
  rw [hsumu, hsume, ← hs, ← hrsum] at hformula'
  exact q9_infty_zmod_candidate r s hr hc hformula'

set_option maxHeartbeats 0 in
lemma q9_infty_branch_no_rainbow
    {g : Fin 9 ↪ Fin 73}
    (hzero : g (0 : Fin 9) = 0)
    (h8 : (g (8 : Fin 9)).val = 72)
    (hfin : ∀ i : Fin 8, (g i.castSucc).val < 72)
    (hf : ∀ ⦃a b c d : Fin 9⦄,
      (SimpleGraph.completeGraph (Fin 9)).Adj a b →
      (SimpleGraph.completeGraph (Fin 9)).Adj c d →
      ¬ SameUndirectedEdge (g a) (g b) (g c) (g d) →
      q9Coloring.color (g a) (g b) ≠ q9Coloring.color (g c) (g d)) : False := by
  let x : Fin 8 → Nat := fun i => (g i.castSucc).val
  let r : Nat := ∑ i : Fin 8, x i % 2
  let s : Nat := ∑ i : Fin 8, (x i + 1) / 2
  have hx : ∀ i, x i < 72 := by
    intro i
    exact hfin i
  have hx0 : x 0 = 0 := by
    simpa [x] using congrArg Fin.val hzero
  have hrbit : ∀ i, x i % 2 ≤ 1 := by
    intro i
    omega
  have hr0 : x 0 % 2 = 0 := by simp [hx0]
  have hr : r ≤ 7 := by
    have hsum := Finset.sum_le_card_nsmul
      (Finset.univ.erase (0 : Fin 8)) (fun i : Fin 8 => x i % 2) 1
      (by intro i hi; exact hrbit i)
    have hcard : (Finset.univ.erase (0 : Fin 8)).card = 7 := by decide
    have hsum' : (Finset.univ.erase (0 : Fin 8)).sum
        (fun i : Fin 8 => x i % 2) ≤ 7 := by
      simpa [hcard, nsmul_eq_mul] using hsum
    have hdecomp := Finset.sum_erase_add (Finset.univ : Finset (Fin 8))
      (fun i : Fin 8 => x i % 2) (Finset.mem_univ (0 : Fin 8))
    dsimp [r]
    rw [← hdecomp]
    omega
  have hrsum : r = ∑ i : Fin 8, x i % 2 := by rfl
  have hs : s = ∑ i : Fin 8, (x i + 1) / 2 := by rfl
  have hsum_le : (∑ i : Fin 8, x i % 2) ≤
      ∑ i : Fin 8, (x i + 1) / 2 := by
    apply Finset.sum_le_sum
    intro i hi
    omega
  have hrs : r ≤ s := by simpa [r, s] using hsum_le
  have hc : r + r.choose 2 ≤ 9 * s := by
    have hchoose : r.choose 2 ≤ 8 * r := by
      interval_cases r <;> norm_num [Nat.choose]
    omega
  have hrzero : r = 0 :=
    q9_infty_branch_candidate h8 hfin hf r s hr hc hs hrsum
  have heven : ∀ i, x i % 2 = 0 := by
    intro i
    have hle : x i % 2 ≤ r := by
      dsimp [r]
      exact Finset.single_le_sum (s := Finset.univ) (f := fun j => x j % 2)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  have hodd_fin :
      (Finset.filter
        (fun p : {p // p ∈ q9EdgePairs8} =>
          q9EdgeColorFast (x p.1.1) (x p.1.2) % 2 = 1)
        Finset.univ).card ≤ 16 :=
    q9_even_finite_odd_le16 x hx heven
  have hodd_all := q9Rainbow_odd_edge_count hf
  have hsplit := q9_split_odd_count (g := fun i => g i) h8 hfin
  have hinf_zero :
      (Finset.filter
        (fun i : Fin 8 => q9EdgeColorFast 72 (g i.castSucc).val % 2 = 1)
        Finset.univ).card = 0 := by
    apply Finset.card_eq_zero.mpr
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hi'
      have hcolor : q9EdgeColorFast 72 (g i.castSucc).val % 2 = 0 := by
        rw [q9_infty_edge_formula_nat]
        have hei := heven i
        have hmod : (g i.castSucc).val % 36 % 2 =
            (g i.castSucc).val % 2 := by
          rw [Nat.mod_mod_of_dvd _ (by norm_num : 2 ∣ 36)]
        rw [hmod]
        exact hei
      omega
    · intro hi
      exact False.elim (by simpa using hi)
  have hfin_le :
      (Finset.filter
        (fun p : {p // p ∈ q9EdgePairs8} =>
          q9EdgeColorFast (g p.1.1.castSucc).val
            (g p.1.2.castSucc).val % 2 = 1)
        Finset.univ).card ≤ 16 := by
    simpa [x] using hodd_fin
  rw [hsplit, hinf_zero] at hodd_all
  omega

lemma q9Rainbow_edge_sum_mod36
    {g : Fin 9 ↪ Fin 73}
    (hf : ∀ ⦃a b c d : Fin 9⦄,
      (SimpleGraph.completeGraph (Fin 9)).Adj a b →
      (SimpleGraph.completeGraph (Fin 9)).Adj c d →
      ¬ SameUndirectedEdge (g a) (g b) (g c) (g d) →
      q9Coloring.color (g a) (g b) ≠ q9Coloring.color (g c) (g d)) :
    (∑ p : {p // p ∈ q9EdgePairs},
      (q9Coloring.color (g p.1.1) (g p.1.2)).val) % 36 = 18 := by
  rw [q9Rainbow_edge_color_sum hf]

end Erdos811
