import Q8PaperInfinityArithmeticBridge
import Q8PaperTranslation
import Q8PaperResidueCertificate

namespace Erdos811

/-! The first normalization layer for an arbitrary infinity embedding.

  `q8TranslateNat` acts on the finite seven-point data while fixing 56.
  These lemmas expose the zero-anchor and residue-list consequences without
  yet choosing an ordering of the seven vertices.
-/

def q8TranslateVector (s : Nat) (x : Fin 7 → Nat) : Fin 7 → Nat :=
  fun i => q8TranslateNat s (x i)

lemma q8Pairs_mem_of_lt {i j : Fin 8} (hij : i < j) :
    (i, j) ∈ q8Pairs := by
  fin_cases i <;> fin_cases j <;> simp_all [q8Pairs]

lemma q8Pairs_mem_of_ne {i j : Fin 8} (hne : i ≠ j) :
    (i, j) ∈ q8Pairs ∨ (j, i) ∈ q8Pairs := by
  have hcases : i < j ∨ j < i := by omega
  rcases hcases with hij | hji
  · exact Or.inl (q8Pairs_mem_of_lt hij)
  · exact Or.inr (q8Pairs_mem_of_lt hji)

def q8CanonicalPair (i j : Fin 8) : Fin 8 × Fin 8 :=
  if i < j then (i, j) else (j, i)

lemma q8CanonicalPair_mem {i j : Fin 8} (hne : i ≠ j) :
    q8CanonicalPair i j ∈ q8Pairs := by
  by_cases hij : i < j
  · simp [q8CanonicalPair, hij]
    exact q8Pairs_mem_of_lt hij
  · have hji : j < i := by omega
    simp [q8CanonicalPair, hij, hji]
    exact q8Pairs_mem_of_lt hji

lemma q8CanonicalPair_color (x : Fin 8 → Nat) {i j : Fin 8} (hne : i ≠ j) :
    q8PaperColorNat (x (q8CanonicalPair i j).1)
        (x (q8CanonicalPair i j).2) =
      q8PaperColorNat (x i) (x j) := by
  by_cases hij : i < j
  · simp [q8CanonicalPair, hij]
  · have hji : j < i := by omega
    simp [q8CanonicalPair, hij, hji, q8PaperColorNat_comm]

lemma q8CanonicalPair_reindex_injective (rho : Fin 8 → Fin 8)
    (hrho : Function.Injective rho) {p q : Fin 8 × Fin 8}
    (hp : p ∈ q8Pairs) (hq : q ∈ q8Pairs)
    (heq : q8CanonicalPair (rho p.1) (rho p.2) =
      q8CanonicalPair (rho q.1) (rho q.2)) :
    p = q := by
  have hpord := q8Pairs_ordered p hp
  have hqord := q8Pairs_ordered q hq
  by_cases hp' : rho p.1 < rho p.2
  · by_cases hq' : rho q.1 < rho q.2
    · simp [q8CanonicalPair, hp', hq'] at heq
      exact Prod.ext (hrho heq.1) (hrho heq.2)
    · have hqne : rho q.1 ≠ rho q.2 := hrho.ne (ne_of_lt hqord)
      have hq'' : rho q.2 < rho q.1 := by omega
      simp [q8CanonicalPair, hp', hq', hq''] at heq
      have h1 : p.1 = q.2 := hrho heq.1
      have h2 : p.2 = q.1 := hrho heq.2
      exfalso
      omega
  · have hp'' : rho p.2 < rho p.1 := by
      have hne : rho p.1 ≠ rho p.2 := hrho.ne (by
        intro h
        exact (ne_of_lt hpord) h)
      omega
    by_cases hq' : rho q.1 < rho q.2
    · simp [q8CanonicalPair, hp', hp'', hq'] at heq
      have h1 : p.2 = q.1 := hrho heq.1
      have h2 : p.1 = q.2 := hrho heq.2
      exfalso
      omega
    · have hqne : rho q.1 ≠ rho q.2 := hrho.ne (ne_of_lt hqord)
      have hq'' : rho q.2 < rho q.1 := by omega
      simp [q8CanonicalPair, hp', hp'', hq', hq''] at heq
      exact Prod.ext (hrho heq.2) (hrho heq.1)

lemma q8TranslateNat_shift_to_zero {v : Nat} (hv : v < 56) :
    q8TranslateNat (56 - v) v = 0 := by
  have hv0 : v = 0 ∨ 0 < v := by omega
  rcases hv0 with rfl | hv0
  · simp [q8TranslateNat]
  · have hsub : 56 - v < 56 := by omega
    have hmod : (56 - v) % 56 = 56 - v := Nat.mod_eq_of_lt hsub
    have hsum : v + (56 - v) = 56 := by omega
    have hvne : v ≠ 56 := by omega
    simp only [q8TranslateNat, hvne, hsum]
    simp

lemma q8TranslateVector_finite (s : Nat) (x : Fin 7 → Nat)
    (hfin : ∀ i, x i < 56) :
    ∀ i, q8TranslateVector s x i < 56 := by
  intro i
  exact q8TranslateNat_finite s (x i) (hfin i)

lemma q8TranslateVector_injective (s : Nat) (x : Fin 7 → Nat)
    (hfin : ∀ i, x i < 56) (hxi : Function.Injective x) :
    Function.Injective (q8TranslateVector s x) := by
  intro i j hij
  apply hxi
  apply q8TranslateNat_injective s (x i) (x j)
    (Nat.le_of_lt (hfin i)) (Nat.le_of_lt (hfin j))
  simpa only [q8TranslateVector] using hij

lemma q8TranslateVector_shift_to_zero (x : Fin 7 → Nat) (k : Fin 7)
    (hfin : ∀ i, x i < 56) :
    q8TranslateVector (56 - x k) x k = 0 := by
  exact q8TranslateNat_shift_to_zero (hfin k)

lemma q8TranslateVector_residue_zero_mem (x : Fin 7 → Nat) (k : Fin 7)
    (hfin : ∀ i, x i < 56) :
    0 ∈ q8ResidueList (q8TranslateVector (56 - x k) x) := by
  unfold q8ResidueList
  apply List.mem_map.mpr
  refine ⟨q8TranslateVector (56 - x k) x k, ?_, ?_⟩
  · exact List.mem_ofFn.mpr ⟨k, rfl⟩
  · rw [q8TranslateVector_shift_to_zero x k hfin]

lemma q8TranslateVector_residue14 (s : Nat) (x : Fin 7 → Nat)
    (hfin : ∀ i, x i < 56) (i : Fin 7) :
    q8TranslateVector s x i % 14 = ((x i % 14 + s % 14) % 14) := by
  have hxi := hfin i
  have hne : x i ≠ 56 := by omega
  simp only [q8TranslateVector, q8TranslateNat, hne, ↓reduceIte]
  omega

lemma q8WithInfinity_injective (x : Fin 7 → Nat)
    (hfin : ∀ i, x i < 56) (hxi : Function.Injective x) :
    Function.Injective (q8WithInfinity x) := by
  intro i j h
  cases i using Fin.lastCases with
  | last =>
      cases j using Fin.lastCases with
      | last => rfl
      | cast j =>
          have hj := hfin j
          have hlast : (56 : Nat) = x j := by
            simpa only [q8WithInfinity, Fin.lastCases_last,
              Fin.lastCases_castSucc] using h
          exfalso
          omega
  | cast i =>
      cases j using Fin.lastCases with
      | last =>
          have hi := hfin i
          have hlast : x i = (56 : Nat) := by
            simpa only [q8WithInfinity, Fin.lastCases_last,
              Fin.lastCases_castSucc] using h
          exfalso
          omega
      | cast j =>
          have hij : x i = x j := by
            simpa only [q8WithInfinity, Fin.lastCases_last,
              Fin.lastCases_castSucc] using h
          have hij' : i = j := hxi hij
          subst j
          rfl

lemma q8ResidueList_translate (s : Nat) (x : Fin 7 → Nat)
    (hfin : ∀ i, x i < 56) :
    q8ResidueList (q8TranslateVector s x) =
      (q8ResidueList x).map (fun r => (r + s % 14) % 14) := by
  rw [q8ResidueList_explicit, q8ResidueList_explicit]
  simp only [List.map_cons, List.map_nil]
  have h0 := q8TranslateVector_residue14 s x hfin (0 : Fin 7)
  have h1 := q8TranslateVector_residue14 s x hfin (1 : Fin 7)
  have h2 := q8TranslateVector_residue14 s x hfin (2 : Fin 7)
  have h3 := q8TranslateVector_residue14 s x hfin (3 : Fin 7)
  have h4 := q8TranslateVector_residue14 s x hfin (4 : Fin 7)
  have h5 := q8TranslateVector_residue14 s x hfin (5 : Fin 7)
  have h6 := q8TranslateVector_residue14 s x hfin (6 : Fin 7)
  simp only [List.cons.injEq]
  simp [h0, h1, h2, h3, h4, h5, h6]

lemma q8WithInfinity_translate (s : Nat) (x : Fin 7 → Nat)
    (hfin : ∀ i, x i < 56) (i : Fin 8) :
    q8WithInfinity (q8TranslateVector s x) i =
      q8TranslateNat s (q8WithInfinity x i) := by
  cases i using Fin.lastCases with
  | last =>
      rw [q8WithInfinity_last, q8WithInfinity_last]
      simp [q8TranslateNat]
  | cast i =>
      simp [q8WithInfinity, q8TranslateVector, q8TranslateNat]

lemma q8Translate_pair_color (s : Nat) (x : Fin 7 → Nat)
    (hfin : ∀ i, x i < 56) (hxi : Function.Injective x)
    (ij : Fin 8 × Fin 8) (hij : ij ∈ q8Pairs) :
    q8PaperColorNat
        (q8WithInfinity (q8TranslateVector s x) ij.1)
        (q8WithInfinity (q8TranslateVector s x) ij.2) =
      (q8PaperColorNat (q8WithInfinity x ij.1)
        (q8WithInfinity x ij.2) + s) % 28 := by
  have hinf := q8WithInfinity_injective x hfin hxi
  have hneq : q8WithInfinity x ij.1 ≠ q8WithInfinity x ij.2 := by
    intro he
    apply (q8Pairs_ordered ij hij).ne
    exact hinf he
  rw [q8WithInfinity_translate s x hfin ij.1,
    q8WithInfinity_translate s x hfin ij.2]
  exact q8TranslateNat_color s _ _ hneq

def q8ShiftColor (s : Nat) (c : Fin 28) : Fin 28 :=
  ⟨(c.val + s) % 28, Nat.mod_lt _ (by decide)⟩

lemma q8FinitePairColors_translate (s : Nat) (x : Fin 7 → Nat)
    (hfin : ∀ i, x i < 56) (hxi : Function.Injective x) :
    q8FinitePairColors (q8WithInfinity (q8TranslateVector s x)) =
      (q8FinitePairColors (q8WithInfinity x)).map (q8ShiftColor s) := by
  simp only [q8FinitePairColors, List.map_map]
  apply List.map_congr_left
  intro ij hij
  apply Fin.ext
  change q8PaperColorNat
      (q8WithInfinity (q8TranslateVector s x) ij.1)
      (q8WithInfinity (q8TranslateVector s x) ij.2) =
    (q8PaperColorNat (q8WithInfinity x ij.1)
      (q8WithInfinity x ij.2) + s) % 28
  exact q8Translate_pair_color s x hfin hxi ij hij

lemma q8ShiftColor_injective (s : Nat) :
    Function.Injective (q8ShiftColor s) := by
  intro a b h
  apply Fin.ext
  have hval := congrArg Fin.val h
  simp only [q8ShiftColor] at hval
  omega

lemma q8FinitePairColors_translate_nodup (s : Nat) (x : Fin 7 → Nat)
    (hfin : ∀ i, x i < 56) (hxi : Function.Injective x)
    (hnd : (q8FinitePairColors (q8WithInfinity x)).Nodup) :
    (q8FinitePairColors (q8WithInfinity (q8TranslateVector s x))).Nodup := by
  rw [q8FinitePairColors_translate s x hfin hxi]
  exact List.Nodup.map (q8ShiftColor_injective s) hnd

/-! A single reusable package for the paper's zero-anchor normalization.

  The shift `56 - x k` sends the selected finite vertex to residue zero,
  keeps all seven entries finite, preserves injectivity, and therefore also
  preserves the rainbow (pair-colour `Nodup`) hypothesis.  The package is
  deliberately stated before any choice of sorted order; the classifier can
  consume these facts after the separate sorting lemmas.
-/
theorem q8ZeroAnchorPackage (x : Fin 7 → Nat) (k : Fin 7)
    (hfin : ∀ i, x i < 56) (hxi : Function.Injective x)
    (hnd : (q8FinitePairColors (q8WithInfinity x)).Nodup) :
    q8TranslateVector (56 - x k) x k = 0 ∧
      (∀ i, q8TranslateVector (56 - x k) x i < 56) ∧
      0 ∈ q8ResidueList (q8TranslateVector (56 - x k) x) ∧
      Function.Injective (q8TranslateVector (56 - x k) x) ∧
      (q8FinitePairColors
        (q8WithInfinity (q8TranslateVector (56 - x k) x))).Nodup := by
  refine ⟨q8TranslateVector_shift_to_zero x k hfin, ?_, ?_, ?_, ?_⟩
  · exact q8TranslateVector_finite (56 - x k) x hfin
  · exact q8TranslateVector_residue_zero_mem x k hfin
  · exact q8TranslateVector_injective (56 - x k) x hfin hxi
  · exact q8FinitePairColors_translate_nodup (56 - x k) x hfin hxi hnd

/-! Sorting now supplies exactly the shape consumed by the finite certificate.

  The input list is the ascending insertion sort of the seven residues.  Once
  zero is known to occur, it is the head; reversing that sorted list gives the
  descending representation `tail.reverse ++ [0]` used by the certificate.
  The quota and odd-count predicates are transported across this reversal by
  the permutation invariance proved in the arithmetic bridge.
-/
theorem q8SortedResidueClassifierInput (x : Fin 7 → Nat)
    (hfin : ∀ i, x i < 56)
    (hnd : (q8FinitePairColors (q8WithInfinity x)).Nodup)
    (hzero : 0 ∈ q8ResidueList x) :
    ∃ tail,
      List.insertionSort (fun a b : Nat => a ≤ b) (q8ResidueList x) =
        0 :: tail ∧
      tail.length = 6 ∧
      q8ResidueContinuation 0 tail ∧
      q8ResidueQuota (tail.reverse ++ [0]) = true ∧
      q8ResidueOddOK (tail.reverse ++ [0]) = true := by
  obtain ⟨tail, hsort⟩ := q8SortedResidue_zero_split x hzero
  have hlen : tail.length = 6 := by
    have hlen' := congrArg List.length hsort
    simp only [List.length_cons] at hlen'
    have hsortlen :
        (List.insertionSort (fun a b : Nat => a ≤ b) (q8ResidueList x)).length =
          7 := by
      calc
        (List.insertionSort (fun a b : Nat => a ≤ b) (q8ResidueList x)).length =
            (q8ResidueList x).length :=
          (q8ResidueList_perm_insertionSort x).length_eq
        _ = 7 := q8ResidueList_length x
    omega
  have hbound : ∀ v ∈ 0 :: tail, v < 14 := by
    intro v hv
    have hvsort : v ∈
        List.insertionSort (fun a b : Nat => a ≤ b) (q8ResidueList x) := by
      rw [hsort]
      exact hv
    have hver : v ∈ q8ResidueList x :=
      (List.mem_insertionSort (fun a b : Nat => a ≤ b)).1 hvsort
    unfold q8ResidueList at hver
    rcases List.mem_map.mp hver with ⟨w, hw, rfl⟩
    exact Nat.mod_lt _ (by decide)
  have hvalid : q8ResidueContinuation 0 tail :=
    q8ResidueContinuation_zero_of_sorted
      (hsort ▸ q8ResidueList_sorted_insertionSort x) hbound
  have hcond := q8InfinityResidueConditions_of_nodup x hfin hnd
  have hperm : (tail.reverse ++ [0]).Perm (q8ResidueList x) := by
    have hrev := List.reverse_perm
      (List.insertionSort (fun a b : Nat => a ≤ b) (q8ResidueList x))
    have hall := hrev.trans (q8ResidueList_perm_insertionSort x)
    simpa [hsort] using hall
  have hquota : q8ResidueQuota (tail.reverse ++ [0]) = true := by
    rw [q8ResidueQuota_perm hperm]
    exact hcond.1
  have hodd : q8ResidueOddOK (tail.reverse ++ [0]) = true := by
    rw [q8ResidueOddOK_perm hperm]
    exact hcond.2
  exact ⟨tail, hsort, hlen, hvalid, hquota, hodd⟩

theorem q8SortedResidueClassify (x : Fin 7 → Nat)
    (hfin : ∀ i, x i < 56)
    (hnd : (q8FinitePairColors (q8WithInfinity x)).Nodup)
    (hzero : 0 ∈ q8ResidueList x) :
    ∃ s : Fin 14, ∃ tail,
      List.insertionSort (fun a b : Nat => a ≤ b) (q8ResidueList x) =
        0 :: tail ∧
      (tail.reverse ++ [0]).Perm
        ([2,4,7,9,11,12,13].map (fun v => (v + s.val) % 14)) := by
  obtain ⟨tail, hsort, hlen, hvalid, hquota, hodd⟩ :=
    q8SortedResidueClassifierInput x hfin hnd hzero
  obtain ⟨s, hclass⟩ :=
    q8ResidueClassify_anchor_zero_translation tail hlen hvalid hquota hodd
  exact ⟨s, tail, hsort, hclass⟩

/-! The actual translated-vector handoff for an arbitrary finite support. -/
theorem q8TranslatedSortedResidueClassify (x : Fin 7 → Nat) (k : Fin 7)
    (hfin : ∀ i, x i < 56) (hxi : Function.Injective x)
    (hnd : (q8FinitePairColors (q8WithInfinity x)).Nodup) :
    ∃ s : Fin 14, ∃ tail,
      List.insertionSort (fun a b : Nat => a ≤ b)
          (q8ResidueList (q8TranslateVector (56 - x k) x)) =
        0 :: tail ∧
      (tail.reverse ++ [0]).Perm
        ([2,4,7,9,11,12,13].map (fun v => (v + s.val) % 14)) := by
  let y : Fin 7 → Nat := q8TranslateVector (56 - x k) x
  have hyfin : ∀ i, y i < 56 := by
    intro i
    exact q8TranslateVector_finite (56 - x k) x hfin i
  have hynd : (q8FinitePairColors (q8WithInfinity y)).Nodup := by
    exact q8FinitePairColors_translate_nodup (56 - x k) x hfin hxi hnd
  have hyzero : 0 ∈ q8ResidueList y := by
    exact q8TranslateVector_residue_zero_mem x k hfin
  obtain ⟨s, tail, hsort, hclass⟩ :=
    q8SortedResidueClassify y hyfin hynd hyzero
  exact ⟨s, tail, by simpa [y] using hsort, hclass⟩

/-! A permutation of seven residue-list entries can be pulled back to the
  original `Fin 7` indices.  This is the small combinatorial bridge needed
  before introducing the lift parameters of `q8NormalizedVertices`.
-/
lemma q8ResiduePerm_reindex (y : Fin 7 → Nat) {xs : List Nat}
    (hperm : (q8ResidueList y).Perm xs) (hxslen : xs.length = 7) :
    ∃ σ : Fin 7 → Fin 7,
      Function.Injective σ ∧
      (∀ i : Fin 7,
        y i % 14 = xs.get (Fin.cast hxslen.symm (σ i))) := by
  let σ : Fin 7 → Fin 7 := fun i =>
    Fin.cast hxslen (hperm.idxBij
      (Fin.cast (q8ResidueList_length y).symm i))
  have hσ : Function.Injective σ := by
    intro i j hij
    dsimp [σ] at hij
    have hidx : hperm.idxBij
        (Fin.cast (q8ResidueList_length y).symm i) =
        hperm.idxBij (Fin.cast (q8ResidueList_length y).symm j) := by
      exact Fin.cast_injective hxslen hij
    have hdom := hperm.idxBij_injective hidx
    apply Fin.ext
    simpa using congrArg Fin.val hdom
  refine ⟨σ, hσ, ?_⟩
  intro i
  have hget := hperm.getElem_idxBij_eq_getElem
    (Fin.cast (q8ResidueList_length y).symm i)
  have hget' : xs.get (Fin.cast hxslen.symm (σ i)) =
      (q8ResidueList y).get (Fin.cast (q8ResidueList_length y).symm i) := by
    simpa [σ] using hget
  rw [hget']
  rw [List.get_eq_getElem]
  simp only [q8ResidueList, List.getElem_map, List.getElem_ofFn]
  rfl

def q8ResidueSupportShift (s : Fin 14) : List Nat :=
  [2,4,7,9,11,12,13].map (fun v => (v + s.val) % 14)

def q8NormalizedResidueSupport : List Nat := [2,4,7,9,11,12,13]

lemma q8NormalizedResidueSupport_length :
    q8NormalizedResidueSupport.length = 7 := by
  rfl

lemma q8NormalizedResidueSupport_get (j : Fin 7) :
    q8NormalizedResidueSupport.get
        (Fin.cast q8NormalizedResidueSupport_length.symm j) =
      (![2, 4, 7, 9, 11, 12, 13] : Fin 7 → Nat) j := by
  fin_cases j <;> rfl

lemma q8NormalizedVertices_castSucc (t : Fin 7 → Nat) (j : Fin 7) :
    q8NormalizedVertices t j.castSucc =
      q8NormalizedResidueSupport.get
        (Fin.cast q8NormalizedResidueSupport_length.symm j) +
        14 * t j := by
  fin_cases j <;> rfl

lemma q8Normalized_reindex_values (z : Fin 7 → Nat)
    (σ : Fin 7 → Fin 7) (t : Fin 7 → Nat)
    (hσ : Function.Injective σ)
    (hz : ∀ i : Fin 7,
      z i = q8NormalizedResidueSupport.get
          (Fin.cast q8NormalizedResidueSupport_length.symm (σ i)) +
        14 * t i) :
    ∃ t' : Fin 7 → Nat, ∀ i : Fin 7,
      q8NormalizedVertices t' (Fin.castSucc (σ i)) = z i := by
  let e : Fin 7 ≃ Fin 7 :=
    Equiv.ofBijective σ ⟨hσ, Finite.surjective_of_injective hσ⟩
  let t' : Fin 7 → Nat := fun j => t (e.symm j)
  refine ⟨t', ?_⟩
  intro i
  rw [q8NormalizedVertices_castSucc]
  have he : e.symm (σ i) = i := by
    change e.symm (e i) = i
    exact e.symm_apply_apply i
  dsimp [t']
  rw [he]
  exact (hz i).symm

def q8ReindexFin8 (e : Fin 7 ≃ Fin 7) : Fin 8 → Fin 8 :=
  Fin.lastCases (Fin.last 7) (fun j => (e.symm j).castSucc)

lemma q8ReindexFin8_injective (e : Fin 7 ≃ Fin 7) :
    Function.Injective (q8ReindexFin8 e) := by
  intro i j h
  cases i using Fin.lastCases with
  | last =>
      cases j using Fin.lastCases with
      | last => rfl
      | cast j =>
          simp [q8ReindexFin8] at h
          have hne : (Fin.last 7) ≠ (e.symm j).castSucc := by
            exact (Fin.castSucc_ne_last (e.symm j)).symm
          exact (hne h).elim
  | cast i =>
      cases j using Fin.lastCases with
      | last =>
          simp [q8ReindexFin8] at h
          have hne : (e.symm i).castSucc ≠ (Fin.last 7) := by
            exact Fin.castSucc_ne_last (e.symm i)
          exact (hne h).elim
      | cast j =>
          have h' : (e.symm i).castSucc = (e.symm j).castSucc := by
            simpa [q8ReindexFin8] using h
          have h'' : e.symm i = e.symm j := (Fin.castSucc_injective 7) h'
          have hij : i = j := e.symm.injective h''
          exact congrArg Fin.castSucc hij

lemma q8WithInfinity_reindex (z w : Fin 7 → Nat) (e : Fin 7 ≃ Fin 7)
    (hvertex : ∀ j : Fin 7, w j = z (e.symm j)) :
    ∀ j : Fin 8, q8WithInfinity w j =
      q8WithInfinity z (q8ReindexFin8 e j) := by
  intro j
  cases j using Fin.lastCases with
  | last =>
      simp only [q8WithInfinity_last, q8ReindexFin8,
        Fin.lastCases_last]
  | cast j =>
      simp [q8ReindexFin8, q8WithInfinity, hvertex]

lemma q8FinitePairColors_reindex_nodup (z w : Fin 7 → Nat)
    (e : Fin 7 ≃ Fin 7)
    (hvertex : ∀ j : Fin 7, w j = z (e.symm j))
    (hnd : (q8FinitePairColors (q8WithInfinity z)).Nodup) :
    (q8FinitePairColors (q8WithInfinity w)).Nodup := by
  let rho : Fin 8 → Fin 8 := q8ReindexFin8 e
  have hrho : Function.Injective rho := q8ReindexFin8_injective e
  have hval (j : Fin 8) : q8WithInfinity w j = q8WithInfinity z (rho j) := by
    exact q8WithInfinity_reindex z w e hvertex j
  apply (List.nodup_iff_pairwise_ne).2
  apply (List.pairwise_map).2
  apply list_pairwise_of_mem_ne q8Pairs_nodup
  intro p hp q hq hpq hcol
  have hpord := q8Pairs_ordered p hp
  have hqord := q8Pairs_ordered q hq
  have hpne : p.1 ≠ p.2 := ne_of_lt hpord
  have hqne : q.1 ≠ q.2 := ne_of_lt hqord
  have hpsne : rho p.1 ≠ rho p.2 := hrho.ne hpne
  have hqsne : rho q.1 ≠ rho q.2 := hrho.ne hqne
  let ps : Fin 8 × Fin 8 := q8CanonicalPair (rho p.1) (rho p.2)
  let qs : Fin 8 × Fin 8 := q8CanonicalPair (rho q.1) (rho q.2)
  have hps : ps ∈ q8Pairs := by
    exact q8CanonicalPair_mem hpsne
  have hqs : qs ∈ q8Pairs := by
    exact q8CanonicalPair_mem hqsne
  have hcol' :
      q8PaperColorNat (q8WithInfinity z (rho p.1))
          (q8WithInfinity z (rho p.2)) =
        q8PaperColorNat (q8WithInfinity z (rho q.1))
          (q8WithInfinity z (rho q.2)) := by
    have hc := congrArg Fin.val hcol
    change q8PaperColorNat (q8WithInfinity w p.1)
          (q8WithInfinity w p.2) =
        q8PaperColorNat (q8WithInfinity w q.1)
          (q8WithInfinity w q.2) at hc
    rw [hval p.1, hval p.2, hval q.1, hval q.2] at hc
    exact hc
  have hpscol :
      q8PaperColorNat (q8WithInfinity z ps.1)
          (q8WithInfinity z ps.2) =
        q8PaperColorNat (q8WithInfinity z (rho p.1))
          (q8WithInfinity z (rho p.2)) := by
    exact q8CanonicalPair_color (q8WithInfinity z) hpsne
  have hqscol :
      q8PaperColorNat (q8WithInfinity z qs.1)
          (q8WithInfinity z qs.2) =
        q8PaperColorNat (q8WithInfinity z (rho q.1))
          (q8WithInfinity z (rho q.2)) := by
    exact q8CanonicalPair_color (q8WithInfinity z) hqsne
  have hsrc :
      q8PaperColorNat (q8WithInfinity z ps.1)
          (q8WithInfinity z ps.2) =
        q8PaperColorNat (q8WithInfinity z qs.1)
          (q8WithInfinity z qs.2) := by
    rw [hpscol, hqscol]
    exact hcol'
  have heq : ps = qs := by
    exact q8PairColor_injective_of_nodup (q8WithInfinity z) hnd hps hqs hsrc
  apply hpq
  exact q8CanonicalPair_reindex_injective rho hrho hp hq (by simpa [ps, qs] using heq)

lemma q8ResidueSupportShift_length (s : Fin 14) :
    (q8ResidueSupportShift s).length = 7 := by
  simp [q8ResidueSupportShift]

lemma q8ResidueSupportShift_get_lt (s : Fin 14) (i : Fin 7) :
    (q8ResidueSupportShift s).get
      (Fin.cast (q8ResidueSupportShift_length s).symm i) < 14 := by
  have hmem : (q8ResidueSupportShift s).get
      (Fin.cast (q8ResidueSupportShift_length s).symm i) ∈
      q8ResidueSupportShift s := List.get_mem _ _
  unfold q8ResidueSupportShift at hmem ⊢
  rcases List.mem_map.mp hmem with ⟨v, hv, hvget⟩
  rw [← hvget]
  exact Nat.mod_lt _ (by decide)

lemma q8ResidueSupportShift_inverse (s : Fin 14) :
    (q8ResidueSupportShift s).map
        (fun r => (r + (56 - s.val) % 14) % 14) =
      [2,4,7,9,11,12,13] := by
  fin_cases s <;> decide

theorem q8TranslatedResiduePermSupport (x : Fin 7 → Nat) (k : Fin 7)
    (hfin : ∀ i, x i < 56) (hxi : Function.Injective x)
    (hnd : (q8FinitePairColors (q8WithInfinity x)).Nodup) :
    ∃ s : Fin 14,
      (q8ResidueList (q8TranslateVector (56 - x k) x)).Perm
        ([2,4,7,9,11,12,13].map (fun v => (v + s.val) % 14)) := by
  obtain ⟨s, tail, hsort, hclass⟩ :=
    q8TranslatedSortedResidueClassify x k hfin hxi hnd
  let sorted := List.insertionSort (fun a b : Nat => a ≤ b)
    (q8ResidueList (q8TranslateVector (56 - x k) x))
  have hrev : sorted.reverse.Perm sorted := List.reverse_perm sorted
  have hsorted : sorted.Perm sorted.reverse := hrev.symm
  have hsortedSupport : sorted.Perm
      ([2,4,7,9,11,12,13].map (fun v => (v + s.val) % 14)) := by
    exact hsorted.trans (by simpa [sorted, hsort] using hclass)
  have hres :
      (q8ResidueList (q8TranslateVector (56 - x k) x)).Perm
        ([2,4,7,9,11,12,13].map (fun v => (v + s.val) % 14)) := by
    exact (q8ResidueList_perm_insertionSort
      (q8TranslateVector (56 - x k) x)).symm.trans hsortedSupport
  exact ⟨s, hres⟩

theorem q8TranslatedResiduePerm_normalized (x : Fin 7 → Nat) (k : Fin 7)
    (hfin : ∀ i, x i < 56) (hxi : Function.Injective x)
    (hnd : (q8FinitePairColors (q8WithInfinity x)).Nodup) :
    ∃ s : Fin 14,
      (q8ResidueList
        (q8TranslateVector (56 - s.val)
          (q8TranslateVector (56 - x k) x))).Perm
        q8NormalizedResidueSupport := by
  obtain ⟨s, hperm⟩ := q8TranslatedResiduePermSupport x k hfin hxi hnd
  let y : Fin 7 → Nat := q8TranslateVector (56 - x k) x
  have hyfin : ∀ i, y i < 56 := by
    intro i
    exact q8TranslateVector_finite (56 - x k) x hfin i
  let f : Nat → Nat := fun r => (r + (56 - s.val) % 14) % 14
  have hmap := hperm.map f
  have hcancel : (q8ResidueSupportShift s).map f =
      [2,4,7,9,11,12,13] := by
    simpa [f] using q8ResidueSupportShift_inverse s
  have hz := q8ResidueList_translate (56 - s.val) y hyfin
  refine ⟨s, ?_⟩
  rw [show q8TranslateVector (56 - s.val) y =
      q8TranslateVector (56 - s.val)
        (q8TranslateVector (56 - x k) x) by rfl]
  rw [q8ResidueList_translate (56 - s.val) y hyfin]
  exact hmap.trans (List.Perm.of_eq hcancel)

theorem q8NormalizedLiftParameters (x : Fin 7 → Nat) (k : Fin 7)
    (hfin : ∀ i, x i < 56) (hxi : Function.Injective x)
    (hnd : (q8FinitePairColors (q8WithInfinity x)).Nodup) :
    ∃ s : Fin 14, ∃ σ : Fin 7 → Fin 7, ∃ t : Fin 7 → Nat,
      Function.Injective σ ∧
      (∀ i : Fin 7,
        q8TranslateVector (56 - s.val)
            (q8TranslateVector (56 - x k) x) i =
          q8NormalizedResidueSupport.get
            (Fin.cast q8NormalizedResidueSupport_length.symm (σ i)) +
          14 * t i) := by
  obtain ⟨s, hperm⟩ := q8TranslatedResiduePerm_normalized x k hfin hxi hnd
  let z : Fin 7 → Nat := q8TranslateVector (56 - s.val)
    (q8TranslateVector (56 - x k) x)
  obtain ⟨σ, hσ, hres⟩ :=
    q8ResiduePerm_reindex z
      (by simpa [q8NormalizedResidueSupport] using hperm)
      q8NormalizedResidueSupport_length
  let t : Fin 7 → Nat := fun i => z i / 14
  refine ⟨s, σ, t, hσ, ?_⟩
  intro i
  have hdecomp := Nat.mod_add_div (z i) 14
  dsimp [z, t]
  calc
    q8TranslateVector (56 - s.val)
          (q8TranslateVector (56 - x k) x) i =
        z i % 14 + 14 * (z i / 14) := hdecomp.symm
    _ = q8NormalizedResidueSupport.get
          (Fin.cast q8NormalizedResidueSupport_length.symm (σ i)) +
        14 * (z i / 14) := by
      rw [hres i]

theorem q8TranslatedResidueReindex (x : Fin 7 → Nat) (k : Fin 7)
    (hfin : ∀ i, x i < 56) (hxi : Function.Injective x)
    (hnd : (q8FinitePairColors (q8WithInfinity x)).Nodup) :
    ∃ s : Fin 14, ∃ σ : Fin 7 → Fin 7,
      Function.Injective σ ∧
      (∀ i : Fin 7,
        q8TranslateVector (56 - x k) x i % 14 =
          (q8ResidueSupportShift s).get
            (Fin.cast (q8ResidueSupportShift_length s).symm (σ i))) := by
  obtain ⟨s, hperm⟩ := q8TranslatedResiduePermSupport x k hfin hxi hnd
  obtain ⟨σ, hσ, hpoint⟩ :=
    q8ResiduePerm_reindex (q8TranslateVector (56 - x k) x)
      (xs := q8ResidueSupportShift s)
      (by simpa [q8ResidueSupportShift] using hperm)
      (q8ResidueSupportShift_length s)
  exact ⟨s, σ, hσ, hpoint⟩

lemma q8ResidueLift_exists (v r : Nat) (hres : v % 14 = r) :
    ∃ t : Nat, v = r + 14 * t := by
  refine ⟨v / 14, ?_⟩
  have hdecomp := Nat.mod_add_div v 14
  omega

theorem q8TranslatedLiftParameters (x : Fin 7 → Nat) (k : Fin 7)
    (hfin : ∀ i, x i < 56) (hxi : Function.Injective x)
    (hnd : (q8FinitePairColors (q8WithInfinity x)).Nodup) :
    ∃ s : Fin 14, ∃ σ : Fin 7 → Fin 7, ∃ t : Fin 7 → Nat,
      Function.Injective σ ∧
      (∀ i : Fin 7,
        q8TranslateVector (56 - x k) x i =
          (q8ResidueSupportShift s).get
            (Fin.cast (q8ResidueSupportShift_length s).symm (σ i)) +
            14 * t i) := by
  obtain ⟨s, σ, hσ, hres⟩ :=
    q8TranslatedResidueReindex x k hfin hxi hnd
  let t : Fin 7 → Nat := fun i => q8TranslateVector (56 - x k) x i / 14
  refine ⟨s, σ, t, hσ, ?_⟩
  intro i
  have hdecomp := Nat.mod_add_div
    (q8TranslateVector (56 - x k) x i) 14
  dsimp [t]
  calc
    q8TranslateVector (56 - x k) x i =
        q8TranslateVector (56 - x k) x i % 14 +
          14 * (q8TranslateVector (56 - x k) x i / 14) := hdecomp.symm
    _ = (q8ResidueSupportShift s).get
          (Fin.cast (q8ResidueSupportShift_length s).symm (σ i)) +
          14 * (q8TranslateVector (56 - x k) x i / 14) := by
      rw [hres i]

theorem q8TranslatedLiftParameters_bounded (x : Fin 7 → Nat) (k : Fin 7)
    (hfin : ∀ i, x i < 56) (hxi : Function.Injective x)
    (hnd : (q8FinitePairColors (q8WithInfinity x)).Nodup) :
    ∃ s : Fin 14, ∃ σ : Fin 7 → Fin 7, ∃ t : Fin 7 → Nat,
      Function.Injective σ ∧
      (∀ i : Fin 7,
        q8TranslateVector (56 - x k) x i =
          (q8ResidueSupportShift s).get
            (Fin.cast (q8ResidueSupportShift_length s).symm (σ i)) +
            14 * t i) ∧
      (∀ i : Fin 7, t i < 4) := by
  obtain ⟨s, σ, t, hσ, hlift⟩ :=
    q8TranslatedLiftParameters x k hfin hxi hnd
  have hyfin : ∀ i, q8TranslateVector (56 - x k) x i < 56 :=
    q8TranslateVector_finite (56 - x k) x hfin
  refine ⟨s, σ, t, hσ, hlift, ?_⟩
  intro i
  have hr := q8ResidueSupportShift_get_lt s (σ i)
  have hv := hyfin i
  have heq := hlift i
  omega

theorem q8Normalized_nodup_transfer (x : Fin 7 → Nat) (k : Fin 7)
    (hfin : ∀ i, x i < 56) (hxi : Function.Injective x)
    (hnd : (q8FinitePairColors (q8WithInfinity x)).Nodup) :
    False := by
  obtain ⟨s, σ, t, hσ, hz⟩ :=
    q8NormalizedLiftParameters x k hfin hxi hnd
  let y : Fin 7 → Nat := q8TranslateVector (56 - x k) x
  let z : Fin 7 → Nat := q8TranslateVector (56 - s.val) y
  have hyfin : ∀ i, y i < 56 := by
    intro i
    exact q8TranslateVector_finite (56 - x k) x hfin i
  have hyxi : Function.Injective y := by
    exact q8TranslateVector_injective (56 - x k) x hfin hxi
  have hynd : (q8FinitePairColors (q8WithInfinity y)).Nodup := by
    exact q8FinitePairColors_translate_nodup (56 - x k) x hfin hxi hnd
  have hzfin : ∀ i, z i < 56 := by
    intro i
    exact q8TranslateVector_finite (56 - s.val) y hyfin i
  have hzxi : Function.Injective z := by
    exact q8TranslateVector_injective (56 - s.val) y hyfin hyxi
  have hznd : (q8FinitePairColors (q8WithInfinity z)).Nodup := by
    exact q8FinitePairColors_translate_nodup (56 - s.val) y hyfin hyxi hynd
  have hz' : ∀ i : Fin 7,
      z i = q8NormalizedResidueSupport.get
          (Fin.cast q8NormalizedResidueSupport_length.symm (σ i)) +
        14 * t i := by
    intro i
    exact hz i
  obtain ⟨t', hzt⟩ := q8Normalized_reindex_values z σ t hσ hz'
  let e : Fin 7 ≃ Fin 7 :=
    Equiv.ofBijective σ ⟨hσ, Finite.surjective_of_injective hσ⟩
  let w : Fin 7 → Nat := fun j => q8NormalizedVertices t' j.castSucc
  have hvertex : ∀ j : Fin 7,
      w j = z (e.symm j) := by
    intro j
    have hh := hzt (e.symm j)
    have he : σ (e.symm j) = j := by
      change e (e.symm j) = j
      exact e.apply_symm_apply j
    rw [he] at hh
    simpa [w] using hh
  have hnormw : (q8FinitePairColors (q8WithInfinity w)).Nodup := by
    exact q8FinitePairColors_reindex_nodup z w e hvertex hznd
  have hfull : q8WithInfinity w = q8NormalizedVertices t' := by
    funext j
    cases j using Fin.lastCases with
    | last =>
        rw [q8WithInfinity_last]
        rfl
    | cast j => simp [q8WithInfinity, w]
  have hnorm :
      (q8FinitePairColors (q8NormalizedVertices t')).Nodup := by
    rw [← hfull]
    exact hnormw
  exact q8NormalizedInfinity_not_nodup t' hnorm

#print axioms q8TranslateVector_injective
#print axioms q8ZeroAnchorPackage
#print axioms q8SortedResidueClassifierInput
#print axioms q8SortedResidueClassify
#print axioms q8TranslatedSortedResidueClassify
#print axioms q8ResiduePerm_reindex
#print axioms q8TranslatedResiduePermSupport
#print axioms q8TranslatedResidueReindex
#print axioms q8ResidueLift_exists
#print axioms q8TranslatedLiftParameters
#print axioms q8ResidueSupportShift_get_lt
#print axioms q8ResidueSupportShift_inverse
#print axioms q8TranslatedLiftParameters_bounded
#print axioms q8TranslatedResiduePerm_normalized
#print axioms q8NormalizedLiftParameters
#print axioms q8Normalized_nodup_transfer

end Erdos811
