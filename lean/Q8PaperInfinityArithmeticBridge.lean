import Q8PaperInfinityArithmetic

namespace Erdos811

/-!
  The arithmetic bridge is kept in a separate module from the definitions and
  local finite lemmas.  This keeps the ordinary import lightweight while still
  exposing the paper-level congruence and its parity consequence.
-/

lemma q8InfinityRawB_mod4 (x : Fin 7 → Nat) :
    (q8Pairs.map (q8InfinityRawB x)).sum % 4 =
      (4 - ((x 0 % 2 + x 1 % 2 + x 2 % 2 + x 3 % 2 +
        x 4 % 2 + x 5 % 2 + x 6 % 2) +
        Nat.choose (x 0 % 2 + x 1 % 2 + x 2 % 2 + x 3 % 2 +
          x 4 % 2 + x 5 % 2 + x 6 % 2) 2) % 4) % 4 := by
  let S : Nat := (q8Pairs.map (q8InfinityRawB x)).sum
  let B : Nat := (q8Pairs7.map (q8B7 x)).sum
  let P : Nat := (q8Pairs7.map (fun ij =>
    (x ij.1 % 2) * (x ij.2 % 2))).sum
  let A : Nat := (x 0 + 1) / 2 + (x 1 + 1) / 2 + (x 2 + 1) / 2 +
    (x 3 + 1) / 2 + (x 4 + 1) / 2 + (x 5 + 1) / 2 + (x 6 + 1) / 2
  let X : Nat := x 0 + x 1 + x 2 + x 3 + x 4 + x 5 + x 6
  let r : Nat := x 0 % 2 + x 1 % 2 + x 2 % 2 + x 3 % 2 +
    x 4 % 2 + x 5 % 2 + x 6 % 2
  change S % 4 = _
  have hBP : B + P = 6 * A := by
    dsimp [B, P, A]
    exact q8B7_sum_add_product x
  have hPC : P = Nat.choose r 2 := by
    dsimp [P, r]
    exact q8ParityProduct_sum_choose x
  have hXR : X + r = 2 * A := by
    dsimp [X, r, A]
    exact q8CeilHalf_relation x
  have hS : S = B + X := by
    dsimp [S, B, X]
    exact q8InfinityRawB_sum x
  have hEq : S + P = 4 * X + 3 * r := by
    omega
  have hPC' : P = Nat.choose
      (x 0 % 2 + x 1 % 2 + x 2 % 2 + x 3 % 2 +
        x 4 % 2 + x 5 % 2 + x 6 % 2) 2 := by
    simpa [r] using hPC
  have hmod : S % 4 = (4 - (r + P) % 4) % 4 := by
    have htotal : S + (r + P) = 4 * (X + r) := by
      omega
    have hzero : S + (r + P) ≡ 0 [MOD 4] := by
      rw [htotal]
      simp [Nat.ModEq]
    have hR : r + P ≡ (r + P) % 4 [MOD 4] := by
      simp [Nat.ModEq]
    have hSR : S + ((r + P) % 4) ≡ 0 [MOD 4] := by
      exact (Nat.ModEq.add (Nat.ModEq.refl S) hR).symm.trans hzero
    let R := (r + P) % 4
    have hRlt : R < 4 := by
      dsimp [R]
      exact Nat.mod_lt _ (by decide)
    have hslt : S % 4 < 4 := Nat.mod_lt _ (by decide)
    have hres : (S % 4 + R) % 4 = 0 := by
      have h := hSR
      simp only [Nat.ModEq] at h
      simpa [R, Nat.add_mod] using h
    by_cases hR0 : R = 0
    · have hS0 : S % 4 = 0 := by
        simpa [hR0] using hres
      simpa [R, hR0] using hS0
    · have hRpos : 0 < R := Nat.pos_of_ne_zero hR0
      have hmod' : S % 4 = 4 - R := by
        omega
      have hTlt : 4 - R < 4 := by omega
      have hmod4 : (4 - R) % 4 = 4 - R := Nat.mod_eq_of_lt hTlt
      simpa [R, hR0, hmod4] using hmod'
  calc
    S % 4 = (4 - (r + P) % 4) % 4 := hmod
    _ = _ := by simp [r, hPC']

theorem q8InfinityParity_three_or_four (x : Fin 7 → Nat)
    (hfin : ∀ i, x i < 56)
    (hnd : (q8FinitePairColors (q8WithInfinity x)).Nodup) :
    (x 0 % 2 + x 1 % 2 + x 2 % 2 + x 3 % 2 +
      x 4 % 2 + x 5 % 2 + x 6 % 2) = 3 ∨
      (x 0 % 2 + x 1 % 2 + x 2 % 2 + x 3 % 2 +
        x 4 % 2 + x 5 % 2 + x 6 % 2) = 4 := by
  have hsum := q8FinitePairColors_sum (q8WithInfinity x) hnd
  have hcol :
      ((q8FinitePairColors (q8WithInfinity x)).map (fun c => c.val)).sum % 4 = 2 := by
    rw [hsum]
  have hmod := q8InfinityColorSum_mod4 x hfin
  have hraw := q8InfinityRawB_mod4 x
  have htarget :
      (4 - ((x 0 % 2 + x 1 % 2 + x 2 % 2 + x 3 % 2 +
        x 4 % 2 + x 5 % 2 + x 6 % 2) +
    Nat.choose (x 0 % 2 + x 1 % 2 + x 2 % 2 + x 3 % 2 +
          x 4 % 2 + x 5 % 2 + x 6 % 2) 2) % 4) % 4 = 2 := by
    rw [← hraw]
    have hmod' :
        (q8Pairs.map (q8InfinityRawB x)).sum % 4 =
          ((q8FinitePairColors (q8WithInfinity x)).map
            (fun c => c.val)).sum % 4 := by
      simpa [Nat.ModEq] using hmod.symm
    exact hmod'.trans hcol
  apply q8OddResidue_candidates _ (by omega)
  exact htarget

/-! The two finite-residue filters used by the anchored classifier. -/
theorem q8InfinityResidueConditions_of_nodup (x : Fin 7 → Nat)
    (hfin : ∀ i, x i < 56)
    (hnd : (q8FinitePairColors (q8WithInfinity x)).Nodup) :
    q8ResidueQuota (q8ResidueList x) = true ∧
      q8ResidueOddOK (q8ResidueList x) = true := by
  have hpar := q8InfinityParity_three_or_four x hfin hnd
  exact ⟨q8ResidueQuota_of_nodup x hfin hnd,
    q8ResidueOddOK_of_parity_sum x hpar⟩

/-! Sorting facts used by the next normalization layer. -/
lemma q8ResidueList_perm_insertionSort (x : Fin 7 → Nat) :
    List.Perm (List.insertionSort (fun a b : Nat => a ≤ b) (q8ResidueList x))
      (q8ResidueList x) := by
  exact List.perm_insertionSort (fun a b : Nat => a ≤ b) (q8ResidueList x)

lemma q8ResidueList_sorted_insertionSort (x : Fin 7 → Nat) :
    (List.insertionSort (fun a b : Nat => a ≤ b) (q8ResidueList x)).Pairwise
      (fun a b : Nat => a ≤ b) := by
  exact List.pairwise_insertionSort (fun a b : Nat => a ≤ b) (q8ResidueList x)

lemma q8ResidueContinuation_of_sorted {lo : Nat} :
    ∀ {l : List Nat}, l.Pairwise (· ≤ ·) →
      (∀ v ∈ l, lo ≤ v) → (∀ v ∈ l, v < 14) →
      q8ResidueContinuation lo l := by
  intro l hsort
  induction l generalizing lo with
  | nil =>
      intro _ _
      trivial
  | cons v l ih =>
      intro hlower hbound
      have hvlo : lo ≤ v := hlower v (by simp)
      have hvlt : v < 14 := hbound v (by simp)
      refine ⟨hvlo, hvlt, ?_⟩
      apply ih (lo := v) hsort.tail
      · intro w hw
        exact (List.pairwise_cons.mp hsort).1 w hw
      · intro w hw
        exact hbound w (by simp [hw])

lemma q8ResidueContinuation_zero_of_sorted {tail : List Nat}
    (hsort : (0 :: tail).Pairwise (· ≤ ·))
    (hbound : ∀ v ∈ 0 :: tail, v < 14) :
    q8ResidueContinuation 0 tail := by
  apply q8ResidueContinuation_of_sorted (l := tail) hsort.tail
  · intro v hv
    exact (List.pairwise_cons.mp hsort).1 v hv
  · intro v hv
    exact hbound v (by simp [hv])

lemma q8Zero_cons_of_sorted_mem {l : List Nat}
    (hsort : l.Pairwise (fun a b : Nat => a ≤ b)) (hzero : 0 ∈ l) :
    ∃ tail, l = 0 :: tail := by
  cases l with
  | nil => simp at hzero
  | cons a l =>
      by_cases ha : a = 0
      · exact ⟨l, by simp [ha]⟩
      · have hapos : 0 < a := Nat.pos_of_ne_zero ha
        have hhead := (List.pairwise_cons.mp hsort).1
        simp only [List.mem_cons] at hzero
        rcases hzero with hzero | hzero
        · exact False.elim (ha hzero.symm)
        · exact False.elim (by
            have hle := hhead 0 hzero
            omega)

lemma q8SortedResidue_zero_split (x : Fin 7 → Nat)
    (hzero : 0 ∈ q8ResidueList x) :
    ∃ tail, List.insertionSort (fun a b : Nat => a ≤ b) (q8ResidueList x) =
      0 :: tail := by
  apply q8Zero_cons_of_sorted_mem (q8ResidueList_sorted_insertionSort x)
  exact (List.mem_insertionSort (fun a b : Nat => a ≤ b)).2 hzero

/-! Quota and odd-count predicates are invariant under sorting the vertices. -/
lemma q8ResidueEdgeColors_perm_of_perm {xs ys : List Nat} (h : xs.Perm ys) :
    List.Perm (q8ResidueEdgeColors xs) (q8ResidueEdgeColors ys) := by
  induction h using List.Perm.rec with
  | nil => rfl
  | @cons a xs ys h ih =>
      simp only [q8ResidueEdgeColors]
      exact List.Perm.append (List.Perm.cons _ (h.map _)) ih
  | swap x y l =>
      let a : Nat := y % 7
      let b : Nat := x % 7
      let c : Nat := (x + y + 1) / 2 % 7
      let my : List Nat := l.map (fun w => (y + w + 1) / 2 % 7)
      let mx : List Nat := l.map (fun w => (x + w + 1) / 2 % 7)
      let e : List Nat := q8ResidueEdgeColors l
      have hmid :
          ((a :: c :: my) ++ (b :: (mx ++ e))).Perm
            (b :: ((a :: c :: my) ++ (mx ++ e))) := by
        exact List.perm_middle
      have hmove :
          (a :: c :: my ++ mx).Perm (c :: (mx ++ a :: my)) := by
        have hc : ([a] ++ c :: (my ++ mx)).Perm
            (c :: ([a] ++ (my ++ mx))) := List.perm_middle
        have hm : ((a :: my) ++ mx).Perm (mx ++ (a :: my)) :=
          List.perm_append_comm
        exact hc.trans (List.Perm.cons c hm)
      have hmoveE :
          ((a :: c :: my) ++ (mx ++ e)).Perm
            (c :: (mx ++ a :: my) ++ e) := by
        simpa [List.append_assoc] using hmove.append_right e
      have hfinal := hmid.trans (List.Perm.cons b hmoveE)
      simpa [q8ResidueEdgeColors, a, b, c, my, mx, e, Nat.add_comm,
        List.append_assoc] using hfinal
  | trans h₁ h₂ ih₁ ih₂ =>
      exact ih₁.trans ih₂

lemma q8ResidueQuota_perm {xs ys : List Nat} (h : xs.Perm ys) :
    q8ResidueQuota xs = q8ResidueQuota ys := by
  have hp := q8ResidueEdgeColors_perm_of_perm h
  have hfun : (fun c : Nat =>
      decide ((q8ResidueEdgeColors xs).count c ≤ 4)) =
      (fun c : Nat => decide ((q8ResidueEdgeColors ys).count c ≤ 4)) := by
    funext c
    rw [hp.count_eq c]
  simp only [q8ResidueQuota]
  rw [hfun]

lemma q8ResidueOddOK_perm {xs ys : List Nat} (h : xs.Perm ys) :
    q8ResidueOddOK xs = q8ResidueOddOK ys := by
  simp only [q8ResidueOddOK]
  rw [(h.map (fun v => v % 2)).sum_eq]

#print axioms q8InfinityRawB_mod4
#print axioms q8InfinityParity_three_or_four
#print axioms q8InfinityResidueConditions_of_nodup
#print axioms q8ResidueQuota_perm
#print axioms q8ResidueOddOK_perm

end Erdos811
