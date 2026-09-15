import Q8PaperEmbedding
import Mathlib.Data.Fin.VecNotation

namespace Erdos811

/-! Arithmetic for the infinity branch.  We keep the seven-finite-vertex
decomposition separate from the graph reindexing and support-normalization
bridges. -/

lemma q8PaperColorNat_mod4 (u v : Nat) :
    q8PaperColorNat u v % 4 =
      if u = 56 then v % 4
      else if v = 56 then u % 4
      else (((u + 1) / 2 + (v + 1) / 2 -
        (u % 2) * (v % 2)) % 4) := by
  by_cases hu : u = 56 <;> by_cases hv : v = 56
  · simp [q8PaperColorNat, hu, hv]
  · simp [q8PaperColorNat, hu, hv]
  · simp [q8PaperColorNat, hu, hv]
  · have hpu : u % 2 = 0 ∨ u % 2 = 1 := by omega
    have hpv : v % 2 = 0 ∨ v % 2 = 1 := by omega
    simp [q8PaperColorNat, hu, hv]
    rcases hpu with hpu | hpu <;> rcases hpv with hpv | hpv <;>
      simp [hpu, hpv] <;> omega

def q8InfinityRawB (x : Fin 7 → Nat) (ij : Fin 8 × Fin 8) : Nat :=
  if ij.1 = 7 then q8WithInfinity x ij.2
  else if ij.2 = 7 then q8WithInfinity x ij.1
  else q8PairB (q8WithInfinity x) ij

lemma q8WithInfinity_castSucc (x : Fin 7 → Nat) (i : Fin 7) :
    q8WithInfinity x i.castSucc = x i := by
  exact Fin.lastCases_castSucc i

lemma q8WithInfinity_last (x : Fin 7 → Nat) :
    q8WithInfinity x (Fin.last 7) = 56 := by
  exact Fin.lastCases_last

lemma q8InfinityRawB_cast_cast (x : Fin 7 → Nat) (i j : Fin 7) :
    q8InfinityRawB x (i.castSucc, j.castSucc) =
      (x i + 1) / 2 + (x j + 1) / 2 - (x i % 2) * (x j % 2) := by
  have hi : i.castSucc ≠ (7 : Fin 8) := Fin.castSucc_ne_last i
  have hj : j.castSucc ≠ (7 : Fin 8) := Fin.castSucc_ne_last j
  simp [q8InfinityRawB, q8WithInfinity_castSucc, q8WithInfinity_last, hi, hj,
    q8PairB]

lemma q8InfinityRawB_cast_last (x : Fin 7 → Nat) (i : Fin 7) :
    q8InfinityRawB x (i.castSucc, 7) = x i := by
  have hi : i.castSucc ≠ (7 : Fin 8) := Fin.castSucc_ne_last i
  simp [q8InfinityRawB, q8WithInfinity_castSucc, q8WithInfinity_last, hi]

lemma q8InfinityRawB_last_cast (x : Fin 7 → Nat) (i : Fin 7) :
    q8InfinityRawB x (7, i.castSucc) = x i := by
  have hi : i.castSucc ≠ (7 : Fin 8) := Fin.castSucc_ne_last i
  simp [q8InfinityRawB, q8WithInfinity_castSucc, q8WithInfinity_last, hi]

lemma q8FiniteEdge_mod4 (u v : Nat) (hu : u < 56) (hv : v < 56) :
    q8PaperColorNat u v ≡
      ((u + 1) / 2 + (v + 1) / 2 - (u % 2) * (v % 2)) [MOD 4] := by
  rw [q8FiniteEdgeFormula u v hu hv]
  simp only [Nat.ModEq]
  omega

lemma q8InfinityEdge_mod4_last (v : Nat) :
    q8PaperColorNat 56 v ≡ v [MOD 4] := by
  simp only [Nat.ModEq, q8PaperColorNat]
  simp only [if_true]
  rw [Nat.mod_mod_of_dvd v (by norm_num : 4 ∣ 28)]

lemma q8InfinityEdge_mod4 (x : Fin 7 → Nat) (hfin : ∀ i, x i < 56)
    (ij : Fin 8 × Fin 8) (hij : ij ∈ q8Pairs) :
    q8PaperColorNat (q8WithInfinity x ij.1) (q8WithInfinity x ij.2) ≡
      q8InfinityRawB x ij [MOD 4] := by
  rcases ij with ⟨i, j⟩
  cases i using Fin.lastCases with
  | last =>
      cases j using Fin.lastCases with
      | last => simp [q8Pairs] at hij
      | cast j =>
          change q8PaperColorNat 56 (q8WithInfinity x j.castSucc) ≡
            q8InfinityRawB x (Fin.last 7, j.castSucc) [MOD 4]
          rw [q8WithInfinity_castSucc]
          have hr : q8InfinityRawB x (Fin.last 7, j.castSucc) = x j := by
            simpa using q8InfinityRawB_last_cast x j
          rw [hr]
          exact q8InfinityEdge_mod4_last (x j)
  | cast i =>
      cases j using Fin.lastCases with
      | last =>
          change q8PaperColorNat (q8WithInfinity x i.castSucc) 56 ≡
            q8InfinityRawB x (i.castSucc, Fin.last 7) [MOD 4]
          rw [q8WithInfinity_castSucc]
          have hr : q8InfinityRawB x (i.castSucc, Fin.last 7) = x i := by
            simpa using q8InfinityRawB_cast_last x i
          rw [hr]
          change q8PaperColorNat (x i) 56 ≡ x i [MOD 4]
          rw [q8PaperColorNat_comm (x i) 56]
          exact q8InfinityEdge_mod4_last (x i)
      | cast j =>
          change q8PaperColorNat (q8WithInfinity x i.castSucc)
              (q8WithInfinity x j.castSucc) ≡
            q8InfinityRawB x (i.castSucc, j.castSucc) [MOD 4]
          rw [q8WithInfinity_castSucc, q8WithInfinity_castSucc]
          rw [q8InfinityRawB_cast_cast]
          have hi := hfin i
          have hj := hfin j
          exact q8FiniteEdge_mod4 _ _ hi hj

lemma q8Perm_sum {l₁ l₂ : List Nat} (h : l₁.Perm l₂) :
    l₁.sum = l₂.sum := by
  exact h.sum_eq

lemma q8Perm_move_right {α : Type*} (l r : List α) (a : α) :
    (l ++ [a] ++ r).Perm (l ++ r ++ [a]) := by
  simpa [List.append_assoc] using
    (List.Perm.append_left l (q8Perm_cons_append a r))

lemma q8Interleave7Perm {α : Type*}
    (e0 e1 e2 e3 e4 e5 e6 : List α)
    (a0 a1 a2 a3 a4 a5 a6 : α) :
    (e0 ++ [a0] ++ e1 ++ [a1] ++ e2 ++ [a2] ++ e3 ++ [a3] ++
      e4 ++ [a4] ++ e5 ++ [a5] ++ e6 ++ [a6]).Perm
      ((e0 ++ e1 ++ e2 ++ e3 ++ e4 ++ e5 ++ e6) ++
        [a0, a1, a2, a3, a4, a5, a6]) := by
  have h0 := q8Perm_move_right e0
    (e1 ++ [a1] ++ e2 ++ [a2] ++ e3 ++ [a3] ++ e4 ++ [a4] ++
      e5 ++ [a5] ++ e6 ++ [a6]) a0
  have h1 := q8Perm_move_right (e0 ++ e1)
    (e2 ++ [a2] ++ e3 ++ [a3] ++ e4 ++ [a4] ++ e5 ++ [a5] ++
      e6 ++ [a6] ++ [a0]) a1
  have h2 := q8Perm_move_right (e0 ++ e1 ++ e2)
    (e3 ++ [a3] ++ e4 ++ [a4] ++ e5 ++ [a5] ++ e6 ++ [a6] ++
      [a0, a1]) a2
  have h3 := q8Perm_move_right (e0 ++ e1 ++ e2 ++ e3)
    (e4 ++ [a4] ++ e5 ++ [a5] ++ e6 ++ [a6] ++ [a0, a1, a2]) a3
  have h4 := q8Perm_move_right (e0 ++ e1 ++ e2 ++ e3 ++ e4)
    (e5 ++ [a5] ++ e6 ++ [a6] ++ [a0, a1, a2, a3]) a4
  have h5 := q8Perm_move_right (e0 ++ e1 ++ e2 ++ e3 ++ e4 ++ e5)
    (e6 ++ [a6] ++ [a0, a1, a2, a3, a4]) a5
  have h6 := q8Perm_move_right (e0 ++ e1 ++ e2 ++ e3 ++ e4 ++ e5 ++ e6)
    [a0, a1, a2, a3, a4, a5] a6
  have h0' :
      (e0 ++ [a0] ++ e1 ++ [a1] ++ e2 ++ [a2] ++ e3 ++ [a3] ++
        e4 ++ [a4] ++ e5 ++ [a5] ++ e6 ++ [a6]).Perm
      (e0 ++ e1 ++ [a1] ++ e2 ++ [a2] ++ e3 ++ [a3] ++ e4 ++ [a4] ++
        e5 ++ [a5] ++ e6 ++ [a6] ++ [a0]) := by
    simpa [List.append_assoc] using h0
  have h1' :
      (e0 ++ e1 ++ [a1] ++ e2 ++ [a2] ++ e3 ++ [a3] ++ e4 ++ [a4] ++
        e5 ++ [a5] ++ e6 ++ [a6] ++ [a0]).Perm
      (e0 ++ e1 ++ e2 ++ [a2] ++ e3 ++ [a3] ++ e4 ++ [a4] ++ e5 ++ [a5] ++
        e6 ++ [a6] ++ [a0, a1]) := by
    simpa [List.append_assoc] using h1
  have h2' :
      (e0 ++ e1 ++ e2 ++ [a2] ++ e3 ++ [a3] ++ e4 ++ [a4] ++ e5 ++ [a5] ++
        e6 ++ [a6] ++ [a0, a1]).Perm
      (e0 ++ e1 ++ e2 ++ e3 ++ [a3] ++ e4 ++ [a4] ++ e5 ++ [a5] ++
        e6 ++ [a6] ++ [a0, a1, a2]) := by
    simpa [List.append_assoc] using h2
  have h3' :
      (e0 ++ e1 ++ e2 ++ e3 ++ [a3] ++ e4 ++ [a4] ++ e5 ++ [a5] ++
        e6 ++ [a6] ++ [a0, a1, a2]).Perm
      (e0 ++ e1 ++ e2 ++ e3 ++ e4 ++ [a4] ++ e5 ++ [a5] ++
        e6 ++ [a6] ++ [a0, a1, a2, a3]) := by
    simpa [List.append_assoc] using h3
  have h4' :
      (e0 ++ e1 ++ e2 ++ e3 ++ e4 ++ [a4] ++ e5 ++ [a5] ++
        e6 ++ [a6] ++ [a0, a1, a2, a3]).Perm
      (e0 ++ e1 ++ e2 ++ e3 ++ e4 ++ e5 ++ [a5] ++ e6 ++ [a6] ++
        [a0, a1, a2, a3, a4]) := by
    simpa [List.append_assoc] using h4
  have h5' :
      (e0 ++ e1 ++ e2 ++ e3 ++ e4 ++ e5 ++ [a5] ++ e6 ++ [a6] ++
        [a0, a1, a2, a3, a4]).Perm
      (e0 ++ e1 ++ e2 ++ e3 ++ e4 ++ e5 ++ e6 ++ [a6] ++
        [a0, a1, a2, a3, a4, a5]) := by
    simpa [List.append_assoc] using h5
  have h6' :
      (e0 ++ e1 ++ e2 ++ e3 ++ e4 ++ e5 ++ e6 ++ [a6] ++
        [a0, a1, a2, a3, a4, a5]).Perm
      ((e0 ++ e1 ++ e2 ++ e3 ++ e4 ++ e5 ++ e6) ++
        [a0, a1, a2, a3, a4, a5, a6]) := by
    simpa [List.append_assoc] using h6
  exact h0'.trans (h1'.trans (h2'.trans (h3'.trans (h4'.trans (h5'.trans h6')))))

def q8Pairs7 : List (Fin 7 × Fin 7) :=
  [ (0,1), (0,2), (0,3), (0,4), (0,5), (0,6),
    (1,2), (1,3), (1,4), (1,5), (1,6),
    (2,3), (2,4), (2,5), (2,6),
    (3,4), (3,5), (3,6),
    (4,5), (4,6),
    (5,6) ]

def q8B7 (x : Fin 7 → Nat) (ij : Fin 7 × Fin 7) : Nat :=
  (x ij.1 + 1) / 2 + (x ij.2 + 1) / 2 -
    (x ij.1 % 2) * (x ij.2 % 2)

lemma q8B7_add_product (x : Fin 7 → Nat) (ij : Fin 7 × Fin 7) :
    q8B7 x ij + (x ij.1 % 2) * (x ij.2 % 2) =
      (x ij.1 + 1) / 2 + (x ij.2 + 1) / 2 := by
  dsimp [q8B7]
  have hi : x ij.1 % 2 = 0 ∨ x ij.1 % 2 = 1 := by omega
  have hj : x ij.2 % 2 = 0 ∨ x ij.2 % 2 = 1 := by omega
  rcases hi with hi | hi <;> rcases hj with hj | hj <;>
    simp [hi, hj] <;> omega

lemma q8B7_sum_add_product (x : Fin 7 → Nat) :
    (q8Pairs7.map (fun ij => q8B7 x ij)).sum +
      (q8Pairs7.map (fun ij => (x ij.1 % 2) * (x ij.2 % 2))).sum =
      6 * ((x 0 + 1) / 2 + (x 1 + 1) / 2 + (x 2 + 1) / 2 +
        (x 3 + 1) / 2 + (x 4 + 1) / 2 + (x 5 + 1) / 2 +
        (x 6 + 1) / 2) := by
  calc
    _ = (q8Pairs7.map (fun ij =>
        q8B7 x ij + (x ij.1 % 2) * (x ij.2 % 2))).sum := by
      symm
      exact List.sum_map_add
    _ = (q8Pairs7.map (fun ij =>
        (x ij.1 + 1) / 2 + (x ij.2 + 1) / 2)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro ij hij
      exact q8B7_add_product x ij
    _ = _ := by
      simp only [q8Pairs7, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega

lemma q8ParityProduct_sum_choose (x : Fin 7 → Nat) :
    (q8Pairs7.map (fun ij => (x ij.1 % 2) * (x ij.2 % 2))).sum =
      Nat.choose
        (x 0 % 2 + x 1 % 2 + x 2 % 2 + x 3 % 2 +
          x 4 % 2 + x 5 % 2 + x 6 % 2) 2 := by
  have h0 : x 0 % 2 = 0 ∨ x 0 % 2 = 1 := by omega
  have h1 : x 1 % 2 = 0 ∨ x 1 % 2 = 1 := by omega
  have h2 : x 2 % 2 = 0 ∨ x 2 % 2 = 1 := by omega
  have h3 : x 3 % 2 = 0 ∨ x 3 % 2 = 1 := by omega
  have h4 : x 4 % 2 = 0 ∨ x 4 % 2 = 1 := by omega
  have h5 : x 5 % 2 = 0 ∨ x 5 % 2 = 1 := by omega
  have h6 : x 6 % 2 = 0 ∨ x 6 % 2 = 1 := by omega
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
    rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
    rcases h4 with h4 | h4 <;> rcases h5 with h5 | h5 <;>
    rcases h6 with h6 | h6 <;>
      simp only [q8Pairs7, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] <;>
      simp_all [Nat.choose] <;> omega

lemma q8CeilHalf_add_mod_two (n : Nat) :
    n + n % 2 = 2 * ((n + 1) / 2) := by
  have h : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases h with h | h <;> omega

lemma q8CeilHalf_relation (x : Fin 7 → Nat) :
    x 0 + x 1 + x 2 + x 3 + x 4 + x 5 + x 6 +
        (x 0 % 2 + x 1 % 2 + x 2 % 2 + x 3 % 2 +
          x 4 % 2 + x 5 % 2 + x 6 % 2) =
      2 * ((x 0 + 1) / 2 + (x 1 + 1) / 2 + (x 2 + 1) / 2 +
        (x 3 + 1) / 2 + (x 4 + 1) / 2 + (x 5 + 1) / 2 +
        (x 6 + 1) / 2) := by
  have h0 := q8CeilHalf_add_mod_two (x 0)
  have h1 := q8CeilHalf_add_mod_two (x 1)
  have h2 := q8CeilHalf_add_mod_two (x 2)
  have h3 := q8CeilHalf_add_mod_two (x 3)
  have h4 := q8CeilHalf_add_mod_two (x 4)
  have h5 := q8CeilHalf_add_mod_two (x 5)
  have h6 := q8CeilHalf_add_mod_two (x 6)
  omega

lemma q8InfinityRawB_interleaved (x : Fin 7 → Nat) :
    q8Pairs.map (q8InfinityRawB x) =
      [q8B7 x (0,1), q8B7 x (0,2), q8B7 x (0,3),
       q8B7 x (0,4), q8B7 x (0,5), q8B7 x (0,6), x 0,
       q8B7 x (1,2), q8B7 x (1,3), q8B7 x (1,4),
       q8B7 x (1,5), q8B7 x (1,6), x 1,
       q8B7 x (2,3), q8B7 x (2,4), q8B7 x (2,5),
       q8B7 x (2,6), x 2,
       q8B7 x (3,4), q8B7 x (3,5), q8B7 x (3,6), x 3,
       q8B7 x (4,5), q8B7 x (4,6), x 4,
       q8B7 x (5,6), x 5, x 6] := by
  have h0 : q8WithInfinity x (0 : Fin 8) = x 0 := by
    change q8WithInfinity x (Fin.castSucc (0 : Fin 7)) = x 0
    exact q8WithInfinity_castSucc x 0
  have h1 : q8WithInfinity x (1 : Fin 8) = x 1 := by
    change q8WithInfinity x (Fin.castSucc (1 : Fin 7)) = x 1
    exact q8WithInfinity_castSucc x 1
  have h2 : q8WithInfinity x (2 : Fin 8) = x 2 := by
    change q8WithInfinity x (Fin.castSucc (2 : Fin 7)) = x 2
    exact q8WithInfinity_castSucc x 2
  have h3 : q8WithInfinity x (3 : Fin 8) = x 3 := by
    change q8WithInfinity x (Fin.castSucc (3 : Fin 7)) = x 3
    exact q8WithInfinity_castSucc x 3
  have h4 : q8WithInfinity x (4 : Fin 8) = x 4 := by
    change q8WithInfinity x (Fin.castSucc (4 : Fin 7)) = x 4
    exact q8WithInfinity_castSucc x 4
  have h5 : q8WithInfinity x (5 : Fin 8) = x 5 := by
    change q8WithInfinity x (Fin.castSucc (5 : Fin 7)) = x 5
    exact q8WithInfinity_castSucc x 5
  have h6 : q8WithInfinity x (6 : Fin 8) = x 6 := by
    change q8WithInfinity x (Fin.castSucc (6 : Fin 7)) = x 6
    exact q8WithInfinity_castSucc x 6
  simp only [q8Pairs, List.map_cons, List.map_nil, List.cons.injEq]
  repeat' constructor
lemma q8InfinityRawB_sum (x : Fin 7 → Nat) :
    (q8Pairs.map (q8InfinityRawB x)).sum =
      (q8Pairs7.map (q8B7 x)).sum +
        (x 0 + x 1 + x 2 + x 3 + x 4 + x 5 + x 6) := by
  rw [q8InfinityRawB_interleaved]
  simp only [q8Pairs7, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

lemma q8InfinityColorSum_mod4 (x : Fin 7 → Nat)
    (hfin : ∀ i, x i < 56) :
    ((q8FinitePairColors (q8WithInfinity x)).map (fun c => c.val)).sum ≡
      (q8Pairs.map (q8InfinityRawB x)).sum [MOD 4] := by
  have hsum := Nat.ModEq.sum (s := q8Pairs.toFinset)
    (f := fun ij => q8PaperColorNat (q8WithInfinity x ij.1)
      (q8WithInfinity x ij.2))
    (g := q8InfinityRawB x) (by
      intro ij hij
      exact q8InfinityEdge_mod4 x hfin ij hij)
  have hmap :
      (q8FinitePairColors (q8WithInfinity x)).map (fun c => c.val) =
        q8Pairs.map (fun ij => q8PaperColorNat (q8WithInfinity x ij.1)
          (q8WithInfinity x ij.2)) := by
    rfl
  rw [hmap]
  rw [← List.sum_toFinset
    (f := fun ij => q8PaperColorNat (q8WithInfinity x ij.1)
      (q8WithInfinity x ij.2)) q8Pairs_nodup]
  rw [← List.sum_toFinset (f := q8InfinityRawB x) q8Pairs_nodup]
  simpa [q8FinitePairColors] using hsum

/-
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
  have hEq : S + P =
      4 * X + 3 * r := by
    omega
  have hPC' : P = Nat.choose
      (x 0 % 2 + x 1 % 2 + x 2 % 2 + x 3 % 2 +
        x 4 % 2 + x 5 % 2 + x 6 % 2) 2 := by
    simpa [r] using hPC
  have hmod : S % 4 = (4 - (r + P) % 4) % 4 := by
    omega
  calc
    S % 4 = (4 - (r + P) % 4) % 4 := hmod
    _ = _ := by simp [r, hPC']

-/


/-
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
    norm_num
  have hmod := q8InfinityColorSum_mod4 x hfin
  have hraw := q8InfinityRawB_mod4 x
  have htarget :
      (4 - ((x 0 % 2 + x 1 % 2 + x 2 % 2 + x 3 % 2 +
        x 4 % 2 + x 5 % 2 + x 6 % 2) +
        Nat.choose (x 0 % 2 + x 1 % 2 + x 2 % 2 + x 3 % 2 +
          x 4 % 2 + x 5 % 2 + x 6 % 2) 2) % 4) % 4 = 2 := by
    rw [← hraw]
    exact hmod.symm ▸ hcol
  apply q8OddResidue_candidates _ (by omega)
  exact htarget

-/

end Erdos811
