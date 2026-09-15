import Q9FastBridge
import Q9EdgePairs
import Q9ParityObstructions
import Q9ParityCountBridge
import Q9FiniteBranchBridge
import Q9LRATSemanticBridge

/-! Finite symmetry bridge for the anchored q=9 search.

The search fixes vertex `0`.  Translation on the 72 finite vertices fixes
the point at infinity and shifts every colour by a constant modulo 36, so
every rainbow copy can be translated to one containing `0`.
-/

namespace Erdos811

open Erdos811Q9SeqCounter
open Erdos811Q9CNFSemantics

lemma q9Color_val (i j : Fin 73) :
    (q9Coloring.color i j).val = q9EdgeColorFast i.val j.val := by
  by_cases hi : i.val = 72 <;> by_cases hj : j.val = 72 <;>
    simp [q9Coloring, q9EdgeColorFast, hi, hj]

def q9Translate (t : Fin 72) (x : Fin 73) : Fin 73 :=
  if hx : x.val = 72 then
    ⟨72, by omega⟩
  else
    ⟨(x.val + t.val) % 72, by omega⟩

def q9ShiftColor (t : Fin 72) (c : Fin 36) : Fin 36 :=
  ⟨(c.val + t.val) % 36, by omega⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem q9Translate_injective_all :
    ∀ t : Fin 72, Function.Injective (q9Translate t) := by
  intro t x y hxy
  by_cases hx : x.val = 72
  · by_cases hy : y.val = 72
    · exact Fin.ext (by omega)
    · have hval := congrArg Fin.val hxy
      simp [q9Translate, hx, hy] at hval
      omega
  · by_cases hy : y.val = 72
    · have hval := congrArg Fin.val hxy
      simp [q9Translate, hx, hy] at hval
      omega
    · apply Fin.ext
      have hval := congrArg Fin.val hxy
      simp only [q9Translate, dif_neg hx, dif_neg hy] at hval
      omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma q9_mod_half_shift {a b t : Nat}
    (ha : a < 72) (hb : b < 72) (ht : t < 72) :
    (((a + t) % 72 + (b + t) % 72 + 1) / 2) % 36 =
      (((a + b + 1) / 2) % 36 + t) % 36 := by
  by_cases hA : a + t < 72
  · have hAm : (a + t) % 72 = a + t := Nat.mod_eq_of_lt hA
    by_cases hB : b + t < 72
    · have hBm : (b + t) % 72 = b + t := Nat.mod_eq_of_lt hB
      rw [hAm, hBm]
      omega
    · have hBge : b + t ≥ 72 := Nat.le_of_not_gt hB
      have hBsub : b + t - 72 < 72 := by omega
      have hBm : (b + t) % 72 = b + t - 72 := by
        rw [Nat.mod_eq_sub_mod hBge, Nat.mod_eq_of_lt hBsub]
      rw [hAm, hBm]
      omega
  · have hAge : a + t ≥ 72 := Nat.le_of_not_gt hA
    have hAsub : a + t - 72 < 72 := by omega
    have hAm : (a + t) % 72 = a + t - 72 := by
      rw [Nat.mod_eq_sub_mod hAge, Nat.mod_eq_of_lt hAsub]
    by_cases hB : b + t < 72
    · have hBm : (b + t) % 72 = b + t := Nat.mod_eq_of_lt hB
      rw [hAm, hBm]
      omega
    · have hBge : b + t ≥ 72 := Nat.le_of_not_gt hB
      have hBsub : b + t - 72 < 72 := by omega
      have hBm : (b + t) % 72 = b + t - 72 := by
        rw [Nat.mod_eq_sub_mod hBge, Nat.mod_eq_of_lt hBsub]
      rw [hAm, hBm]
      omega

theorem q9Translate_edgeColor_all :
    ∀ (t : Fin 72) (i j : Fin 73),
      i ≠ j →
      q9EdgeColorFast (q9Translate t i).val (q9Translate t j).val =
        (q9EdgeColorFast i.val j.val + t.val) % 36 := by
  intro t i j hij
  by_cases hi : i.val = 72
  · by_cases hj : j.val = 72
    · exfalso
      apply hij
      exact Fin.ext (by omega)
    · simp [q9Translate, q9EdgeColorFast, hi, hj]
  · by_cases hj : j.val = 72
    · have hitne : (i.val + t.val) % 72 ≠ 72 := by omega
      simp [q9Translate, q9EdgeColorFast, hi, hj, hitne]
    · have hitne : (i.val + t.val) % 72 ≠ 72 := by omega
      have hjtne : (j.val + t.val) % 72 ≠ 72 := by omega
      simp [q9Translate, q9EdgeColorFast, hi, hj, hitne, hjtne]
      simpa [Nat.add_mod] using
        (q9_mod_half_shift (a := i.val) (b := j.val) (t := t.val)
          (by omega) (by omega) (by omega))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem q9ShiftColor_injective_all :
    ∀ t : Fin 72, Function.Injective (q9ShiftColor t) := by
  intro t x y hxy
  apply Fin.ext
  have hval := congrArg Fin.val hxy
  simp only [q9ShiftColor] at hval
  omega

lemma q9Translate_color (t : Fin 72) (i j : Fin 73) (hij : i ≠ j) :
    q9Coloring.color (q9Translate t i) (q9Translate t j) =
      q9ShiftColor t (q9Coloring.color i j) := by
  apply Fin.ext
  simpa [q9Color_val, q9ShiftColor] using q9Translate_edgeColor_all t i j hij

def q9TranslateEmbedding (t : Fin 72) : Fin 73 ↪ Fin 73 :=
  { toFun := q9Translate t
    inj' := q9Translate_injective_all t }

lemma q9FiniteIndex (f : Fin 9 ↪ Fin 73) :
    (f (if (f 0).val = 72 then (1 : Fin 9) else 0)).val < 72 := by
  by_cases h : (f 0).val = 72
  · have hne : f (1 : Fin 9) ≠ f 0 := f.injective.ne (by decide)
    have h1 : (f (1 : Fin 9)).val ≠ 72 := by
      intro h1
      apply hne
      apply Fin.ext
      omega
    have h1lt : (f (1 : Fin 9)).val < 73 := (f (1 : Fin 9)).isLt
    simp only [if_pos h]
    omega
  · simp [h]
    have h0lt : (f (0 : Fin 9)).val < 73 := (f (0 : Fin 9)).isLt
    omega

def q9ShiftToZero (v : Fin 73) : Fin 72 :=
  ⟨(72 - v.val) % 72, by omega⟩

lemma q9Translate_shift_to_zero {v : Fin 73} (hv : v.val < 72) :
    q9Translate (q9ShiftToZero v) v = 0 := by
  have hne : v.val ≠ 72 := by omega
  simp only [q9Translate, dif_neg hne, q9ShiftToZero]
  apply Fin.ext
  by_cases hv0 : v.val = 0
  · simp [hv0]
  · have hvpos : 0 < v.val := Nat.pos_of_ne_zero hv0
    have hsub_lt : 72 - v.val < 72 := by omega
    have hmod : (72 - v.val) % 72 = 72 - v.val :=
      Nat.mod_eq_of_lt hsub_lt
    simp only [hmod]
    have hsum : v.val + (72 - v.val) = 72 := by omega
    rw [hsum]
    simp

lemma q9Translated_rainbow
    {f : Fin 9 ↪ Fin 73}
    (hf : ∀ ⦃a b c d : Fin 9⦄,
      (SimpleGraph.completeGraph (Fin 9)).Adj a b →
      (SimpleGraph.completeGraph (Fin 9)).Adj c d →
      ¬ SameUndirectedEdge a b c d →
      q9Coloring.color (f a) (f b) ≠ q9Coloring.color (f c) (f d))
    (t : Fin 72) :
    ∀ ⦃a b c d : Fin 9⦄,
      (SimpleGraph.completeGraph (Fin 9)).Adj a b →
      (SimpleGraph.completeGraph (Fin 9)).Adj c d →
      ¬ SameUndirectedEdge a b c d →
      q9Coloring.color ((f.trans (q9TranslateEmbedding t)) a)
          ((f.trans (q9TranslateEmbedding t)) b) ≠
        q9Coloring.color ((f.trans (q9TranslateEmbedding t)) c)
          ((f.trans (q9TranslateEmbedding t)) d) := by
  intro a b c d hab hcd hsame heq
  apply hf hab hcd hsame
  apply (q9ShiftColor_injective_all t)
  have hab_ne : a ≠ b := by simpa using hab
  have hcd_ne : c ≠ d := by simpa using hcd
  have hab' : f a ≠ f b := f.injective.ne hab_ne
  have hcd' : f c ≠ f d := f.injective.ne hcd_ne
  change q9Coloring.color (q9Translate t (f a)) (q9Translate t (f b)) =
      q9Coloring.color (q9Translate t (f c)) (q9Translate t (f d)) at heq
  rw [q9Translate_color t (f a) (f b) hab',
    q9Translate_color t (f c) (f d) hcd'] at heq
  exact heq

lemma q9_no_rainbow_with_zero_using
    (finite_branch_false :
      ∀ {xs : List Nat} {g : Fin 9 ↪ Fin 73},
        xs.length = 8 →
        xs.Sublist (List.range' 1 72) →
        (xs ++ [0]).Nodup →
        q9EdgeDistinct (xs ++ [0]) →
        g (0 : Fin 9) = 0 →
        (∀ i : Fin 9, (g i).val < 72) →
        (∀ ⦃a b c d : Fin 9⦄,
          (SimpleGraph.completeGraph (Fin 9)).Adj a b →
          (SimpleGraph.completeGraph (Fin 9)).Adj c d →
          ¬ SameUndirectedEdge (g a) (g b) (g c) (g d) →
          q9Coloring.color (g a) (g b) ≠ q9Coloring.color (g c) (g d)) →
        (∀ z, z ∈ xs ++ [0] → ∃ i : Fin 9, z = (g i).val) →
        (∀ i : Fin 9, (g i).val ∈ xs ++ [0]) →
        (∀ z, z ∈ xs ++ [0] → z < 73) →
        9 ≤ (xs ++ [0]).toFinset.card →
        False) :
    ¬ ∃ (f : Fin 9 ↪ Fin 73),
      0 ∈ Finset.univ.image f ∧
      (∀ ⦃a b c d : Fin 9⦄,
        (SimpleGraph.completeGraph (Fin 9)).Adj a b →
        (SimpleGraph.completeGraph (Fin 9)).Adj c d →
        ¬ SameUndirectedEdge a b c d →
        q9Coloring.color (f a) (f b) ≠ q9Coloring.color (f c) (f d)) := by
  rintro ⟨f, hfzero, hf⟩
  let s : Finset (Fin 73) := Finset.univ.image f
  have hs_card : s.card = 9 := by
    dsimp [s]
    apply (Finset.card_image_iff).2
    intro x hx y hy hxy
    exact f.injective hxy
  let gOrder : Fin 9 ↪o Fin 73 := s.orderEmbOfFin hs_card
  let g : Fin 9 ↪ Fin 73 := gOrder.toEmbedding
  have hg_mem (i : Fin 9) : g i ∈ s := by
    exact Finset.orderEmbOfFin_mem s hs_card i
  have hmem_image (i : Fin 9) : g i ∈ Finset.univ.image f := by
    simpa [s] using hg_mem i
  have hzero_mem : (0 : Fin 73) ∈ s := by
    simpa [s] using hfzero
  have hzero_range : (0 : Fin 73) ∈ Set.range gOrder := by
    rw [show gOrder = s.orderEmbOfFin hs_card from rfl,
      Finset.range_orderEmbOfFin s hs_card]
    exact hzero_mem
  obtain ⟨i, hi⟩ := hzero_range
  have hgzero : g 0 = 0 := by
    have hi0 : i = 0 := by
      by_contra hne
      have hpos : 0 < (i : Nat) := Nat.pos_of_ne_zero (by
        intro hz
        apply hne
        exact Fin.ext hz)
      have hposFin : (0 : Fin 9) < i := by
        exact hpos
      have hlt := gOrder.strictMono hposFin
      rw [hi] at hlt
      exact (not_lt_of_ge (Fin.zero_le _)) hlt
    subst i
    exact hi
  have hdiff {a b c d : Fin 9}
      (hab : a ≠ b) (hcd : c ≠ d)
      (hnot : ¬ SameUndirectedEdge a b c d) :
      q9Coloring.color (g a) (g b) ≠ q9Coloring.color (g c) (g d) := by
    have hp_spec (i : Fin 9) :
        ∃ j : Fin 9, f j = g i := by
      rcases Finset.mem_image.mp (hmem_image i) with ⟨j, _, hj⟩
      exact ⟨j, hj⟩
    choose p hp using hp_spec
    let pEmb : Fin 9 ↪ Fin 9 := {
      toFun := p
      inj' := by
        intro i j hij
        apply g.injective
        rw [← hp i, ← hp j, hij]
    }
    rw [← hp a, ← hp b, ← hp c, ← hp d]
    apply hf
    · intro hEq
      exact hab (pEmb.injective hEq)
    · intro hEq
      exact hcd (pEmb.injective hEq)
    · intro hsame
      apply hnot
      rcases hsame with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨pEmb.injective h1, pEmb.injective h2⟩
      · exact Or.inr ⟨pEmb.injective h1, pEmb.injective h2⟩
  let xs : List Nat := List.ofFn (fun i : Fin 8 => (g (Fin.succ i)).val)
  have hlen : xs.length = 8 := by simp [xs]
  have hstrict : StrictMono (fun i : Fin 8 => (g (Fin.succ i)).val) := by
    intro i j hij
    have hij' : Fin.succ i < Fin.succ j := by
      exact Nat.succ_lt_succ (show (i : Nat) < (j : Nat) from hij)
    simpa [g] using gOrder.strictMono hij'
  have hsorted : xs.SortedLT := (List.sortedLT_ofFn_iff).2 hstrict
  have hsubset : xs ⊆ List.range' 1 72 := by
    intro x hx
    change x ∈ List.ofFn (fun i : Fin 8 => (g (Fin.succ i)).val) at hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    have hpos : 0 < (g (Fin.succ i)).val := by
      have hlt := gOrder.strictMono (Fin.succ_pos i)
      have hlt' : g 0 < g (Fin.succ i) := by simpa [g] using hlt
      rw [hgzero] at hlt'
      exact hlt'
    have hlt : (g (Fin.succ i)).val < 73 := (g (Fin.succ i)).isLt
    simp only [List.mem_range'_1]
    omega
  have hsubperm : xs.Subperm (List.range' 1 72) := hsorted.nodup.subperm hsubset
  have hsub : xs.Sublist (List.range' 1 72) :=
    List.sublist_of_subperm_of_sortedLE hsubperm hsorted.sortedLE
      (List.sortedLT_range' 1 72 (by decide)).sortedLE
  have hzero_not : 0 ∉ xs := by
    intro hz
    change 0 ∈ List.ofFn (fun i : Fin 8 => (g (Fin.succ i)).val) at hz
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hz
    have hlt := gOrder.strictMono (Fin.succ_pos i)
    have hlt' : g 0 < g (Fin.succ i) := by simpa [g] using hlt
    rw [hgzero] at hlt'
    omega
  have hnodup : (xs ++ [0]).Nodup := by
    apply List.Nodup.append hsorted.nodup (by simp)
    intro a ha hb
    simp at hb
    subst a
    exact hzero_not ha
  have hindex : ∀ z, z ∈ xs ++ [0] → ∃ i : Fin 9, z = (g i).val := by
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · change z ∈ List.ofFn (fun i : Fin 8 => (g (Fin.succ i)).val) at hz
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
      exact ⟨Fin.succ i, rfl⟩
    · simp at hz
      subst z
      exact ⟨0, by simpa [hgzero]⟩
  have hdist : q9EdgeDistinct (xs ++ [0]) := by
    intro a b c d ha hb hc hd hab hcd hsame
    obtain ⟨i, rfl⟩ := hindex a ha
    obtain ⟨j, rfl⟩ := hindex b hb
    obtain ⟨k, rfl⟩ := hindex c hc
    obtain ⟨l, rfl⟩ := hindex d hd
    have hab' : i ≠ j := by
      intro hij
      apply hab
      simp [hij]
    have hcd' : k ≠ l := by
      intro hkl
      apply hcd
      simp [hkl]
    have hsame' : ¬ SameUndirectedEdge i j k l := by
      intro hsame'
      apply hsame
      rcases hsame' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨congrArg (fun t => (g t).val) h1,
          congrArg (fun t => (g t).val) h2⟩
      · exact Or.inr ⟨congrArg (fun t => (g t).val) h1,
          congrArg (fun t => (g t).val) h2⟩
    intro heq
    apply hdiff hab' hcd' hsame'
    apply Fin.ext
    simpa only [q9Color_val] using heq
  by_cases hinf : (g (8 : Fin 9)).val = 72
  · have hfin' : ∀ i : Fin 8, (g i.castSucc).val < 72 := by
      intro i
      have hi_lt : i.castSucc < (8 : Fin 9) := by
        simpa using (Fin.castSucc_lt_last i)
      have hlt := gOrder.strictMono hi_lt
      have hval : (g i.castSucc).val < (g (8 : Fin 9)).val := by
        simpa [g] using hlt
      rw [hinf] at hval
      exact hval
    have hdiff' {a b c d : Fin 9}
        (hab : (SimpleGraph.completeGraph (Fin 9)).Adj a b)
        (hcd : (SimpleGraph.completeGraph (Fin 9)).Adj c d)
        (hnot : ¬ SameUndirectedEdge (g a) (g b) (g c) (g d)) :
        q9Coloring.color (g a) (g b) ≠ q9Coloring.color (g c) (g d) := by
      have hab' : a ≠ b := by simpa using hab
      have hcd' : c ≠ d := by simpa using hcd
      apply hdiff hab' hcd'
      intro hsame
      apply hnot
      rcases hsame with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨congrArg g h1, congrArg g h2⟩
      · exact Or.inr ⟨congrArg g h1, congrArg g h2⟩
    refine q9_infty_branch_no_rainbow hgzero hinf hfin' ?_
    intro a b c d hab hcd hnot
    exact hdiff' hab hcd hnot
  · have himage : ∀ i : Fin 9, (g i).val ∈ xs ++ [0] := by
      intro i
      by_cases hi : i = 0
      · subst i
        simp [hgzero]
      · obtain ⟨j, rfl⟩ := i.eq_succ_of_ne_zero hi
        apply List.mem_append.mpr
        left
        change (g (Fin.succ j)).val ∈
          List.ofFn (fun k : Fin 8 => (g (Fin.succ k)).val)
        exact List.mem_ofFn.mpr ⟨j, rfl⟩
    have hbound : ∀ z, z ∈ xs ++ [0] → z < 73 := by
      intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · change z ∈ List.ofFn (fun i : Fin 8 => (g (Fin.succ i)).val) at hz
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
        exact (g (Fin.succ i)).isLt
      · simp at hz
        omega
    have hcard : 9 ≤ (xs ++ [0]).toFinset.card := by
      rw [List.toFinset_card_of_nodup hnodup]
      simp [hlen]
    have hcounts := Erdos811Q9FiniteBranchBridge.finite_branch_count_identities
      (xs := xs ++ [0]) (g := g) hgzero hindex himage hbound hcard
    have hfin : ∀ i : Fin 9, (g i).val < 72 := by
      intro i
      have hle : i ≤ (8 : Fin 9) := Fin.le_last i
      rcases lt_or_eq_of_le hle with hil | rfl
      · have hlt := gOrder.strictMono hil
        have hval : (g i).val < (g (8 : Fin 9)).val := by
          simpa [g] using hlt
        omega
      · have hlt := (g (8 : Fin 9)).isLt
        omega
    have hf' : ∀ ⦃a b c d : Fin 9⦄,
        (SimpleGraph.completeGraph (Fin 9)).Adj a b →
        (SimpleGraph.completeGraph (Fin 9)).Adj c d →
        ¬ SameUndirectedEdge (g a) (g b) (g c) (g d) →
        q9Coloring.color (g a) (g b) ≠ q9Coloring.color (g c) (g d) := by
      intro a b c d hab hcd hnot
      have hab' : a ≠ b := by simpa using hab
      have hcd' : c ≠ d := by simpa using hcd
      apply hdiff hab' hcd'
      intro hsame
      apply hnot
      rcases hsame with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨congrArg g h1, congrArg g h2⟩
      · exact Or.inr ⟨congrArg g h1, congrArg g h2⟩
    exact finite_branch_false hlen hsub hnodup hdist hgzero hfin hf'
      hindex himage hbound hcard

/- Native-search wrapper retained for the current fast build.  The theorem
   above is parameterized so the same symmetry argument can later be closed
   with the staged LRAT certificates without duplicating its construction. -/
lemma q9_no_rainbow_with_zero :
    ¬ ∃ (f : Fin 9 ↪ Fin 73),
      0 ∈ Finset.univ.image f ∧
      (∀ ⦃a b c d : Fin 9⦄,
        (SimpleGraph.completeGraph (Fin 9)).Adj a b →
        (SimpleGraph.completeGraph (Fin 9)).Adj c d →
        ¬ SameUndirectedEdge a b c d →
        q9Coloring.color (f a) (f b) ≠ q9Coloring.color (f c) (f d)) := by
  apply q9_no_rainbow_with_zero_using
  intro xs g hlen hsub hnodup hdist hgzero hfin hf hcoverage himage hbound hcard
  exact q9_no_sublist_edgeDistinct_zero ⟨xs, hlen, hsub, hnodup, hdist⟩

/- LRAT-ready wrapper.  It is intentionally parameterized by the two final
   empty-clause proofs, so it compiles before the large staged replay reaches
   stage 197/127 and becomes the replacement endpoint once those proofs exist. -/
lemma q9_no_rainbow_with_zero_lrat
    (hproof4 : Erdos811Q9NoInfR4CNF.q9_noinf_r4_ctx.proof [])
    (hproof5 : Erdos811Q9NoInfR5CNF.q9_noinf_r5_ctx.proof []) :
    ¬ ∃ (f : Fin 9 ↪ Fin 73),
      0 ∈ Finset.univ.image f ∧
      (∀ ⦃a b c d : Fin 9⦄,
        (SimpleGraph.completeGraph (Fin 9)).Adj a b →
        (SimpleGraph.completeGraph (Fin 9)).Adj c d →
        ¬ SameUndirectedEdge a b c d →
        q9Coloring.color (f a) (f b) ≠ q9Coloring.color (f c) (f d)) := by
  apply q9_no_rainbow_with_zero_using
  intro xs g hlen hsub hnodup hdist hgzero hfin hf hcoverage himage hbound hcard
  have hcounts := Erdos811Q9FiniteBranchBridge.finite_branch_count_identities
    (xs := xs ++ [0]) (g := g) hgzero hcoverage himage hbound hcard
  have hcand := Erdos811Q9FiniteBranchBridge.finite_branch_candidate_of_counts
    (xs := xs ++ [0]) (g := g) hgzero hfin hf hcoverage himage hbound hcard
  have hodd :
      prefixCount (q9OddSelectionBool (xs ++ [0])) 36 = 4 ∨
        prefixCount (q9OddSelectionBool (xs ++ [0])) 36 = 5 := by
    simpa using hcand
  have h0 : 0 ∈ xs ++ [0] := by simp
  have h72xs : 72 ∉ xs := by
    intro hz
    obtain ⟨i, hi⟩ := hcoverage 72 (List.mem_append.mpr (Or.inl hz))
    have hi_lt := hfin i
    omega
  have h72 : 72 ∉ xs ++ [0] := by
    intro hz
    rcases List.mem_append.mp hz with hz | hz
    · exact h72xs hz
    · simp at hz
  exact Erdos811Q9LRATSemanticBridge.false_of_lrat_r4_or_r5
    (r := prefixCount (q9OddSelectionBool (xs ++ [0])) 36)
    hproof4 hproof5 hdist hcounts.2 rfl hodd h0 h72

theorem q9_no_rainbow :
    ¬ HasRainbowCopy (SimpleGraph.completeGraph (Fin 9)) q9Coloring := by
  classical
  rintro ⟨f, hf⟩
  let i : Fin 9 := if (f 0).val = 72 then 1 else 0
  have hi : (f i).val < 72 := by
    simpa [i] using q9FiniteIndex f
  let t : Fin 72 := q9ShiftToZero (f i)
  let g : Fin 9 ↪ Fin 73 := f.trans (q9TranslateEmbedding t)
  have hzero : (0 : Fin 73) ∈ Finset.univ.image g := by
    refine Finset.mem_image.mpr ⟨i, Finset.mem_univ _, ?_⟩
    change q9Translate t (f i) = 0
    exact q9Translate_shift_to_zero hi
  apply q9_no_rainbow_with_zero
  refine ⟨g, hzero, ?_⟩
  exact q9Translated_rainbow hf t

/- The same translation argument with the LRAT-ready endpoint.  Once the
   staged wrappers expose the two empty-clause proofs, this theorem is the
   strict-kernel q=9 replacement for the native-search theorem above. -/
theorem q9_no_rainbow_lrat
    (hproof4 : Erdos811Q9NoInfR4CNF.q9_noinf_r4_ctx.proof [])
    (hproof5 : Erdos811Q9NoInfR5CNF.q9_noinf_r5_ctx.proof []) :
    ¬ HasRainbowCopy (SimpleGraph.completeGraph (Fin 9)) q9Coloring := by
  classical
  rintro ⟨f, hf⟩
  let i : Fin 9 := if (f 0).val = 72 then 1 else 0
  have hi : (f i).val < 72 := by
    simpa [i] using q9FiniteIndex f
  let t : Fin 72 := q9ShiftToZero (f i)
  let g : Fin 9 ↪ Fin 73 := f.trans (q9TranslateEmbedding t)
  have hzero : (0 : Fin 73) ∈ Finset.univ.image g := by
    refine Finset.mem_image.mpr ⟨i, Finset.mem_univ _, ?_⟩
    change q9Translate t (f i) = 0
    exact q9Translate_shift_to_zero hi
  apply q9_no_rainbow_with_zero_lrat hproof4 hproof5
  refine ⟨g, hzero, ?_⟩
  exact q9Translated_rainbow hf t

#print axioms q9_no_rainbow

end Erdos811
