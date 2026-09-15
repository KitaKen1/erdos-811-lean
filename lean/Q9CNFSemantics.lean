import Q9SeqCounter
import Q9FastProof

/-! Small semantic building blocks for the q=9 DIMACS bridge.

The generated collision clauses are lists of negative literals.  These
lemmas isolate their propositional meaning from the particular CNF parser so
the later clause classifier only has to establish a missing selected vertex.
-/

namespace Erdos811Q9CNFSemantics

open Mathlib.Tactic.Sat
open Erdos811

def selectionValuation (xs : List Nat) : Sat.Valuation :=
  fun i => i ∈ xs

def selectionBool (xs : List Nat) (i : Nat) : Bool :=
  xs.elem i

lemma selectionBool_true_iff (xs : List Nat) (i : Nat) :
    selectionBool xs i = true ↔ i ∈ xs := by
  simp [selectionBool]

lemma selectionValuation_iff (xs : List Nat) (i : Nat) :
    selectionValuation xs i ↔ selectionBool xs i = true := by
  simp [selectionValuation, selectionBool]

lemma selection_input_pos (xs : List Nat) (i : Nat) :
    ¬ (selectionValuation xs).neg (.pos i) ↔
      selectionBool xs i = true := by
  simp [selectionValuation, selectionBool, Sat.Valuation.neg]

lemma selection_input_neg (xs : List Nat) (i : Nat) :
    ¬ (selectionValuation xs).neg (.neg i) ↔
      selectionBool xs i = false := by
  simp [selectionValuation, selectionBool, Sat.Valuation.neg]

def q9SelectionInput (i : Nat) : Sat.Literal :=
  .pos i

def q9BaseInput (i : Nat) : Sat.Literal :=
  .neg i

def q9OddInputPos (j : Nat) : Sat.Literal :=
  -- PySAT receives zero-based vertex numbers `2,4,...,72`; DIMACS
  -- translates those one-based IDs to Lean variables `1,3,...,71`.
  .pos (2 * j + 1)

def q9OddInputNeg (j : Nat) : Sat.Literal :=
  .neg (2 * j + 1)

lemma q9OddInputPos_selection (xs : List Nat) (j : Nat) :
    ¬ (selectionValuation xs).neg (q9OddInputPos j) ↔
      selectionBool xs (2 * j + 1) = true := by
  simpa [q9OddInputPos] using selection_input_pos xs (2 * j + 1)

lemma q9OddInputNeg_selection (xs : List Nat) (j : Nat) :
    ¬ (selectionValuation xs).neg (q9OddInputNeg j) ↔
      selectionBool xs (2 * j + 1) = false := by
  simpa [q9OddInputNeg] using selection_input_neg xs (2 * j + 1)

def q9OddSelectionBool (xs : List Nat) (j : Nat) : Bool :=
  selectionBool xs (2 * j + 1)

def q9OddComplementBool (xs : List Nat) (j : Nat) : Bool :=
  !(q9OddSelectionBool xs j)

lemma q9OddComplementBool_true_iff (xs : List Nat) (j : Nat) :
    q9OddComplementBool xs j = true ↔
      q9OddSelectionBool xs j = false := by
  simp [q9OddComplementBool]

def negativeClause (xs : List Nat) : Sat.Clause :=
  xs.map Sat.Literal.neg

lemma satisfies_of_true_literal {v : Sat.Valuation} {l : Sat.Literal}
    (h : ¬ v.neg l) : v.satisfies [l] := by
  intro hl
  exact (h hl).elim

lemma satisfies_of_true_literal_mem {v : Sat.Valuation} {l : Sat.Literal}
    {ls : Sat.Clause} (h : ¬ v.neg l) : v.satisfies (l :: ls) := by
  intro hl
  exact (h hl).elim

lemma selection_anchor_pos {xs : List Nat} (h0 : 0 ∈ xs) :
    (selectionValuation xs).satisfies [Sat.Literal.pos 0] := by
  apply satisfies_of_true_literal
  simp [selectionValuation, Sat.Valuation.neg, h0]

lemma selection_anchor_neg {xs : List Nat} (h72 : 72 ∉ xs) :
    (selectionValuation xs).satisfies [Sat.Literal.neg 72] := by
  apply satisfies_of_true_literal
  simp [selectionValuation, Sat.Valuation.neg, h72]

lemma satisfies_negativeClause_of_missing
    {v : Sat.Valuation} {lits : List Nat}
    (hmiss : ∃ i ∈ lits, ¬ v i) :
    v.satisfies (negativeClause lits) := by
  induction lits with
  | nil =>
      rcases hmiss with ⟨i, hi, _⟩
      simp at hi
  | cons a rest ih =>
      simp only [negativeClause, List.map_cons]
      intro ha
      by_cases ha' : v a
      · apply ih
        rcases hmiss with ⟨i, hi, hnot⟩
        rcases List.mem_cons.mp hi with rfl | hi
        · exact False.elim (hnot ha')
        · exact ⟨i, hi, hnot⟩
      · exact False.elim (ha' ha)

lemma satisfies_negativeClause_of_not_forall
    {v : Sat.Valuation} {lits : List Nat}
    (hmiss : ¬ ∀ i ∈ lits, v i) :
    v.satisfies (negativeClause lits) := by
  refine satisfies_negativeClause_of_missing (v := v) (lits := lits) ?_
  by_contra h
  apply hmiss
  intro i hi
  exact Classical.byContradiction (fun hnot => h ⟨i, hi, hnot⟩)

lemma selection_negativeClause_of_missing
    {xs lits : List Nat} (hmiss : ∃ i ∈ lits, i ∉ xs) :
    (selectionValuation xs).satisfies (negativeClause lits) := by
  refine satisfies_negativeClause_of_missing
    (v := selectionValuation xs) (lits := lits) ?_
  simpa [selectionValuation] using hmiss

lemma selection_negativeClause_of_not_all_mem
    {xs lits : List Nat} (hnot : ¬ ∀ i ∈ lits, i ∈ xs) :
    (selectionValuation xs).satisfies (negativeClause lits) := by
  apply selection_negativeClause_of_missing
  by_contra hmiss
  apply hnot
  intro i hi
  exact Classical.byContradiction (fun hnoti => hmiss ⟨i, hi, hnoti⟩)

lemma selection_collision_clause
    {xs : List Nat} {a b c d : Nat}
    (hdist : q9EdgeDistinct xs)
    (hab : a ≠ b) (hcd : c ≠ d)
    (hsame : ¬ SameUndirectedEdge a b c d)
    (hcolor : q9EdgeColorFast a b = q9EdgeColorFast c d) :
    (selectionValuation xs).satisfies
      (negativeClause [a, b, c, d]) := by
  apply selection_negativeClause_of_missing
  by_contra hmiss
  have ha : a ∈ xs := by
    by_contra ha
    apply hmiss
    exact ⟨a, by simp, ha⟩
  have hb : b ∈ xs := by
    by_contra hb
    apply hmiss
    exact ⟨b, by simp, hb⟩
  have hc : c ∈ xs := by
    by_contra hc
    apply hmiss
    exact ⟨c, by simp, hc⟩
  have hd : d ∈ xs := by
    by_contra hd
    apply hmiss
    exact ⟨d, by simp, hd⟩
  exact (hdist ha hb hc hd hab hcd hsame) hcolor

/- The first collision clause in the anchored q=9 DIMACS is
   `-1 -72 -73`: it comes from the equal-coloured edges (0,71) and
   (0,72), whose endpoint set has only three elements. -/
lemma q9_first_collision_clause {xs : List Nat}
    (hdist : q9EdgeDistinct xs) :
    (selectionValuation xs).satisfies
      (negativeClause [0, 71, 72]) := by
  apply selection_negativeClause_of_not_all_mem
  intro hall
  have h0 : 0 ∈ xs := hall 0 (by simp)
  have h71 : 71 ∈ xs := hall 71 (by simp)
  have h72 : 72 ∈ xs := hall 72 (by simp)
  have hne₀ : 0 ≠ 71 := by decide
  have hne₁ : 0 ≠ 72 := by decide
  have hsame : ¬ SameUndirectedEdge 0 71 0 72 := by
    simp [SameUndirectedEdge]
  have hcolor : q9EdgeColorFast 0 71 = q9EdgeColorFast 0 72 := by decide
  exact (hdist h0 h71 h0 h72 hne₀ hne₁ hsame) hcolor

/- The base CNF encodes `at least 9` selected vertices as `at most 64` of
   their negated input literals.  This wrapper instantiates the generic
   sequential-counter theorem with the exact q=9 parameters. -/
lemma q9_base_atleast9_counter
    {v : Sat.Valuation} {xs : List Nat}
    (aux : Nat → Nat → Sat.Literal)
    (hsel : ∀ i, ¬ v.neg (q9BaseInput i) ↔
      selectionBool xs i = false)
    (haux : ∀ k j, k < 64 → j < 73 - 64 →
      (¬ v.neg (aux k j) ↔
        Erdos811Q9SeqCounter.y
          (fun i => !(selectionBool xs i)) k j))
    (hcount : Erdos811Q9SeqCounter.prefixCount
      (fun i => !(selectionBool xs i)) 73 ≤ 64) :
    (∀ j, j < 73 - 64 →
      v.satisfies [ (q9BaseInput j).negate, aux 0 j ]) ∧
    (∀ k, k < 64 → ∀ j, j + 1 < 73 - 64 →
      v.satisfies [ (aux k j).negate, aux k (j + 1) ]) ∧
    (∀ k, k + 1 < 64 → ∀ j, j < 73 - 64 →
      v.satisfies [ (q9BaseInput (j + k + 1)).negate,
        (aux k j).negate, aux (k + 1) j ]) ∧
    (∀ j, j < 73 - 64 →
      v.satisfies [ (q9BaseInput (j + 64)).negate,
        (aux (64 - 1) j).negate ]) := by
  apply Erdos811Q9SeqCounter.seq_counter_satisfies
    (x := fun i => !(selectionBool xs i))
    (input := fun i => q9BaseInput i) (aux := aux)
  · intro i _hi
    simpa [q9BaseInput] using hsel i
  · exact haux
  · decide
  · decide
  · exact hcount

lemma q9_odd_atmost_pos_counter
    {v : Sat.Valuation} {xs : List Nat}
    (t : Nat) (aux : Nat → Nat → Sat.Literal)
    (hsel : ∀ j, ¬ v.neg (q9OddInputPos j) ↔
      q9OddSelectionBool xs j = true)
    (haux : ∀ k j, k < t → j < 36 - t →
      (¬ v.neg (aux k j) ↔
        Erdos811Q9SeqCounter.y (q9OddSelectionBool xs) k j))
    (ht : 0 < t)
    (htn : t ≤ 36)
    (hcount : Erdos811Q9SeqCounter.prefixCount
      (q9OddSelectionBool xs) 36 ≤ t) :
    Erdos811Q9SeqCounter.SeqCounterCNF v
      (fun j => q9OddInputPos j) aux 36 t := by
  apply Erdos811Q9SeqCounter.seq_counter_satisfies_cnf
    (x := q9OddSelectionBool xs)
    (input := fun j => q9OddInputPos j) (aux := aux)
  · intro j _hj
    exact hsel j
  · exact haux
  · exact ht
  · exact htn
  · exact hcount

lemma q9_odd_atmost_neg_counter
    {v : Sat.Valuation} {xs : List Nat}
    (t : Nat) (aux : Nat → Nat → Sat.Literal)
    (hsel : ∀ j, ¬ v.neg (q9OddInputNeg j) ↔
      q9OddSelectionBool xs j = false)
    (haux : ∀ k j, k < t → j < 36 - t →
      (¬ v.neg (aux k j) ↔
        Erdos811Q9SeqCounter.y (q9OddComplementBool xs) k j))
    (ht : 0 < t)
    (htn : t ≤ 36)
    (hcount : Erdos811Q9SeqCounter.prefixCount
      (q9OddComplementBool xs) 36 ≤ t) :
    Erdos811Q9SeqCounter.SeqCounterCNF v
      (fun j => q9OddInputNeg j) aux 36 t := by
  apply Erdos811Q9SeqCounter.seq_counter_satisfies_cnf
    (x := q9OddComplementBool xs)
    (input := fun j => q9OddInputNeg j) (aux := aux)
  · intro j _hj
    simpa [q9OddComplementBool] using hsel j
  · exact haux
  · exact ht
  · exact htn
  · exact hcount

lemma satisfies_clause_of_true_literal
    {v : Sat.Valuation} {ls : Sat.Clause} {l : Sat.Literal}
    (hl : List.Mem l (show List Sat.Literal from ls))
    (htrue : ¬ v.neg l) : v.satisfies ls := by
  induction ls with
  | nil => cases hl
  | cons a rest ih =>
      intro ha
      cases hl with
      | head => exact (htrue ha).elim
      | tail _ hl => exact ih hl

end Erdos811Q9CNFSemantics
