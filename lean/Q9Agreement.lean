import Q9CNFBridge

/-! Agreement lemmas for the q=9 constructive valuations.

The custom valuations contain auxiliary sequential-counter variables, while
`selectionValuation` only describes the 73 vertex variables.  On those
vertex variables the two valuations are definitionally the same.  This file
isolates the resulting transport lemma for negative clauses; the finite
statement that every generated collision clause uses variables below 73 is
kept as a separate executable audit.
-/

namespace Erdos811Q9Agreement

open Mathlib.Tactic.Sat
open Erdos811
open Erdos811Q9CNFSemantics
open Erdos811Q9CNFBridge

lemma q9R4_vertex_agreement (xs : List Nat) {i : Nat} (hi : i < 73) :
    q9R4SelectionValuation xs i ↔ selectionValuation xs i := by
  simp only [q9R4SelectionValuation, if_pos hi, selectionValuation]
  exact selectionBool_true_iff xs i

lemma q9R5_vertex_agreement (xs : List Nat) {i : Nat} (hi : i < 73) :
    q9R5SelectionValuation xs i ↔ selectionValuation xs i := by
  simp only [q9R5SelectionValuation, if_pos hi, selectionValuation]
  exact selectionBool_true_iff xs i

def literalIndex (l : Sat.Literal) : Nat :=
  match l with
  | .pos i => i
  | .neg i => i

def clauseIndicesBelow73 (c : Sat.Clause) : Prop :=
  ∀ (l : Sat.Literal), List.Mem l c → literalIndex l < 73

def literalIndexBelow73Bool (l : Sat.Literal) : Bool :=
  decide (literalIndex l < 73)

def clauseIndicesBelow73Bool : Sat.Clause → Bool
  | [] => true
  | l :: ls => literalIndexBelow73Bool l && clauseIndicesBelow73Bool ls

lemma clauseIndicesBelow73_of_bool_true {c : Sat.Clause}
    (h : clauseIndicesBelow73Bool c = true) :
    clauseIndicesBelow73 c := by
  induction c with
  | nil =>
      intro l hl
      cases hl
  | cons l ls ih =>
      simp only [clauseIndicesBelow73Bool, Bool.and_eq_true] at h
      intro m hm
      rcases List.mem_cons.mp hm with rfl | hm
      · cases m with
        | pos i =>
            exact of_decide_eq_true (by
              simpa [literalIndexBelow73Bool, literalIndex] using h.1)
        | neg i =>
            exact of_decide_eq_true (by
              simpa [literalIndexBelow73Bool, literalIndex] using h.1)
      · exact ih h.2 m hm

def collisionTreeBoundedAll : FmlaTree → Bool
  | .leaf c => q9CollisionClauseBool c && clauseIndicesBelow73Bool c
  | .fork l r => collisionTreeBoundedAll l && collisionTreeBoundedAll r

lemma collisionTreeBoundedAll_true {t : FmlaTree}
    (h : collisionTreeBoundedAll t = true) :
    ∀ c ∈ collisionTreeFlatten t,
      Q9CollisionClause c ∧ clauseIndicesBelow73 c := by
  induction t with
  | leaf c =>
      simp only [collisionTreeBoundedAll, Bool.and_eq_true] at h
      intro d hd
      have heq : d = c := by simpa [collisionTreeFlatten, fmlaTreeFlatten] using hd
      subst d
      exact ⟨h.1, clauseIndicesBelow73_of_bool_true h.2⟩
  | fork l r ihl ihr =>
      simp only [collisionTreeBoundedAll, Bool.and_eq_true] at h
      intro c hc
      simp only [collisionTreeFlatten, fmlaTreeFlatten, List.mem_append] at hc
      rcases hc with hc | hc
      · exact ihl h.1 c hc
      · exact ihr h.2 c hc

lemma negativeClause_satisfied_of_vertex_agreement
    {v w : Sat.Valuation} :
    ∀ lits : List Nat,
      (∀ i ∈ lits, i < 73) →
      (∀ i, i < 73 → (v i ↔ w i)) →
      w.satisfies (negativeClause lits) →
      v.satisfies (negativeClause lits) := by
  intro lits
  induction lits with
  | nil =>
      intro _ _ hw
      cases hw
  | cons a rest ih =>
      intro hbound hagree hw
      simp only [negativeClause, List.map_cons]
      intro ha
      by_cases hva : v a
      · apply ih
        · intro i hi
          exact hbound i (by simp [hi])
        · intro i hi
          exact hagree i hi
        · apply hw
          exact (hagree a (hbound a (by simp))).mp hva
      · exact (hva ha).elim

lemma q9R4_collision_satisfied_constructive
    {xs : List Nat} (hdist : q9EdgeDistinct xs)
    {c : Sat.Clause} (hshape : Q9CollisionClause c)
    (hbound : clauseIndicesBelow73 c) :
    (q9R4SelectionValuation xs).satisfies c := by
  rcases q9_collision_clause_cases hshape with h3 | h4
  · rcases h3 with ⟨a, b, d, rfl, hab, hbd, hcol⟩
    apply negativeClause_satisfied_of_vertex_agreement
      (lits := [a, b, d])
      (fun i hi => hbound (.neg i)
        (List.mem_map.mpr ⟨i, hi, rfl⟩))
      (fun i hi => q9R4_vertex_agreement xs hi)
    exact q9_collision_clause_satisfied hdist
      (by simpa using hshape)
  · rcases h4 with ⟨a, b, c', d, rfl, hab, hbc, hcd, hcol⟩
    apply negativeClause_satisfied_of_vertex_agreement
      (lits := [a, b, c', d])
      (fun i hi => hbound (.neg i)
        (List.mem_map.mpr ⟨i, hi, rfl⟩))
      (fun i hi => q9R4_vertex_agreement xs hi)
    exact q9_collision_clause_satisfied hdist
      (by simpa using hshape)

lemma q9R5_collision_satisfied_constructive
    {xs : List Nat} (hdist : q9EdgeDistinct xs)
    {c : Sat.Clause} (hshape : Q9CollisionClause c)
    (hbound : clauseIndicesBelow73 c) :
    (q9R5SelectionValuation xs).satisfies c := by
  rcases q9_collision_clause_cases hshape with h3 | h4
  · rcases h3 with ⟨a, b, d, rfl, hab, hbd, hcol⟩
    apply negativeClause_satisfied_of_vertex_agreement
      (lits := [a, b, d])
      (fun i hi => hbound (.neg i)
        (List.mem_map.mpr ⟨i, hi, rfl⟩))
      (fun i hi => q9R5_vertex_agreement xs hi)
    exact q9_collision_clause_satisfied hdist
      (by simpa using hshape)
  · rcases h4 with ⟨a, b, c', d, rfl, hab, hbc, hcd, hcol⟩
    apply negativeClause_satisfied_of_vertex_agreement
      (lits := [a, b, c', d])
      (fun i hi => hbound (.neg i)
        (List.mem_map.mpr ⟨i, hi, rfl⟩))
      (fun i hi => q9R5_vertex_agreement xs hi)
    exact q9_collision_clause_satisfied hdist
      (by simpa using hshape)

end Erdos811Q9Agreement
