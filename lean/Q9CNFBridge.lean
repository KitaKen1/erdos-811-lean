import Q9CNFSemantics
import Q9NoInfR4CNF
import Q9NoInfR5CNF

/-! Syntactic bridge for the checked-in q=9 DIMACS branches.

The parsed formulas are deliberately kept as ordinary `Sat.Fmla` constants.
This file first records the exact slices occupied by the base counter and
checks, with a finite native computation, that every clause in those slices
has one of the four semantic sequential-counter shapes.  The proof-facing
lemma below then converts that finite shape audit into ordinary Lean clause
semantics.  The native computation is an auditable intermediate; it is not a
replacement for the eventual kernel/LRAT replay.
-/

namespace Erdos811Q9CNFBridge

open Mathlib.Tactic.Sat
open Erdos811
open Erdos811Q9SeqCounter
open Erdos811Q9CNFSemantics

/- The collision prefix is generated from pairs of equal-coloured edges.  A
   clause has three literals when the two edges share one endpoint and four
   literals otherwise.  This executable classifier checks sorted negative
   literals and the corresponding edge-colour equality without enumerating
   all 36 * C(73,2) source pairs. -/
def q9CollisionClauseBool : Sat.Clause → Bool
  | [.neg a, .neg b, .neg d] =>
      a < b && b < d &&
        (q9EdgeColorFast a b == q9EdgeColorFast a d ||
         q9EdgeColorFast a b == q9EdgeColorFast b d ||
         q9EdgeColorFast a d == q9EdgeColorFast b d)
  | [.neg a, .neg b, .neg c, .neg d] =>
      a < b && b < c && c < d &&
        (q9EdgeColorFast a b == q9EdgeColorFast c d ||
         q9EdgeColorFast a c == q9EdgeColorFast b d ||
         q9EdgeColorFast a d == q9EdgeColorFast b c)
  | _ => false

def Q9CollisionClause (c : Sat.Clause) : Prop :=
  q9CollisionClauseBool c = true

abbrev collisionTreeFlatten : FmlaTree → Sat.Fmla := fmlaTreeFlatten

/- Difference-list form used for the large generated prefixes.  It keeps the
   cost of flattening linear in the number of leaves instead of repeatedly
   traversing left subtrees through `List.append`. -/
def collisionTreeFlattenDL : FmlaTree → Sat.Fmla → Sat.Fmla
  | .leaf c, k => c :: k
  | .fork l r, k => collisionTreeFlattenDL l (collisionTreeFlattenDL r k)

lemma collisionTreeFlattenDL_append (t : FmlaTree) (a b : Sat.Fmla) :
    collisionTreeFlattenDL t (a ++ b) =
      collisionTreeFlattenDL t a ++ b := by
  induction t generalizing a b with
  | leaf c => simp [collisionTreeFlattenDL]
  | fork l r ihl ihr =>
    simp only [collisionTreeFlattenDL]
    rw [ihr, ihl]

lemma collisionTreeFlatten_eq_dl (t : FmlaTree) :
    collisionTreeFlatten t = collisionTreeFlattenDL t [] := by
  induction t with
  | leaf c => rfl
  | fork l r ihl ihr =>
    change collisionTreeFlatten l ++ collisionTreeFlatten r =
      collisionTreeFlattenDL l (collisionTreeFlattenDL r [])
    rw [ihl, ihr]
    change collisionTreeFlattenDL l [] ++ collisionTreeFlattenDL r [] =
      collisionTreeFlattenDL l (collisionTreeFlattenDL r [])
    symm
    simpa using (collisionTreeFlattenDL_append l []
      (collisionTreeFlattenDL r []))

def collisionTreeAll : FmlaTree → Bool
  | .leaf c => q9CollisionClauseBool c
  | .fork l r => collisionTreeAll l && collisionTreeAll r

lemma collisionTreeAll_true
    {t : FmlaTree} (h : collisionTreeAll t = true) :
    ∀ c ∈ collisionTreeFlatten t, Q9CollisionClause c := by
  induction t with
  | leaf c =>
      simp only [collisionTreeAll] at h
      intro d hd
      have heq : d = c := by simpa [fmlaTreeFlatten] using hd
      subst d
      exact h
  | fork l r ihl ihr =>
      simp only [collisionTreeAll, Bool.and_eq_true] at h
      intro c hc
      simp only [fmlaTreeFlatten, List.mem_append] at hc
      rcases hc with hc | hc
      · exact ihl h.1 c hc
      · exact ihr h.2 c hc

lemma q9_collision_clause_cases {c : Sat.Clause} (h : Q9CollisionClause c) :
    (∃ a b d, c = negativeClause [a, b, d] ∧ a < b ∧ b < d ∧
      (q9EdgeColorFast a b = q9EdgeColorFast a d ∨
       q9EdgeColorFast a b = q9EdgeColorFast b d ∨
       q9EdgeColorFast a d = q9EdgeColorFast b d)) ∨
    (∃ a b c' d, c = negativeClause [a, b, c', d] ∧ a < b ∧ b < c' ∧ c' < d ∧
      (q9EdgeColorFast a b = q9EdgeColorFast c' d ∨
       q9EdgeColorFast a c' = q9EdgeColorFast b d ∨
       q9EdgeColorFast a d = q9EdgeColorFast b c')) := by
  cases c with
  | nil => simp [Q9CollisionClause, q9CollisionClauseBool] at h
  | cons l1 r1 =>
    cases r1 with
    | nil => cases l1 <;> simp_all [Q9CollisionClause, q9CollisionClauseBool]
    | cons l2 r2 =>
      cases r2 with
      | nil =>
        cases l1 <;> cases l2 <;>
          simp_all [Q9CollisionClause, q9CollisionClauseBool]
      | cons l3 r3 =>
        cases r3 with
        | nil =>
          cases l1 <;> cases l2 <;> cases l3 <;>
            simp_all [Q9CollisionClause, q9CollisionClauseBool]
          all_goals
            exact Or.inl ⟨_, _, _, rfl, h.1.1, h.1.2, by
              simpa [or_assoc] using h.2⟩
        | cons l4 r4 =>
          cases r4 with
          | nil =>
            cases l1 <;> cases l2 <;> cases l3 <;> cases l4 <;>
              simp_all [Q9CollisionClause, q9CollisionClauseBool]
            all_goals
              exact Or.inr ⟨_, _, _, _, rfl, h.1.1.1, h.1.1.2,
                h.1.2, by simpa [or_assoc] using h.2⟩
          | cons l5 r5 =>
            cases l1 <;> cases l2 <;> cases l3 <;> cases l4 <;>
              simp_all [Q9CollisionClause, q9CollisionClauseBool]

def q9BaseAux (k j : Nat) : Sat.Literal :=
  seqAuxLiteral 73 64 k j

def allSeqCounterShapes (input : Nat → Sat.Literal)
    (aux : Nat → Nat → Sat.Literal) (n t : Nat) : Sat.Fmla → Bool
  | [] => true
  | c :: cs =>
      SeqCounterClauseBool input aux n t c &&
        allSeqCounterShapes input aux n t cs

lemma allSeqCounterShapes_true
    (input : Nat → Sat.Literal) (aux : Nat → Nat → Sat.Literal)
    (n t : Nat) (f : Sat.Fmla)
    (h : allSeqCounterShapes input aux n t f = true) :
    ∀ c ∈ f, SeqCounterClause input aux n t c := by
  induction f with
  | nil => simp
  | cons c cs ih =>
      simp only [allSeqCounterShapes, Bool.and_eq_true] at h
      intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact seqCounterClauseBool_true input aux n t h.1
      · exact ih h.2 d hd

lemma mem_take_or_drop {α : Type} (f : List α) (n : Nat) {c : α}
    (hc : c ∈ f) : c ∈ f.take n ∨ c ∈ f.drop n := by
  rw [← List.take_append_drop n f] at hc
  exact List.mem_append.mp hc

lemma mem_take_or_drop_flat {α : Type} (f : List α) (offset n : Nat)
    {c : α} (hc : c ∈ f.drop offset) :
    c ∈ (f.drop offset).take n ∨ c ∈ f.drop (offset + n) := by
  have hs := mem_take_or_drop (f.drop offset) n hc
  rcases hs with hs | hs
  · exact Or.inl hs
  · right
    simpa only [List.drop_drop] using hs

lemma seq_counter_slice_satisfied
    {v : SatValuation} {x : Nat → Bool} {n t : Nat}
    (input : Nat → SatLiteral) (aux : Nat → Nat → SatLiteral)
    (hinput : ∀ i, i < n → (¬ v.neg (input i) ↔ x i = true))
    (haux : ∀ k j, k < t → j < n - t →
      (¬ v.neg (aux k j) ↔ y x k j))
    (ht : 0 < t) (htn : t ≤ n) (hcount : prefixCount x n ≤ t)
    {f : Sat.Fmla}
    (hshape : ∀ c ∈ f, SeqCounterClause input aux n t c) :
    ∀ c ∈ f, v.satisfies c := by
  intro c hc
  exact seq_counter_satisfies_clause input aux hinput haux ht htn hcount
    (hshape c hc)

def q9R4AtLeastAux (k j : Nat) : Sat.Literal :=
  seqAuxLiteral q9R4AtLeastStart 32 k j

def q9R4AtMostAux (k j : Nat) : Sat.Literal :=
  seqAuxLiteral q9R4AtMostStart 4 k j

def q9R5AtLeastAux (k j : Nat) : Sat.Literal :=
  seqAuxLiteral q9R5AtLeastStart 31 k j

def q9R5AtMostAux (k j : Nat) : Sat.Literal :=
  seqAuxLiteral q9R5AtMostStart 5 k j

/- Decode the interleaved/column-major auxiliary numbering used by PySAT's
   sequential counter.  `q9CounterValue` is intentionally parameterized by a
   start offset and counter width so the r=4 and r=5 branches share one
   arithmetic proof. -/
def q9CounterValue (x : Nat → Bool) (start t i : Nat) : Prop :=
  let off := i - start
  if off < 2 * t then
    y x (off / 2) (off % 2)
  else
    y x (off % t) (off / t)

lemma q9CounterValue_aux (x : Nat → Bool) (start t k j : Nat)
    (ht : 0 < t) (hk : k < t) :
    q9CounterValue x start t (seqAuxId start t k j).pred ↔ y x k j := by
  unfold q9CounterValue seqAuxId seqAuxOffset
  by_cases hj2 : j < 2
  · have hoff : 2 * k + j < 2 * t := by omega
    have hdiv : (2 * k + j) / 2 = k := by omega
    have hmod : (2 * k + j) % 2 = j := by omega
    simp [hj2, hoff, hdiv, hmod]
  · have hge : 2 ≤ j := by omega
    have hdiv : (t * j + k) / t = j := by
      apply Nat.div_eq_of_lt_le
      · simp [Nat.mul_comm]
      · calc
          t * j + k < t * j + t := Nat.add_lt_add_left hk _
          _ = (j + 1) * t := by ring
    have hmod : (t * j + k) % t = k := by
      rw [Nat.add_comm]
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt hk
    have htwo : 2 * t ≤ t * j := by
      have h := Nat.mul_le_mul_left t hge
      simpa [Nat.mul_comm] using h
    have hlt : ¬ (t * j + k < 2 * t) := by omega
    simp [hj2, hlt, hdiv, hmod]

def q9R4SelectionValuation (xs : List Nat) : SatValuation :=
  fun i =>
    if i < 73 then
      selectionBool xs i = true
    else if i < 649 then
      q9CounterValue (fun j => !(selectionBool xs j)) 73 64 i
    else if i < 777 then
      q9CounterValue (q9OddComplementBool xs) 649 32 i
    else if i < 905 then
      q9CounterValue (q9OddSelectionBool xs) 777 4 i
    else False

def q9R5SelectionValuation (xs : List Nat) : SatValuation :=
  fun i =>
    if i < 73 then
      selectionBool xs i = true
    else if i < 649 then
      q9CounterValue (fun j => !(selectionBool xs j)) 73 64 i
    else if i < 804 then
      q9CounterValue (q9OddComplementBool xs) 649 31 i
    else if i < 959 then
      q9CounterValue (q9OddSelectionBool xs) 804 5 i
    else False

lemma q9R4SelectionValuation_input (xs : List Nat) (i : Nat) (hi : i < 73) :
    ¬ (q9R4SelectionValuation xs).neg (q9BaseInput i) ↔
      (fun j => !(selectionBool xs j)) i = true := by
  simp [q9R4SelectionValuation, q9BaseInput, Sat.Valuation.neg, hi]

lemma q9R5SelectionValuation_input (xs : List Nat) (i : Nat) (hi : i < 73) :
    ¬ (q9R5SelectionValuation xs).neg (q9BaseInput i) ↔
      (fun j => !(selectionBool xs j)) i = true := by
  simp [q9R5SelectionValuation, q9BaseInput, Sat.Valuation.neg, hi]

lemma q9R4SelectionValuation_odd_neg_input (xs : List Nat) (j : Nat)
    (hj : j < 36) :
    ¬ (q9R4SelectionValuation xs).neg (q9OddInputNeg j) ↔
      q9OddComplementBool xs j = true := by
  have hi : 2 * j + 1 < 73 := by omega
  simp [q9R4SelectionValuation, q9OddInputNeg, q9OddComplementBool,
    q9OddSelectionBool, Sat.Valuation.neg, hi]

lemma q9R4SelectionValuation_odd_pos_input (xs : List Nat) (j : Nat)
    (hj : j < 36) :
    ¬ (q9R4SelectionValuation xs).neg (q9OddInputPos j) ↔
      q9OddSelectionBool xs j = true := by
  have hi : 2 * j + 1 < 73 := by omega
  simp [q9R4SelectionValuation, q9OddInputPos,
    q9OddSelectionBool, Sat.Valuation.neg, hi]

lemma q9R5SelectionValuation_odd_neg_input (xs : List Nat) (j : Nat)
    (hj : j < 36) :
    ¬ (q9R5SelectionValuation xs).neg (q9OddInputNeg j) ↔
      q9OddComplementBool xs j = true := by
  have hi : 2 * j + 1 < 73 := by omega
  simp [q9R5SelectionValuation, q9OddInputNeg, q9OddComplementBool,
    q9OddSelectionBool, Sat.Valuation.neg, hi]

lemma q9R5SelectionValuation_odd_pos_input (xs : List Nat) (j : Nat)
    (hj : j < 36) :
    ¬ (q9R5SelectionValuation xs).neg (q9OddInputPos j) ↔
      q9OddSelectionBool xs j = true := by
  have hi : 2 * j + 1 < 73 := by omega
  simp [q9R5SelectionValuation, q9OddInputPos,
    q9OddSelectionBool, Sat.Valuation.neg, hi]

lemma q9R4SelectionValuation_base_aux (xs : List Nat) (k j : Nat)
    (hk : k < 64) (hj : j < 9) :
    ¬ (q9R4SelectionValuation xs).neg (q9BaseAux k j) ↔
      y (fun i => !(selectionBool xs i)) k j := by
  change ¬ ¬ (q9R4SelectionValuation xs)
      (seqAuxId 73 64 k j).pred ↔ _
  have hpred : seqAuxId 73 64 k j - 1 =
      73 + (if j ≤ 1 then 2 * k + j else 64 * j + k) := by
    simp [seqAuxId, seqAuxOffset]
  have hlow : 73 ≤ 73 + (if j ≤ 1 then 2 * k + j else 64 * j + k) := by omega
  have hupp : 73 + (if j ≤ 1 then 2 * k + j else 64 * j + k) < 649 := by
    by_cases hj2 : j ≤ 1 <;> simp [hj2] <;> omega
  have haux := q9CounterValue_aux
    (fun i => !(selectionBool xs i)) 73 64 k j (by decide) hk
  simpa [q9R4SelectionValuation, hpred, hlow, hupp] using haux

lemma q9R5SelectionValuation_base_aux (xs : List Nat) (k j : Nat)
    (hk : k < 64) (hj : j < 9) :
    ¬ (q9R5SelectionValuation xs).neg (q9BaseAux k j) ↔
      y (fun i => !(selectionBool xs i)) k j := by
  change ¬ ¬ (q9R5SelectionValuation xs)
      (seqAuxId 73 64 k j).pred ↔ _
  have hpred : seqAuxId 73 64 k j - 1 =
      73 + (if j ≤ 1 then 2 * k + j else 64 * j + k) := by
    simp [seqAuxId, seqAuxOffset]
  have hlow : 73 ≤ 73 + (if j ≤ 1 then 2 * k + j else 64 * j + k) := by omega
  have hupp : 73 + (if j ≤ 1 then 2 * k + j else 64 * j + k) < 649 := by
    by_cases hj2 : j ≤ 1 <;> simp [hj2] <;> omega
  have haux := q9CounterValue_aux
    (fun i => !(selectionBool xs i)) 73 64 k j (by decide) hk
  simpa [q9R5SelectionValuation, hpred, hlow, hupp] using haux

set_option maxRecDepth 100000 in
lemma q9R4SelectionValuation_atleast_aux (xs : List Nat) (k j : Nat)
    (hk : k < 32) (hj : j < 4) :
    ¬ (q9R4SelectionValuation xs).neg (q9R4AtLeastAux k j) ↔
      y (q9OddComplementBool xs) k j := by
  change ¬ ¬ (q9R4SelectionValuation xs)
      (seqAuxId 649 32 k j).pred ↔ _
  have hpred : seqAuxId 649 32 k j - 1 =
      649 + (if j ≤ 1 then 2 * k + j else 32 * j + k) := by
    simp [seqAuxId, seqAuxOffset]
  have hlow : 649 ≤ 649 + (if j ≤ 1 then 2 * k + j else 32 * j + k) := by omega
  have hupp : 649 + (if j ≤ 1 then 2 * k + j else 32 * j + k) < 777 := by
    by_cases hj2 : j ≤ 1 <;> simp [hj2] <;> omega
  have hnot : ¬ (649 + (if j ≤ 1 then 2 * k + j else 32 * j + k) < 73) := by omega
  have haux := q9CounterValue_aux
    (q9OddComplementBool xs) 649 32 k j (by decide) hk
  simpa [q9R4SelectionValuation, hpred, hlow, hupp, hnot] using haux

set_option maxRecDepth 100000 in
lemma q9R4SelectionValuation_atmost_aux (xs : List Nat) (k j : Nat)
    (hk : k < 4) (hj : j < 32) :
    ¬ (q9R4SelectionValuation xs).neg (q9R4AtMostAux k j) ↔
      y (q9OddSelectionBool xs) k j := by
  change ¬ ¬ (q9R4SelectionValuation xs)
      (seqAuxId 777 4 k j).pred ↔ _
  have hpred : seqAuxId 777 4 k j - 1 =
      777 + (if j ≤ 1 then 2 * k + j else 4 * j + k) := by
    simp [seqAuxId, seqAuxOffset]
  have hlow : 777 ≤ 777 + (if j ≤ 1 then 2 * k + j else 4 * j + k) := by omega
  have hupp : 777 + (if j ≤ 1 then 2 * k + j else 4 * j + k) < 905 := by
    by_cases hj2 : j ≤ 1 <;> simp [hj2] <;> omega
  have hnot73 : ¬ (777 + (if j ≤ 1 then 2 * k + j else 4 * j + k) < 73) := by omega
  have hnot649 : ¬ (777 + (if j ≤ 1 then 2 * k + j else 4 * j + k) < 649) := by omega
  have hnot777 : ¬ (777 + (if j ≤ 1 then 2 * k + j else 4 * j + k) < 777) := by omega
  have haux := q9CounterValue_aux
    (q9OddSelectionBool xs) 777 4 k j (by decide) hk
  simpa [q9R4SelectionValuation, hpred, hlow, hupp, hnot73, hnot649, hnot777] using haux

set_option maxRecDepth 100000 in
lemma q9R5SelectionValuation_atleast_aux (xs : List Nat) (k j : Nat)
    (hk : k < 31) (hj : j < 5) :
    ¬ (q9R5SelectionValuation xs).neg (q9R5AtLeastAux k j) ↔
      y (q9OddComplementBool xs) k j := by
  change ¬ ¬ (q9R5SelectionValuation xs)
      (seqAuxId 649 31 k j).pred ↔ _
  have hpred : seqAuxId 649 31 k j - 1 =
      649 + (if j ≤ 1 then 2 * k + j else 31 * j + k) := by
    simp [seqAuxId, seqAuxOffset]
  have hlow : 649 ≤ 649 + (if j ≤ 1 then 2 * k + j else 31 * j + k) := by omega
  have hupp : 649 + (if j ≤ 1 then 2 * k + j else 31 * j + k) < 804 := by
    by_cases hj2 : j ≤ 1 <;> simp [hj2] <;> omega
  have hnot : ¬ (649 + (if j ≤ 1 then 2 * k + j else 31 * j + k) < 73) := by omega
  have haux := q9CounterValue_aux
    (q9OddComplementBool xs) 649 31 k j (by decide) hk
  simpa [q9R5SelectionValuation, hpred, hlow, hupp, hnot] using haux

set_option maxRecDepth 100000 in
lemma q9R5SelectionValuation_atmost_aux (xs : List Nat) (k j : Nat)
    (hk : k < 5) (hj : j < 31) :
    ¬ (q9R5SelectionValuation xs).neg (q9R5AtMostAux k j) ↔
      y (q9OddSelectionBool xs) k j := by
  change ¬ ¬ (q9R5SelectionValuation xs)
      (seqAuxId 804 5 k j).pred ↔ _
  have hpred : seqAuxId 804 5 k j - 1 =
      804 + (if j ≤ 1 then 2 * k + j else 5 * j + k) := by
    simp [seqAuxId, seqAuxOffset]
  have hlow : 804 ≤ 804 + (if j ≤ 1 then 2 * k + j else 5 * j + k) := by omega
  have hupp : 804 + (if j ≤ 1 then 2 * k + j else 5 * j + k) < 959 := by
    by_cases hj2 : j ≤ 1 <;> simp [hj2] <;> omega
  have hnot73 : ¬ (804 + (if j ≤ 1 then 2 * k + j else 5 * j + k) < 73) := by omega
  have hnot649 : ¬ (804 + (if j ≤ 1 then 2 * k + j else 5 * j + k) < 649) := by omega
  have hnot804 : ¬ (804 + (if j ≤ 1 then 2 * k + j else 5 * j + k) < 804) := by omega
  have haux := q9CounterValue_aux
    (q9OddSelectionBool xs) 804 5 k j (by decide) hk
  simpa [q9R5SelectionValuation, hpred, hlow, hupp, hnot73, hnot649, hnot804] using haux

def q9Anchor0BasePart (ctx : Sat.Fmla) : Sat.Fmla :=
  (ctx.drop 94608).take 1097

def q9R4EqualityPart (ctx : Sat.Fmla) : Sat.Fmla :=
  (ctx.drop 95707).take 512

def q9R5EqualityPart (ctx : Sat.Fmla) : Sat.Fmla :=
  (ctx.drop 95707).take 620

lemma q9_r4_base_chunk0_shapes :
    ∀ c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_chunk0,
      SeqCounterClause (fun i => q9BaseInput i) q9BaseAux 73 64 c := by
  apply allSeqCounterShapes_true
  decide

lemma q9_r4_base_chunk1_shapes :
    ∀ c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_chunk1,
      SeqCounterClause (fun i => q9BaseInput i) q9BaseAux 73 64 c := by
  apply allSeqCounterShapes_true
  decide

lemma q9_r4_base_chunk2_shapes :
    ∀ c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_chunk2,
      SeqCounterClause (fun i => q9BaseInput i) q9BaseAux 73 64 c := by
  apply allSeqCounterShapes_true
  decide

lemma q9_r4_base_chunk3_shapes :
    ∀ c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_chunk3,
      SeqCounterClause (fun i => q9BaseInput i) q9BaseAux 73 64 c := by
  apply allSeqCounterShapes_true
  decide

lemma q9_r4_base_chunk4_shapes :
    ∀ c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_chunk4,
      SeqCounterClause (fun i => q9BaseInput i) q9BaseAux 73 64 c := by
  apply allSeqCounterShapes_true
  decide

lemma q9_r4_base_chunk5_shapes :
    ∀ c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_chunk5,
      SeqCounterClause (fun i => q9BaseInput i) q9BaseAux 73 64 c := by
  apply allSeqCounterShapes_true
  decide

lemma q9_r4_base_chunk6_shapes :
    ∀ c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_chunk6,
      SeqCounterClause (fun i => q9BaseInput i) q9BaseAux 73 64 c := by
  apply allSeqCounterShapes_true
  decide

lemma q9_r4_base_chunk7_shapes :
    ∀ c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_chunk7,
      SeqCounterClause (fun i => q9BaseInput i) q9BaseAux 73 64 c := by
  apply allSeqCounterShapes_true
  decide

lemma q9_r4_base_chunk8_shapes :
    ∀ c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_chunk8,
      SeqCounterClause (fun i => q9BaseInput i) q9BaseAux 73 64 c := by
  apply allSeqCounterShapes_true
  decide

lemma q9_r4_base_chunk9_shapes :
    ∀ c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_chunk9,
      SeqCounterClause (fun i => q9BaseInput i) q9BaseAux 73 64 c := by
  apply allSeqCounterShapes_true
  decide

lemma q9_r4_base_chunk10_shapes :
    ∀ c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_chunk10,
      SeqCounterClause (fun i => q9BaseInput i) q9BaseAux 73 64 c := by
  apply allSeqCounterShapes_true
  decide

lemma q9_r4_base_chunk11_shapes :
    ∀ c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_chunk11,
      SeqCounterClause (fun i => q9BaseInput i) q9BaseAux 73 64 c := by
  apply allSeqCounterShapes_true
  decide

lemma q9_r4_base_chunk12_shapes :
    ∀ c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_chunk12,
      SeqCounterClause (fun i => q9BaseInput i) q9BaseAux 73 64 c := by
  apply allSeqCounterShapes_true
  decide

lemma q9_r4_base_chunk13_shapes :
    ∀ c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_chunk13,
      SeqCounterClause (fun i => q9BaseInput i) q9BaseAux 73 64 c := by
  apply allSeqCounterShapes_true
  decide

lemma q9_r4_base_chunk14_shapes :
    ∀ c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_chunk14,
      SeqCounterClause (fun i => q9BaseInput i) q9BaseAux 73 64 c := by
  apply allSeqCounterShapes_true
  decide

lemma q9_r4_base_chunk15_shapes :
    ∀ c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_chunk15,
      SeqCounterClause (fun i => q9BaseInput i) q9BaseAux 73 64 c := by
  apply allSeqCounterShapes_true
  decide

lemma q9_r4_base_chunk16_shapes :
    ∀ c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_chunk16,
      SeqCounterClause (fun i => q9BaseInput i) q9BaseAux 73 64 c := by
  apply allSeqCounterShapes_true
  decide

lemma q9_r4_base_chunk17_shapes :
    ∀ c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_chunk17,
      SeqCounterClause (fun i => q9BaseInput i) q9BaseAux 73 64 c := by
  apply allSeqCounterShapes_true
  decide

set_option maxRecDepth 100000 in
lemma q9_r4_base_shapes :
    ∀ c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_ctx,
      SeqCounterClause (fun i => q9BaseInput i) q9BaseAux 73 64 c := by
  intro c hc
  have h0 := mem_take_or_drop_flat Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_ctx 0 64 hc
  rcases h0 with h0 | hrest
  · change c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_chunk0 at h0
    exact q9_r4_base_chunk0_shapes c h0
  · have h1 := mem_take_or_drop_flat Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_ctx 64 64 hrest
    rcases h1 with h1 | hrest
    · change c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_chunk1 at h1
      exact q9_r4_base_chunk1_shapes c h1
    · have h2 := mem_take_or_drop_flat Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_ctx 128 64 hrest
      rcases h2 with h2 | hrest
      · change c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_chunk2 at h2
        exact q9_r4_base_chunk2_shapes c h2
      · have h3 := mem_take_or_drop_flat Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_ctx 192 64 hrest
        rcases h3 with h3 | hrest
        · change c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_chunk3 at h3
          exact q9_r4_base_chunk3_shapes c h3
        · have h4 := mem_take_or_drop_flat Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_ctx 256 64 hrest
          rcases h4 with h4 | hrest
          · change c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_chunk4 at h4
            exact q9_r4_base_chunk4_shapes c h4
          · have h5 := mem_take_or_drop_flat Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_ctx 320 64 hrest
            rcases h5 with h5 | hrest
            · change c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_chunk5 at h5
              exact q9_r4_base_chunk5_shapes c h5
            · have h6 := mem_take_or_drop_flat Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_ctx 384 64 hrest
              rcases h6 with h6 | hrest
              · change c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_chunk6 at h6
                exact q9_r4_base_chunk6_shapes c h6
              · have h7 := mem_take_or_drop_flat Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_ctx 448 64 hrest
                rcases h7 with h7 | hrest
                · change c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_chunk7 at h7
                  exact q9_r4_base_chunk7_shapes c h7
                · have h8 := mem_take_or_drop_flat Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_ctx 512 64 hrest
                  rcases h8 with h8 | hrest
                  · change c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_chunk8 at h8
                    exact q9_r4_base_chunk8_shapes c h8
                  · have h9 := mem_take_or_drop_flat Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_ctx 576 64 hrest
                    rcases h9 with h9 | hrest
                    · change c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_chunk9 at h9
                      exact q9_r4_base_chunk9_shapes c h9
                    · have h10 := mem_take_or_drop_flat Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_ctx 640 64 hrest
                      rcases h10 with h10 | hrest
                      · change c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_chunk10 at h10
                        exact q9_r4_base_chunk10_shapes c h10
                      · have h11 := mem_take_or_drop_flat Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_ctx 704 64 hrest
                        rcases h11 with h11 | hrest
                        · change c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_chunk11 at h11
                          exact q9_r4_base_chunk11_shapes c h11
                        · have h12 := mem_take_or_drop_flat Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_ctx 768 64 hrest
                          rcases h12 with h12 | hrest
                          · change c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_chunk12 at h12
                            exact q9_r4_base_chunk12_shapes c h12
                          · have h13 := mem_take_or_drop_flat Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_ctx 832 64 hrest
                            rcases h13 with h13 | hrest
                            · change c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_chunk13 at h13
                              exact q9_r4_base_chunk13_shapes c h13
                            · have h14 := mem_take_or_drop_flat Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_ctx 896 64 hrest
                              rcases h14 with h14 | hrest
                              · change c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_chunk14 at h14
                                exact q9_r4_base_chunk14_shapes c h14
                              · have h15 := mem_take_or_drop_flat Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_ctx 960 64 hrest
                                rcases h15 with h15 | hrest
                                · change c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_chunk15 at h15
                                  exact q9_r4_base_chunk15_shapes c h15
                                · have h16 := mem_take_or_drop_flat Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_ctx 1024 64 hrest
                                  rcases h16 with h16 | hrest
                                  · change c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_chunk16 at h16
                                    exact q9_r4_base_chunk16_shapes c h16
                                  · have h17 := mem_take_or_drop_flat Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_ctx 1088 9 hrest
                                    rcases h17 with h17 | hrest
                                    · change c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_chunk17 at h17
                                      exact q9_r4_base_chunk17_shapes c h17
                                    · have hempty : Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_ctx.drop 1097 = [] := by
                                        decide
                                      rw [hempty] at hrest
                                      simp at hrest

lemma q9_r4_base_satisfied
    {v : SatValuation} {x : Nat → Bool}
    (hinput : ∀ i, i < 73 → (¬ v.neg (q9BaseInput i) ↔ x i = true))
    (haux : ∀ k j, k < 64 → j < 73 - 64 →
      (¬ v.neg (q9BaseAux k j) ↔ y x k j))
    (hcount : prefixCount x 73 ≤ 64) :
    ∀ c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_ctx,
      v.satisfies c := by
  exact seq_counter_slice_satisfied (fun i => q9BaseInput i) q9BaseAux
    hinput haux (by decide) (by decide) hcount q9_r4_base_shapes

lemma q9_r4_base_satisfied_selection
    {xs : List Nat}
    (haux : ∀ k j, k < 64 → j < 73 - 64 →
      (¬ (selectionValuation xs).neg (q9BaseAux k j) ↔
        y (fun i => !(selectionBool xs i)) k j))
    (hcount : prefixCount (fun i => !(selectionBool xs i)) 73 ≤ 64) :
    ∀ c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_ctx,
      (selectionValuation xs).satisfies c := by
  apply q9_r4_base_satisfied
    (v := selectionValuation xs)
    (x := fun i => !(selectionBool xs i))
  · intro i _hi
    simpa [q9BaseInput, selectionBool] using selection_input_neg xs i
  · exact haux
  · exact hcount

lemma q9_r5_base_shapes :
    ∀ c ∈ Erdos811Q9NoInfR5CNF.q9_noinf_r5_base_ctx,
      SeqCounterClause (fun i => q9BaseInput i) q9BaseAux 73 64 c := by
  intro c hc
  exact q9_r4_base_shapes c hc

lemma q9_r5_base_satisfied
    {v : SatValuation} {x : Nat → Bool}
    (hinput : ∀ i, i < 73 → (¬ v.neg (q9BaseInput i) ↔ x i = true))
    (haux : ∀ k j, k < 64 → j < 73 - 64 →
      (¬ v.neg (q9BaseAux k j) ↔ y x k j))
    (hcount : prefixCount x 73 ≤ 64) :
    ∀ c ∈ Erdos811Q9NoInfR5CNF.q9_noinf_r5_base_ctx,
      v.satisfies c := by
  exact seq_counter_slice_satisfied (fun i => q9BaseInput i) q9BaseAux
    hinput haux (by decide) (by decide) hcount q9_r5_base_shapes

set_option maxRecDepth 100000 in
lemma q9_r4_eq_atleast_shapes :
    ∀ c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_eq_atleast_ctx,
      SeqCounterClause (fun j => q9OddInputNeg j) q9R4AtLeastAux 36 32 c := by
  apply allSeqCounterShapes_true
  decide

set_option maxRecDepth 100000 in
lemma q9_r4_eq_atmost_shapes :
    ∀ c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_eq_atmost_ctx,
      SeqCounterClause (fun j => q9OddInputPos j) q9R4AtMostAux 36 4 c := by
  apply allSeqCounterShapes_true
  decide

set_option maxRecDepth 100000 in
lemma q9_r5_eq_atleast_shapes :
    ∀ c ∈ Erdos811Q9NoInfR5CNF.q9_noinf_r5_eq_atleast_ctx,
      SeqCounterClause (fun j => q9OddInputNeg j) q9R5AtLeastAux 36 31 c := by
  apply allSeqCounterShapes_true
  decide

set_option maxRecDepth 100000 in
lemma q9_r5_eq_atmost_shapes :
    ∀ c ∈ Erdos811Q9NoInfR5CNF.q9_noinf_r5_eq_atmost_ctx,
      SeqCounterClause (fun j => q9OddInputPos j) q9R5AtMostAux 36 5 c := by
  apply allSeqCounterShapes_true
  decide

lemma q9_r4_eq_atleast_satisfied
    {v : SatValuation} {x : Nat → Bool}
    (hinput : ∀ j, j < 36 → (¬ v.neg (q9OddInputNeg j) ↔ x j = true))
    (haux : ∀ k j, k < 32 → j < 36 - 32 →
      (¬ v.neg (q9R4AtLeastAux k j) ↔ y x k j))
    (hcount : prefixCount x 36 ≤ 32) :
    ∀ c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_eq_atleast_ctx,
      v.satisfies c := by
  exact seq_counter_slice_satisfied (fun j => q9OddInputNeg j)
    q9R4AtLeastAux hinput haux (by decide) (by decide) hcount q9_r4_eq_atleast_shapes

lemma q9_r4_eq_atmost_satisfied
    {v : SatValuation} {x : Nat → Bool}
    (hinput : ∀ j, j < 36 → (¬ v.neg (q9OddInputPos j) ↔ x j = true))
    (haux : ∀ k j, k < 4 → j < 36 - 4 →
      (¬ v.neg (q9R4AtMostAux k j) ↔ y x k j))
    (hcount : prefixCount x 36 ≤ 4) :
    ∀ c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_eq_atmost_ctx,
      v.satisfies c := by
  exact seq_counter_slice_satisfied (fun j => q9OddInputPos j)
    q9R4AtMostAux hinput haux (by decide) (by decide) hcount q9_r4_eq_atmost_shapes

lemma q9_r5_eq_atleast_satisfied
    {v : SatValuation} {x : Nat → Bool}
    (hinput : ∀ j, j < 36 → (¬ v.neg (q9OddInputNeg j) ↔ x j = true))
    (haux : ∀ k j, k < 31 → j < 36 - 31 →
      (¬ v.neg (q9R5AtLeastAux k j) ↔ y x k j))
    (hcount : prefixCount x 36 ≤ 31) :
    ∀ c ∈ Erdos811Q9NoInfR5CNF.q9_noinf_r5_eq_atleast_ctx,
      v.satisfies c := by
  exact seq_counter_slice_satisfied (fun j => q9OddInputNeg j)
    q9R5AtLeastAux hinput haux (by decide) (by decide) hcount q9_r5_eq_atleast_shapes

lemma q9_r5_eq_atmost_satisfied
    {v : SatValuation} {x : Nat → Bool}
    (hinput : ∀ j, j < 36 → (¬ v.neg (q9OddInputPos j) ↔ x j = true))
    (haux : ∀ k j, k < 5 → j < 36 - 5 →
      (¬ v.neg (q9R5AtMostAux k j) ↔ y x k j))
    (hcount : prefixCount x 36 ≤ 5) :
    ∀ c ∈ Erdos811Q9NoInfR5CNF.q9_noinf_r5_eq_atmost_ctx,
      v.satisfies c := by
  exact seq_counter_slice_satisfied (fun j => q9OddInputPos j)
    q9R5AtMostAux hinput haux (by decide) (by decide) hcount q9_r5_eq_atmost_shapes

lemma q9_r4_anchor_satisfied {xs : List Nat}
    (h0 : 0 ∈ xs) (h72 : 72 ∉ xs) :
    ∀ c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_anchor_ctx,
      (selectionValuation xs).satisfies c := by
  intro c hc
  change c ∈ [[.pos 0], [.neg 72]] at hc
  rcases List.mem_cons.mp hc with hc | hc
  · have heq : c = [.pos 0] := hc
    subst c
    exact selection_anchor_pos h0
  · have heq : c = [.neg 72] := by
      exact List.mem_singleton.mp hc
    subst c
    exact selection_anchor_neg h72

lemma q9_r5_anchor_satisfied {xs : List Nat}
    (h0 : 0 ∈ xs) (h72 : 72 ∉ xs) :
    ∀ c ∈ Erdos811Q9NoInfR5CNF.q9_noinf_r5_anchor_ctx,
      (selectionValuation xs).satisfies c := by
  intro c hc
  exact q9_r4_anchor_satisfied h0 h72 c hc

/- The balanced tree is definitionally the parsed collision slice.  The
   explicit slice constant is used here so later membership proofs do not
   normalize a 96k-element take/drop expression. -/
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma q9_r4_collision_tree_flatten :
    collisionTreeFlatten
        Erdos811Q9NoInfR4CNF.q9_noinf_r4_collision_tree =
      Erdos811Q9NoInfR4CNF.q9_noinf_r4_collision_ctx := by
  symm
  exact Mathlib.Tactic.Sat.fmlaTreeFlattenOpaque_eq _

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma q9_r5_collision_tree_flatten :
    collisionTreeFlatten
        Erdos811Q9NoInfR5CNF.q9_noinf_r5_collision_tree =
      Erdos811Q9NoInfR5CNF.q9_noinf_r5_collision_ctx := by
  symm
  exact Mathlib.Tactic.Sat.fmlaTreeFlattenOpaque_eq _

lemma q9_collision_clause_satisfied
    {xs : List Nat} (hdist : q9EdgeDistinct xs)
    {c : Sat.Clause} (hshape : Q9CollisionClause c) :
    (selectionValuation xs).satisfies c := by
  rcases q9_collision_clause_cases hshape with h3 | h4
  · rcases h3 with ⟨a, b, d, rfl, hab, hbd, hcol⟩
    apply selection_negativeClause_of_not_all_mem
    intro hall
    have ha : a ∈ xs := hall a (by simp)
    have hb : b ∈ xs := hall b (by simp)
    have hd : d ∈ xs := hall d (by simp)
    rcases hcol with hcol | hcol | hcol
    · have hsame : ¬ SameUndirectedEdge a b a d := by
        simp [SameUndirectedEdge]
        omega
      exact (hdist ha hb ha hd (by omega) (by omega) hsame) hcol
    · have hsame : ¬ SameUndirectedEdge a b b d := by
        simp [SameUndirectedEdge]
        omega
      exact (hdist ha hb hb hd (by omega) (by omega) hsame) hcol
    · have hsame : ¬ SameUndirectedEdge a d b d := by
        simp [SameUndirectedEdge]
        omega
      exact (hdist ha hd hb hd (by omega) (by omega) hsame) hcol
  · rcases h4 with ⟨a, b, c', d, rfl, hab, hbc, hcd, hcol⟩
    rcases hcol with hcol | hcol | hcol
    · apply selection_collision_clause hdist (by omega) (by omega) (by
        simp [SameUndirectedEdge]
        omega) hcol
    · have hs := selection_collision_clause (xs := xs) hdist (by omega) (by omega) (by
        simp [SameUndirectedEdge]
        omega) hcol
      change (selectionValuation xs).satisfies
        (negativeClause [a, c', b, d]) at hs
      change (selectionValuation xs).satisfies
        (negativeClause [a, b, c', d])
      intro ha hb hc hd
      exact hs ha hc hb hd
    · have hs := selection_collision_clause (xs := xs) hdist (by omega) (by omega) (by
        simp [SameUndirectedEdge]
        omega) hcol
      change (selectionValuation xs).satisfies
        (negativeClause [a, d, b, c']) at hs
      change (selectionValuation xs).satisfies
        (negativeClause [a, b, c', d])
      intro ha hb hc hd
      exact hs ha hd hb hc

lemma q9_r4_base_chunk0_satisfied
    {v : SatValuation} {x : Nat → Bool}
    (hinput : ∀ i, i < 73 → (¬ v.neg (q9BaseInput i) ↔ x i = true))
    (haux : ∀ k j, k < 64 → j < 73 - 64 →
      (¬ v.neg (q9BaseAux k j) ↔ y x k j))
    (hcount : prefixCount x 73 ≤ 64) :
    ∀ c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_chunk0,
      v.satisfies c := by
  exact seq_counter_slice_satisfied (fun i => q9BaseInput i) q9BaseAux
    hinput haux (by decide) (by decide) hcount q9_r4_base_chunk0_shapes

/- The 1097 base clauses are audited in 64-clause slices and then assembled
   by `q9_r4_base_shapes`.  Keeping the computation chunked avoids the
   Lean 4.34 native compiler's join-point failure on the unsliced formula. -/

end Erdos811Q9CNFBridge
