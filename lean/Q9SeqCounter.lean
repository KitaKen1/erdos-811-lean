import Mathlib

/-!
Semantic facts for the irredundant sequential-counter clauses used by the
checked-in q=9 certificates.  The encoder's auxiliary `y(k,j)` means that the
prefix ending at `j+k` contains at least `k+1` true input literals.
-/

namespace Erdos811Q9SeqCounter

open Mathlib.Tactic.Sat

abbrev SatValuation := Sat.Valuation
abbrev SatLiteral := Sat.Literal

/- A transparent equality decision procedure for the two-constructor literal
   type.  `Sat.Clause` is a reducible list definition, but its equality is
   written explicitly as list equality below so this instance is usable by
   finite computational audits. -/
instance satLiteralDecidableEq : DecidableEq SatLiteral := by
  intro a b
  cases a with
  | pos i =>
      cases b with
      | pos j => exact decidable_of_iff (i = j) (by simp)
      | neg j => exact isFalse (by simp)
  | neg i =>
      cases b with
      | pos j => exact isFalse (by simp)
      | neg j => exact decidable_of_iff (i = j) (by simp)

def valuationOfBool (x : Nat → Bool) : SatValuation :=
  fun i => x i = true

lemma valuationOfBool_pos_neg (x : Nat → Bool) (i : Nat) :
    ¬ (valuationOfBool x).neg (.pos i) ↔ x i = true := by
  simp [valuationOfBool, Sat.Valuation.neg]

lemma valuationOfBool_neg_neg (x : Nat → Bool) (i : Nat) :
    ¬ (valuationOfBool x).neg (.neg i) ↔ x i = false := by
  simp [valuationOfBool, Sat.Valuation.neg]

def prefixCount (x : Nat → Bool) (n : Nat) : Nat :=
  (Finset.range n).sum (fun i => if x i = true then 1 else 0)

def y (x : Nat → Bool) (k j : Nat) : Prop :=
  k + 1 ≤ prefixCount x (j + k + 1)

lemma neg_negate (v : SatValuation) (l : SatLiteral) :
    v.neg l.negate ↔ ¬ v.neg l := by
  cases l <;> simp [Sat.Valuation.neg, Sat.Literal.negate, Classical.not_not]

lemma satisfies_pair_of_imp {v : SatValuation} {l₁ l₂ : SatLiteral}
    (h : v.neg l₁ → v.neg l₂ → False) :
    v.satisfies [l₁, l₂] := by
  exact h

lemma satisfies_triple_of_imp {v : SatValuation}
    {l₁ l₂ l₃ : SatLiteral}
    (h : v.neg l₁ → v.neg l₂ → v.neg l₃ → False) :
    v.satisfies [l₁, l₂, l₃] := by
  exact h

lemma seq_base_clause {v : SatValuation} {l a : SatLiteral}
    (h : v.neg l.negate → ¬ v.neg a) :
    v.satisfies [l.negate, a] := by
  exact h

lemma seq_mono_clause {v : SatValuation} {a b : SatLiteral}
    (h : v.neg a.negate → ¬ v.neg b) :
    v.satisfies [a.negate, b] := by
  exact h

lemma seq_step_clause {v : SatValuation} {l a b : SatLiteral}
    (h : v.neg l.negate → v.neg a.negate → ¬ v.neg b) :
    v.satisfies [l.negate, a.negate, b] := by
  exact h

lemma seq_overflow_clause {v : SatValuation} {l a : SatLiteral}
    (h : v.neg l.negate → v.neg a.negate → False) :
    v.satisfies [l.negate, a.negate] := by
  exact h

lemma prefixCount_succ (x : Nat → Bool) (n : Nat) :
    prefixCount x (n + 1) = prefixCount x n + (if x n = true then 1 else 0) := by
  unfold prefixCount
  rw [show n + 1 = Nat.succ n by omega, Finset.sum_range_succ]

lemma prefixCount_mono (x : Nat → Bool) {a b : Nat} (hab : a ≤ b) :
    prefixCount x a ≤ prefixCount x b := by
  induction b with
  | zero =>
      have ha : a = 0 := by omega
      subst a
      exact le_rfl
  | succ b ih =>
      by_cases h : a ≤ b
      · have hi := ih h
        rw [show b + 1 = b + 1 by rfl, prefixCount_succ]
        exact hi.trans (Nat.le_add_right _ _)
      · have : a = b + 1 := by omega
        subst a
        exact le_rfl

lemma y_mono (x : Nat → Bool) {k j : Nat} :
    y x k j → y x k (j + 1) := by
  intro h
  unfold y at h ⊢
  exact h.trans (prefixCount_mono x (by omega))

lemma y_step (x : Nat → Bool) {k j : Nat}
    (h : y x k j) (hx : x (j + k + 1) = true) :
    y x (k + 1) j := by
  unfold y at h ⊢
  have hp : j + (k + 1) + 1 = (j + k + 1) + 1 := by omega
  rw [hp, prefixCount_succ]
  simp [hx]
  omega

lemma y_overflow (x : Nat → Bool) {t j : Nat}
    (hcount : prefixCount x (j + t + 1) ≤ t)
    (hy : y x (t - 1) j) : x (j + t) = false := by
  unfold y at hy
  by_cases ht0 : t = 0
  · subst t
    simp at hy hcount
    omega
  have ht : 0 < t := Nat.pos_of_ne_zero ht0
  have htm : j + (t - 1) + 1 = j + t := by omega
  rw [htm] at hy
  have hp : j + t + 1 = (j + t) + 1 := by omega
  rw [hp, prefixCount_succ] at hcount
  cases hxb : x (j + t) with
  | false => rfl
  | true =>
      simp [hxb] at hcount
      omega

lemma y_overflow_of_total (x : Nat → Bool) {n t j : Nat}
    (hjn : j + t + 1 ≤ n)
    (hcount : prefixCount x n ≤ t)
    (hy : y x (t - 1) j) : x (j + t) = false := by
  apply y_overflow x (j := j) (t := t)
  · exact (prefixCount_mono x hjn).trans hcount
  · exact hy

lemma seq_base_of_y {v : SatValuation} {x : Nat → Bool}
    {j : Nat} {l a : SatLiteral}
    (hl : ¬ v.neg l ↔ x j = true)
    (ha : ¬ v.neg a ↔ y x 0 j)
    (hy : x j = true → y x 0 j) :
    v.satisfies [l.negate, a] := by
  apply seq_base_clause
  intro hL hA
  have hx : x j = true := hl.mp ((neg_negate v l).mp hL)
  have hY : y x 0 j := hy hx
  exact (ha.mpr hY) hA

lemma seq_mono_of_y {v : SatValuation} {x : Nat → Bool}
    {k j : Nat} {a b : SatLiteral}
    (ha : ¬ v.neg a ↔ y x k j)
    (hb : ¬ v.neg b ↔ y x k (j + 1)) :
    v.satisfies [a.negate, b] := by
  apply seq_mono_clause
  intro hA hB
  have hY : y x k j := ha.mp ((neg_negate v a).mp hA)
  have hY' : y x k (j + 1) := y_mono x hY
  exact (hb.mpr hY') hB

lemma seq_step_of_y {v : SatValuation} {x : Nat → Bool}
    {k j : Nat} {l a b : SatLiteral}
    (hl : ¬ v.neg l ↔ x (j + k + 1) = true)
    (ha : ¬ v.neg a ↔ y x k j)
    (hb : ¬ v.neg b ↔ y x (k + 1) j)
    (hy : x (j + k + 1) = true → y x k j → y x (k + 1) j) :
    v.satisfies [l.negate, a.negate, b] := by
  apply seq_step_clause
  intro hL hA hB
  have hx : x (j + k + 1) = true := hl.mp ((neg_negate v l).mp hL)
  have hY : y x k j := ha.mp ((neg_negate v a).mp hA)
  have hY' : y x (k + 1) j := hy hx hY
  exact (hb.mpr hY') hB

lemma seq_overflow_of_y {v : SatValuation} {x : Nat → Bool}
    {n t j : Nat} {l a : SatLiteral}
    (hl : ¬ v.neg l ↔ x (j + t) = true)
    (ha : ¬ v.neg a ↔ y x (t - 1) j)
    (hjn : j + t + 1 ≤ n)
    (hcount : prefixCount x n ≤ t) :
    v.satisfies [l.negate, a.negate] := by
  apply seq_overflow_clause
  intro hL hA
  have hx : x (j + t) = true := hl.mp ((neg_negate v l).mp hL)
  have hY : y x (t - 1) j := ha.mp ((neg_negate v a).mp hA)
  have hx0 : x (j + t) = false := y_overflow_of_total x hjn hcount hY
  simp [hx] at *

lemma seq_counter_satisfies
    {v : SatValuation} {x : Nat → Bool} {n t : Nat}
    (input : Nat → SatLiteral) (aux : Nat → Nat → SatLiteral)
    (hinput : ∀ i, i < n → (¬ v.neg (input i) ↔ x i = true))
    (haux : ∀ k j, k < t → j < n - t →
      (¬ v.neg (aux k j) ↔ y x k j))
    (ht : 0 < t)
    (_htn : t ≤ n)
    (hcount : prefixCount x n ≤ t) :
    (∀ j, j < n - t →
      v.satisfies [ (input j).negate, aux 0 j ]) ∧
    (∀ k, k < t → ∀ j, j + 1 < n - t →
      v.satisfies [ (aux k j).negate, aux k (j + 1) ]) ∧
    (∀ k, k + 1 < t → ∀ j, j < n - t →
      v.satisfies [ (input (j + k + 1)).negate,
        (aux k j).negate, aux (k + 1) j ]) ∧
    (∀ j, j < n - t →
      v.satisfies [ (input (j + t)).negate, (aux (t - 1) j).negate ]) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    apply seq_base_of_y (hinput j (by omega)) (haux 0 j ht hj)
    intro hx
    unfold y
    rw [prefixCount_succ]
    simp [hx]
  · intro k hk j hj
    exact seq_mono_of_y (haux k j (by omega) (by omega))
      (haux k (j + 1) (by omega) (by omega))
  · intro k hk j hj
    exact seq_step_of_y (hinput (j + k + 1) (by omega))
      (haux k j (by omega) (by omega))
      (haux (k + 1) j (by omega) (by omega))
      (fun hx hy => y_step x hy hx)
  · intro j hj
    apply seq_overflow_of_y (hinput (j + t) (by omega))
      (haux (t - 1) j (Nat.sub_lt ht (by decide)) hj)
    · have hsum : j + t < n := Nat.add_lt_of_lt_sub hj
      have hsucc : Nat.succ (j + t) ≤ n := Nat.succ_le_of_lt hsum
      simpa [Nat.succ_eq_add_one] using hsucc
    · exact hcount

def SeqCounterCNF (v : SatValuation) (input : Nat → SatLiteral)
    (aux : Nat → Nat → SatLiteral) (n t : Nat) : Prop :=
  (∀ j, j < n - t →
      v.satisfies [ (input j).negate, aux 0 j ]) ∧
    (∀ k, k < t → ∀ j, j + 1 < n - t →
      v.satisfies [ (aux k j).negate, aux k (j + 1) ]) ∧
    (∀ k, k + 1 < t → ∀ j, j < n - t →
      v.satisfies [ (input (j + k + 1)).negate,
        (aux k j).negate, aux (k + 1) j ]) ∧
    (∀ j, j < n - t →
      v.satisfies [ (input (j + t)).negate, (aux (t - 1) j).negate ])

/- A syntactic membership predicate for the four clause families.  The
   DIMACS parser does not preserve the encoder's generation order as a
   mathematical notion, so the semantic bridge uses this predicate rather
   than relying on a particular list ordering. -/
def SeqCounterClause (input : Nat → SatLiteral)
    (aux : Nat → Nat → SatLiteral) (n t : Nat) (c : Sat.Clause) : Prop :=
  (∃ j, j < n - t ∧
    c = [ (input j).negate, aux 0 j ]) ∨
  (∃ k, k < t ∧ ∃ j, j + 1 < n - t ∧
    c = [ (aux k j).negate, aux k (j + 1) ]) ∨
  (∃ k, k + 1 < t ∧ ∃ j, j < n - t ∧
    c = [ (input (j + k + 1)).negate,
      (aux k j).negate, aux (k + 1) j ]) ∨
  (∃ j, j < n - t ∧
    c = [ (input (j + t)).negate, (aux (t - 1) j).negate ])

lemma seq_counter_satisfies_clause
    {v : SatValuation} {x : Nat → Bool} {n t : Nat}
    (input : Nat → SatLiteral) (aux : Nat → Nat → SatLiteral)
    (hinput : ∀ i, i < n → (¬ v.neg (input i) ↔ x i = true))
    (haux : ∀ k j, k < t → j < n - t →
      (¬ v.neg (aux k j) ↔ y x k j))
    (ht : 0 < t) (htn : t ≤ n) (hcount : prefixCount x n ≤ t)
    {c : Sat.Clause} (hc : SeqCounterClause input aux n t c) :
    v.satisfies c := by
  have hall := seq_counter_satisfies input aux hinput haux ht htn hcount
  rcases hc with hbase | hrest
  · rcases hbase with ⟨j, hj, rfl⟩
    exact hall.1 j hj
  rcases hrest with hmono | hrest
  · rcases hmono with ⟨k, hk, j, hj, rfl⟩
    exact hall.2.1 k hk j hj
  rcases hrest with hstep | hover
  · rcases hstep with ⟨k, hk, j, hj, rfl⟩
    exact hall.2.2.1 k hk j hj
  · rcases hover with ⟨j, hj, rfl⟩
    exact hall.2.2.2 j hj

/- A bounded-witness version of the shape predicate.  Unlike the convenient
   Nat-indexed form above, this one has a computational `Decidable` instance;
   it is used to audit the parsed DIMACS list with a finite checker. -/
def SeqCounterClauseFin (input : Nat → SatLiteral)
    (aux : Nat → Nat → SatLiteral) (n t : Nat) (c : Sat.Clause) : Prop :=
  (∃ j : Fin (n - t),
    (show List SatLiteral from c) =
      [ (input j.val).negate, aux 0 j.val ]) ∨
  (∃ k : Fin t, ∃ j : Fin (n - t - 1),
    (show List SatLiteral from c) =
      [ (aux k.val j.val).negate, aux k.val (j.val + 1) ]) ∨
  (∃ k : Fin (t - 1), ∃ j : Fin (n - t),
    (show List SatLiteral from c) =
      [ (input (j.val + k.val + 1)).negate,
        (aux k.val j.val).negate, aux (k.val + 1) j.val ]) ∨
  (∃ j : Fin (n - t),
    (show List SatLiteral from c) =
    [ (input (j.val + t)).negate, (aux (t - 1) j.val).negate ])

def clauseEqBool (a b : Sat.Clause) : Bool :=
  decide ((show List SatLiteral from a) = (show List SatLiteral from b))

/- Executable, bounded counterpart of `SeqCounterClause`.  The finite
   disjunctions are represented by `List.any`, so this definition has a
   computational decision procedure even though the proposition-valued
   shape predicate contains unbounded Nat existentials. -/
def SeqCounterClauseBool (input : Nat → SatLiteral)
    (aux : Nat → Nat → SatLiteral) (n t : Nat) (c : Sat.Clause) : Bool :=
  (List.range (n - t)).any (fun j =>
    clauseEqBool c [ (input j).negate, aux 0 j ]) ||
  (List.range t).any (fun k =>
    (List.range (n - t - 1)).any (fun j =>
      clauseEqBool c [ (aux k j).negate, aux k (j + 1) ]) ) ||
  (List.range (t - 1)).any (fun k =>
    (List.range (n - t)).any (fun j =>
      clauseEqBool c [ (input (j + k + 1)).negate,
        (aux k j).negate, aux (k + 1) j ]) ) ||
  (List.range (n - t)).any (fun j =>
    clauseEqBool c [ (input (j + t)).negate, (aux (t - 1) j).negate ])

lemma seqCounterClauseBool_true
    (input : Nat → SatLiteral) (aux : Nat → Nat → SatLiteral)
  (n t : Nat) {c : Sat.Clause}
    (h : SeqCounterClauseBool input aux n t c = true) :
    SeqCounterClause input aux n t c := by
  simp [SeqCounterClauseBool, List.any_eq_true, clauseEqBool] at h
  rcases h with hleft | hover
  · rcases hleft with hleft | hstep
    · rcases hleft with hbase | hmono
      · exact Or.inl hbase
      · rcases hmono with ⟨k, hk, j, hj, heq⟩
        exact Or.inr (Or.inl ⟨k, hk, j, by omega, heq⟩)
    · rcases hstep with ⟨k, hk, j, hj, heq⟩
      exact Or.inr (Or.inr (Or.inl ⟨k, by omega, j, hj, heq⟩))
  · exact Or.inr (Or.inr (Or.inr hover))

lemma seq_counter_satisfies_clause_fin
    {v : SatValuation} {x : Nat → Bool} {n t : Nat}
    (input : Nat → SatLiteral) (aux : Nat → Nat → SatLiteral)
    (hinput : ∀ i, i < n → (¬ v.neg (input i) ↔ x i = true))
    (haux : ∀ k j, k < t → j < n - t →
      (¬ v.neg (aux k j) ↔ y x k j))
    (ht : 0 < t) (htn : t ≤ n) (hcount : prefixCount x n ≤ t)
    {c : Sat.Clause} (hc : SeqCounterClauseFin input aux n t c) :
    v.satisfies c := by
  have hall := seq_counter_satisfies input aux hinput haux ht htn hcount
  rcases hc with hbase | hrest
  · rcases hbase with ⟨j, rfl⟩
    exact hall.1 j.val j.isLt
  rcases hrest with hmono | hrest
  · rcases hmono with ⟨k, j, rfl⟩
    exact hall.2.1 k.val k.isLt j.val (by omega)
  rcases hrest with hstep | hover
  · rcases hstep with ⟨k, j, rfl⟩
    exact hall.2.2.1 k.val (by omega) j.val j.isLt
  · rcases hover with ⟨j, rfl⟩
    exact hall.2.2.2 j.val j.isLt

lemma seq_counter_satisfies_cnf
    {v : SatValuation} {x : Nat → Bool} {n t : Nat}
    (input : Nat → SatLiteral) (aux : Nat → Nat → SatLiteral)
    (hinput : ∀ i, i < n → (¬ v.neg (input i) ↔ x i = true))
    (haux : ∀ k j, k < t → j < n - t →
      (¬ v.neg (aux k j) ↔ y x k j))
    (ht : 0 < t) (htn : t ≤ n)
    (hcount : prefixCount x n ≤ t) :
    SeqCounterCNF v input aux n t := by
  simpa [SeqCounterCNF] using
    (seq_counter_satisfies input aux hinput haux ht htn hcount)

/-! Exact DIMACS numbering used by PySAT's `EncType.seqcounter` in the q=9
    branch certificates.  The first two columns are allocated interleaved;
    later columns use the contiguous `t*j+k` block.  `start` is the largest
    variable already present before the counter is appended. -/

def seqAuxOffset (t k j : Nat) : Nat :=
  if j < 2 then 2 * k + j else t * j + k

def seqAuxId (start t k j : Nat) : Nat :=
  start + 1 + seqAuxOffset t k j

/- The CNF parser stores DIMACS variable `d` as Lean variable `d-1`.
   This helper is therefore the literal-level version of `seqAuxId`. -/
def seqAuxLiteral (start t k j : Nat) : SatLiteral :=
  .pos ((seqAuxId start t k j).pred)

def q9R4AtLeastStart : Nat := 649
def q9R4AtMostStart : Nat := 777
def q9R5AtLeastStart : Nat := 649
def q9R5AtMostStart : Nat := 804

example : seqAuxId q9R4AtLeastStart 32 0 0 = 650 := by decide
example : seqAuxId q9R4AtLeastStart 32 1 0 = 652 := by decide
example : seqAuxId q9R4AtLeastStart 32 0 2 = 714 := by decide
example : seqAuxId q9R4AtMostStart 4 0 0 = 778 := by decide
example : seqAuxId q9R5AtLeastStart 31 0 0 = 650 := by decide
example : seqAuxId q9R5AtMostStart 5 0 0 = 805 := by decide

example : seqAuxLiteral 73 64 0 0 = .pos 73 := by rfl
example : seqAuxLiteral q9R4AtLeastStart 32 0 0 = .pos 649 := by rfl
example : seqAuxLiteral q9R4AtMostStart 4 0 0 = .pos 777 := by rfl

end Erdos811Q9SeqCounter
