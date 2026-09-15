import FormalConjecturesUtil

/-!
# Shared definitions for Erdős Problem 811

The Formal Conjectures statement and the finite certificate modules import this
file so that constructions are checked against exactly the same predicates.
-/

open Classical Filter

namespace Erdos811

structure CompleteEdgeColoring (V C : Type*) where
  color : V → V → C
  color_symm : ∀ v w, color v w = color w v

def CompleteEdgeColoring.colorDegree {V C : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq C] (κ : CompleteEdgeColoring V C) (v : V) (c : C) : ℕ :=
  ((Finset.univ.erase v).filter fun w => κ.color v w = c).card

def CompleteEdgeColoring.IsBalanced {V C : Type*} [Fintype V] [DecidableEq V]
    [Fintype C] [DecidableEq C] (κ : CompleteEdgeColoring V C) : Prop :=
  ∀ v c, κ.colorDegree v c = Fintype.card V / Fintype.card C

def SameUndirectedEdge {α : Type*} (a b c d : α) : Prop :=
  (a = c ∧ b = d) ∨ (a = d ∧ b = c)

def HasRainbowCopy {α V C : Type*} (G : SimpleGraph α)
    (κ : CompleteEdgeColoring V C) : Prop :=
  ∃ f : α ↪ V, ∀ ⦃a b c d : α⦄,
    G.Adj a b → G.Adj c d → ¬ SameUndirectedEdge a b c d →
      κ.color (f a) (f b) ≠ κ.color (f c) (f d)

noncomputable def edgeCount {α : Type*} [Fintype α] (G : SimpleGraph α) : ℕ :=
  Nat.card G.edgeSet

theorem edgeCount_completeGraph_fin (q : ℕ) :
    edgeCount (SimpleGraph.completeGraph (Fin q)) = q.choose 2 := by
  classical
  unfold edgeCount
  rw [SimpleGraph.completeGraph_eq_top]
  rw [SimpleGraph.edgeSet_top]
  change Nat.card {x : Sym2 (Fin q) // ¬ x.IsDiag} = q.choose 2
  calc
    Nat.card {x : Sym2 (Fin q) // ¬ x.IsDiag} =
        Fintype.card {x : Sym2 (Fin q) // ¬ x.IsDiag} := Nat.card_eq_fintype_card
    _ = q.choose 2 := by
      simpa using (Sym2.card_subtype_not_diag (α := Fin q))

def HasBalancedCounterexampleAt {α : Type*} [Fintype α]
    (G : SimpleGraph α) (n : ℕ) : Prop :=
  n % edgeCount G = 1 ∧
    ∃ κ : CompleteEdgeColoring (Fin n) (Fin (edgeCount G)),
      κ.IsBalanced ∧ ¬ HasRainbowCopy G κ

def HasArbitrarilyLargeBalancedCounterexamples {α : Type*} [Fintype α]
    (G : SimpleGraph α) : Prop :=
  ∀ n₀ : ℕ, ∃ n : ℕ, n₀ ≤ n ∧ HasBalancedCounterexampleAt G n

def AllCliquesHaveCounterexamples : Prop :=
  ∀ q : ℕ, 4 ≤ q →
    HasArbitrarilyLargeBalancedCounterexamples (SimpleGraph.completeGraph (Fin q))

end Erdos811
