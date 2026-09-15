import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.PNat.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Canonical natural-language definitions for Erdős 811

Shared by the statement catalogue and the corrected proof endpoint.
The historical proof core retains its floor(n/m) convention in its separate
namespace; Erdos811NaturalBridge proves the required conversion, not an axiom.
The threshold is defined only for positive host orders and graphs with edges.
-/

open Classical

namespace Erdos811

/-- A complete edge-colouring; diagonal values are dummy values, never edges. -/
structure CompleteEdgeColoring (V C : Type*) where
  color : V → V → C
  color_symm : ∀ v w, color v w = color w v

/-- Count the actual edges of colour c incident with v; exclude the diagonal. -/
def CompleteEdgeColoring.colorDegree {V C : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq C] (κ : CompleteEdgeColoring V C) (v : V) (c : C) : ℕ :=
  ((Finset.univ.erase v).filter fun w => κ.color v w = c).card

/-- Every colour has degree (|V|-1)/|C| at every vertex. -/
def CompleteEdgeColoring.IsBalanced {V C : Type*} [Fintype V] [DecidableEq V]
    [Fintype C] [DecidableEq C] (κ : CompleteEdgeColoring V C) : Prop :=
  ∀ v c, κ.colorDegree v c = (Fintype.card V - 1) / Fintype.card C

/-- All palette colours occur on real edges, not merely on the diagonal. -/
def CompleteEdgeColoring.UsesEveryColor {V C : Type*}
    (κ : CompleteEdgeColoring V C) : Prop :=
  ∀ c, ∃ v w, v ≠ w ∧ κ.color v w = c

/-- An ordinary, not necessarily induced, rainbow copy of G. -/
def HasRainbowCopy {α V C : Type*} (G : SimpleGraph α)
    (κ : CompleteEdgeColoring V C) : Prop :=
  ∃ f : α ↪ V, ∀ ⦃a b c d : α⦄,
    G.Adj a b → G.Adj c d → ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) →
      κ.color (f a) (f b) ≠ κ.color (f c) (f d)

/-- Number of unordered edges of a finite graph. -/
noncomputable def edgeCount {α : Type*} [Fintype α] (G : SimpleGraph α) : ℕ :=
  Nat.card G.edgeSet

/-- Paper convention: positive order, positive number of edges, and every
palette colour used. The infimum of an empty admissible set is infinity. -/
noncomputable def rainbowThreshold {α : Type*} [Fintype α]
    (G : SimpleGraph α) (_hG : 0 < edgeCount G) (n : ℕ+) : ℕ∞ :=
  sInf ((fun d : ℕ => (d : ℕ∞)) ''
    {d : ℕ | d ≤ ((n : ℕ) - 1) / edgeCount G ∧
      ∀ κ : CompleteEdgeColoring (Fin (n : ℕ)) (Fin (edgeCount G)),
        κ.UsesEveryColor →
        (∀ v c, d ≤ κ.colorDegree v c) → HasRainbowCopy G κ})

end Erdos811
