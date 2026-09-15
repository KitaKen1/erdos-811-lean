import Erdos811Definitions

/-!
# Cyclic finite bases for q = 8 and q = 9

The source report gives the colouring on `Z_(2m) ∪ {∞}` by
`ceil((x+y)/2) mod m` and `c(∞,x)=x mod m`.  These declarations make the
finite objects explicit in the shared FC-like definitions.  The balance
checks below are kernel reductions; the rainbow-free checks still need a
compressed finite certificate rather than an unbounded `decide` call.
-/

namespace Erdos811

def q8Coloring : CompleteEdgeColoring (Fin 57) (Fin 28) where
  color p q :=
    if p.val = 56 then
      ⟨q.val % 28, by omega⟩
    else if q.val = 56 then
      ⟨p.val % 28, by omega⟩
    else
      ⟨((p.val + q.val + 1) / 2) % 28, by omega⟩
  color_symm p q := by
    by_cases hp : p.val = 56
    · by_cases hq : q.val = 56
      · simp [hp, hq]
      · simp [hp, hq]
    · by_cases hq : q.val = 56
      · simp [hp, hq]
      · simp [hp, hq, Nat.add_comm]

def q9Coloring : CompleteEdgeColoring (Fin 73) (Fin 36) where
  color p q :=
    if p.val = 72 then
      ⟨q.val % 36, by omega⟩
    else if q.val = 72 then
      ⟨p.val % 36, by omega⟩
    else
      ⟨((p.val + q.val + 1) / 2) % 36, by omega⟩
  color_symm p q := by
    by_cases hp : p.val = 72
    · by_cases hq : q.val = 72
      · simp [hp, hq]
      · simp [hp, hq]
    · by_cases hq : q.val = 72
      · simp [hp, hq]
      · simp [hp, hq, Nat.add_comm]

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem q8_balanced : q8Coloring.IsBalanced := by
  change ∀ v : Fin 57, ∀ c : Fin 28,
    q8Coloring.colorDegree v c = Fintype.card (Fin 57) / Fintype.card (Fin 28)
  letI : DecidablePred (fun v : Fin 57 => ∀ c : Fin 28,
      q8Coloring.colorDegree v c = Fintype.card (Fin 57) / Fintype.card (Fin 28)) :=
    fun v => Fintype.decidableForallFintype
  letI : Decidable (∀ v : Fin 57, ∀ c : Fin 28,
      q8Coloring.colorDegree v c = Fintype.card (Fin 57) / Fintype.card (Fin 28)) :=
    Fintype.decidableForallFintype
  decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem q9_balanced : q9Coloring.IsBalanced := by
  change ∀ v : Fin 73, ∀ c : Fin 36,
    q9Coloring.colorDegree v c = Fintype.card (Fin 73) / Fintype.card (Fin 36)
  letI : DecidablePred (fun v : Fin 73 => ∀ c : Fin 36,
      q9Coloring.colorDegree v c = Fintype.card (Fin 73) / Fintype.card (Fin 36)) :=
    fun v => Fintype.decidableForallFintype
  letI : Decidable (∀ v : Fin 73, ∀ c : Fin 36,
      q9Coloring.colorDegree v c = Fintype.card (Fin 73) / Fintype.card (Fin 36)) :=
    Fintype.decidableForallFintype
  decide

#print axioms q8_balanced
#print axioms q9_balanced

end Erdos811
