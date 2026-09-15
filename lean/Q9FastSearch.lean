import CyclicBases

/-! A contest-style benchmark for the q=9 finite search.

This is deliberately separated from the theorem bridge: `used` is a Nat bitset
for the 36 colours, while `chosen` remains a short list (at most eight
vertices).  It measures whether a compact deterministic kernel search is a
practical alternative to the 205 MB LRAT elaboration.
-/

namespace Erdos811

def q9EdgeColorFast (i j : Nat) : Nat :=
  if i = 72 then j % 36
  else if j = 72 then i % 36
  else ((i + j + 1) / 2) % 36

def q9AddMask : List Nat → Nat → Option Nat
  | [], mask => some mask
  | c :: cs, mask =>
      let bit := Nat.shiftLeft 1 c
      if Nat.land mask bit != 0 then none
      else q9AddMask cs (Nat.lor mask bit)

def q9AddFreshFast (v : Nat) (chosen : List Nat) (used : Nat) : Option Nat :=
  q9AddMask (chosen.map (q9EdgeColorFast v)) used

def q9SearchFast : List Nat → Nat → List Nat → Nat → List Nat → Bool
  | _, 0, _, _, _ => true
  | [], _ + 1, _, _, _ => false
  | v :: rest, depth + 1, chosen, used, usedColors =>
      let here :=
        match q9AddFreshFast v chosen used with
        | none => false
        | some used' =>
            q9SearchFast rest depth (v :: chosen) used'
              (usedColors ++ chosen.map (q9EdgeColorFast v))
      if here then true else q9SearchFast rest (depth + 1) chosen used usedColors

/- The cyclic colouring has a translation symmetry on the 72 finite
vertices.  For the benchmark we start with vertex 0; the formal symmetry
reduction belongs in the theorem bridge below this computational kernel. -/
def q9SearchFastResult : Bool := q9SearchFast (List.range' 1 72) 8 [0] 0 []

lemma q9FastSearch_nat_land_one_shiftLeft_eq_zero_of_testBit_false {m c : Nat}
    (h : m.testBit c = false) : m.land (1 <<< c) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (m &&& (1 <<< c)).testBit i = (0 : Nat).testBit i
  rw [Nat.testBit_land, Nat.testBit_shiftLeft]
  by_cases hic : i < c
  · simp [hic]
  · have hge : c ≤ i := Nat.le_of_not_gt hic
    by_cases hio : i = c
    · subst i
      simp [h]
    · have hsub : 0 < i - c := Nat.sub_pos_of_lt (Nat.lt_of_le_of_ne hge (Ne.symm hio))
      simp only [Nat.testBit_eq_decide_div_mod_eq]
      have hpow : 1 < 2 ^ (i - c) := by
        exact Nat.one_lt_two_pow hsub.ne'
      have hdiv : 1 / 2 ^ (i - c) = 0 := Nat.div_eq_of_lt hpow
      simp [hge, hdiv]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem q9SearchFastResult_false : q9SearchFastResult = false := by
  native_decide

#print axioms q9SearchFastResult_false

end Erdos811
