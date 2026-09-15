import Q8PaperNormalized

/-! A small residue-profile classifier, with a generic completeness proof.
Lists of chosen residues are stored in descending order; repeated residues
are allowed. Search prunes only when a colour count already exceeds four. -/

namespace Erdos811

def q8ResidueEdgeColors : List Nat → List Nat
  | [] => []
  | v :: vs => (v % 7 :: vs.map (fun w => ((v + w + 1) / 2) % 7)) ++
      q8ResidueEdgeColors vs

def q8ResidueQuota (xs : List Nat) : Bool :=
  (List.range 7).all (fun c => decide ((q8ResidueEdgeColors xs).count c ≤ 4))

def q8ResidueOddOK (xs : List Nat) : Bool :=
  decide ((xs.map (fun v => v % 2)).sum = 3 ∨ (xs.map (fun v => v % 2)).sum = 4)

/-- The 14 translated supports, already sorted in descending order.
Storing this tiny table avoids reducing well-founded merge-sort in the certificate. -/
def q8ResidueTypes : List (List Nat) :=
  [[13,12,11,9,7,4,2],
    [13,12,10,8,5,3,0],
    [13,11,9,6,4,1,0],
    [12,10,7,5,2,1,0],
    [13,11,8,6,3,2,1],
    [12,9,7,4,3,2,0],
    [13,10,8,5,4,3,1],
    [11,9,6,5,4,2,0],
    [12,10,7,6,5,3,1],
    [13,11,8,7,6,4,2],
    [12,9,8,7,5,3,0],
    [13,10,9,8,6,4,1],
    [11,10,9,7,5,2,0],
    [12,11,10,8,6,3,1]]

lemma q8ResidueTypes_translates (xs : List Nat) (hx : xs ∈ q8ResidueTypes) :
    ∃ s : Fin 14, xs.Perm ([2,4,7,9,11,12,13].map (fun v => (v + s.val) % 14)) := by
  have h : q8ResidueTypes.Forall (fun ys =>
      ∃ s : Fin 14, ys.Perm ([2,4,7,9,11,12,13].map (fun v => (v + s.val) % 14))) := by
    decide
  exact (List.forall_iff_forall_mem.mp h) xs hx

def q8ResidueContinuation : Nat → List Nat → Prop
  | _, [] => True
  | lo, v :: vs => lo ≤ v ∧ v < 14 ∧ q8ResidueContinuation v vs

def q8ResidueCheck : Nat → Nat → List Nat → Bool
  | 0, _, chosen => if q8ResidueOddOK chosen then decide (chosen ∈ q8ResidueTypes) else true
  | n + 1, lo, chosen => (List.range 14).all (fun v =>
      if lo ≤ v then
        if q8ResidueQuota (v :: chosen) then q8ResidueCheck n v (v :: chosen) else true
      else true)

lemma q8ResidueColors_count_suffix (ys xs : List Nat) (c : Nat) :
    (q8ResidueEdgeColors xs).count c ≤ (q8ResidueEdgeColors (ys ++ xs)).count c := by
  induction ys with
  | nil => rfl
  | cons v ys ih =>
    simp only [List.cons_append, q8ResidueEdgeColors, List.count_cons, List.count_append]
    omega

lemma q8ResidueQuota_suffix (ys xs : List Nat)
    (h : q8ResidueQuota (ys ++ xs) = true) : q8ResidueQuota xs = true := by
  simp only [q8ResidueQuota, List.all_eq_true, decide_eq_true_eq] at h ⊢
  intro c hc
  exact (q8ResidueColors_count_suffix ys xs c).trans (h c hc)

/-- A passing search covers every sorted bounded continuation with valid
quotas and odd count. In particular, pruning cannot discard such a continuation. -/
theorem q8ResidueCheck_sound (tail : List Nat) (lo : Nat) (chosen : List Nat)
    (hvalid : q8ResidueContinuation lo tail)
    (hcheck : q8ResidueCheck tail.length lo chosen = true)
    (hquota : q8ResidueQuota (tail.reverse ++ chosen) = true)
    (hodd : q8ResidueOddOK (tail.reverse ++ chosen) = true) :
    tail.reverse ++ chosen ∈ q8ResidueTypes := by
  induction tail generalizing lo chosen with
  | nil =>
    change q8ResidueOddOK chosen = true at hodd
    simpa [q8ResidueCheck, hodd] using hcheck
  | cons v tail ih =>
    obtain ⟨hlow, hv, hrest⟩ := hvalid
    have hquota' : q8ResidueQuota (tail.reverse ++ (v :: chosen)) = true := by
      simpa using hquota
    have hodd' : q8ResidueOddOK (tail.reverse ++ (v :: chosen)) = true := by
      simpa using hodd
    have hprefix := q8ResidueQuota_suffix tail.reverse (v :: chosen) hquota'
    have hstep := (List.all_eq_true.mp hcheck) v (List.mem_range.mpr hv)
    have hcheck' : q8ResidueCheck tail.length v (v :: chosen) = true := by
      simpa [hlow, hprefix] using hstep
    simpa using ih v (v :: chosen) hrest hcheck' hquota' hodd'

#print axioms q8ResidueCheck_sound

end Erdos811
