import Q9FastSearch
import Q9BitsetLemmas

/-! Proof-facing correctness lemmas for the competitive-programming-style
bitset search used for the `q = 9` cyclic base. -/

namespace Erdos811

/-! The proof-facing companion to the bitset search.

The search carries a ghost list of used colours.  It is not used by the
evaluator, but makes the invariant connecting the bit mask to edge colours
explicit and easy to audit.
-/

def q9AllEdgeColors : List Nat → List Nat
  | [] => []
  | v :: vs => vs.map (q9EdgeColorFast v) ++ q9AllEdgeColors vs

def q9EdgeDistinct (xs : List Nat) : Prop :=
  ∀ ⦃a b c d : Nat⦄, a ∈ xs → b ∈ xs → c ∈ xs → d ∈ xs →
    a ≠ b → c ≠ d → ¬ SameUndirectedEdge a b c d →
      q9EdgeColorFast a b ≠ q9EdgeColorFast c d

def q9CanSearchFast (xs : List Nat) (depth : Nat)
    (chosen : List Nat) (used : Nat) (usedColors : List Nat) : Prop :=
  match depth, xs with
  | 0, _ => True
  | _ + 1, [] => False
  | d + 1, v :: rest =>
      (∃ used', q9AddFreshFast v chosen used = some used' ∧
        q9CanSearchFast rest d (v :: chosen) used'
          (usedColors ++ chosen.map (q9EdgeColorFast v))) ∨
      q9CanSearchFast rest (d + 1) chosen used usedColors

lemma q9SearchFast_iff_canSearchFast :
    ∀ (xs : List Nat) (depth : Nat) (chosen : List Nat) (used : Nat)
      (usedColors : List Nat),
      q9SearchFast xs depth chosen used usedColors = true ↔
        q9CanSearchFast xs depth chosen used usedColors := by
  intro xs
  induction xs with
  | nil =>
      intro depth chosen used usedColors
      cases depth <;> simp [q9SearchFast, q9CanSearchFast]
  | cons v rest ih =>
      intro depth chosen used usedColors
      cases depth with
      | zero => simp [q9SearchFast, q9CanSearchFast]
      | succ d =>
          by_cases hfresh : q9AddFreshFast v chosen used = none
          · simp [q9SearchFast, q9CanSearchFast, hfresh, ih]
          · obtain ⟨used', hused'⟩ :
                ∃ used', q9AddFreshFast v chosen used = some used' := by
              simpa only [Option.ne_none_iff_exists, eq_comm] using hfresh
            simp [q9SearchFast, q9CanSearchFast, hused', ih]

def q9Mask : List Nat → Nat :=
  List.foldr (fun c mask => Nat.lor mask (1 <<< c)) 0

lemma q9Mask_append (xs ys : List Nat) :
    q9Mask (xs ++ ys) = Nat.lor (q9Mask xs) (q9Mask ys) := by
  induction xs with
  | nil => simp [q9Mask]
  | cons c cs ih =>
      simp only [List.cons_append]
      change Nat.lor (q9Mask (cs ++ ys)) (1 <<< c) =
        Nat.lor (Nat.lor (q9Mask cs) (1 <<< c)) (q9Mask ys)
      rw [ih]
      simp [Nat.lor_assoc, Nat.lor_comm]

lemma q9Mask_no_bit_of_not_mem {xs : List Nat} {c : Nat}
    (hc : c ∉ xs) : (q9Mask xs).land (1 <<< c) = 0 := by
  induction xs with
  | nil => simp [q9Mask]
  | cons d ds ih =>
      have hdc : d ≠ c := by
        intro h
        apply hc
        simp [h]
      have hrest : c ∉ ds := by
        intro h
        apply hc
        simp [h]
      simp only [q9Mask, List.foldr]
      apply nat_land_lor_shiftLeft_eq_zero
      · exact ih hrest
      · exact hdc

lemma q9AddMask_eq_mask_append {cs usedColors : List Nat}
    (hcs : cs.Nodup) (hdisj : ∀ c ∈ cs, c ∉ usedColors) :
    ∃ used', q9AddMask cs (q9Mask usedColors) = some used' ∧
      used' = q9Mask (usedColors ++ cs) := by
  induction cs generalizing usedColors with
  | nil =>
      simp [q9AddMask]
  | cons c cs ih =>
      have hcnot : c ∉ usedColors := hdisj c (by simp)
      have hbit : (q9Mask usedColors).land (1 <<< c) = 0 :=
        q9Mask_no_bit_of_not_mem hcnot
      have hrestnodup : cs.Nodup := hcs.of_cons
      have hrestdisj : ∀ d ∈ cs, d ∉ (usedColors ++ [c]) := by
        intro d hd hmem
        rcases List.mem_append.mp hmem with hmem | hmem
        · exact hdisj d (by simp [hd]) hmem
        · have hdc : d = c := by simpa using hmem
          apply (List.nodup_cons.mp hcs).1
          simpa [hdc] using hd
      obtain ⟨used', hused', hmask'⟩ :=
        ih (usedColors := usedColors ++ [c]) hrestnodup hrestdisj
      have hstart : q9Mask (usedColors ++ [c]) =
          Nat.lor (q9Mask usedColors) (1 <<< c) := by
        rw [q9Mask_append]
        simp [q9Mask]
      rw [hstart] at hused'
      refine ⟨used', ?_, ?_⟩
      · have hzero : q9Mask usedColors &&& (1 <<< c) = 0 := hbit
        change (if ((q9Mask usedColors &&& (1 <<< c)) != 0) = true then none
          else q9AddMask cs (Nat.lor (q9Mask usedColors) (1 <<< c))) = some used'
        simp [hzero]
        exact hused'
      · simpa [List.append_assoc] using hmask'

def q9GoodPathFast : List Nat → List Nat → Nat → List Nat → Prop
  | [], _, _, _ => True
  | v :: vs, chosen, used, usedColors =>
      ∃ used', q9AddFreshFast v chosen used = some used' ∧
        q9GoodPathFast vs (v :: chosen) used'
          (usedColors ++ chosen.map (q9EdgeColorFast v))

def q9UsedSound (chosen usedColors : List Nat) : Prop :=
  ∀ {c : Nat}, c ∈ usedColors →
    ∃ a ∈ chosen, ∃ b ∈ chosen, a ≠ b ∧ q9EdgeColorFast a b = c

lemma q9Colors_nodup {v : Nat} {chosen : List Nat}
    (hnodup : (v :: chosen).Nodup) (hdist : q9EdgeDistinct (v :: chosen)) :
    (chosen.map (q9EdgeColorFast v)).Nodup := by
  apply (List.nodup_iff_pairwise_ne).2
  apply List.pairwise_map.mpr
  apply (List.nodup_cons.mp hnodup).2.imp_of_mem
  intro a b ha hb hab
  apply hdist
  · simp
  · simp [ha]
  · simp
  · simp [hb]
  · intro hva
    subst a
    exact (List.nodup_cons.mp hnodup).1 (by simp [ha])
  · intro hvb
    subst b
    exact (List.nodup_cons.mp hnodup).1 (by simp [hb])
  · intro hsame
    rcases hsame with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hab h2
    · exact (List.nodup_cons.mp hnodup).1 (by simpa [h1] using hb)

lemma q9UsedSound_append {v : Nat} {chosen usedColors : List Nat}
    (hsound : q9UsedSound chosen usedColors)
    (hnew : ∀ c ∈ chosen.map (q9EdgeColorFast v),
      ∃ b ∈ chosen, b ≠ v ∧ q9EdgeColorFast v b = c) :
    q9UsedSound (v :: chosen)
      (usedColors ++ chosen.map (q9EdgeColorFast v)) := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨a, ha, b, hb, hab, heq⟩ := hsound hc
    exact ⟨a, by simp [ha], b, by simp [hb], hab, heq⟩
  · obtain ⟨b, hb, hbv, heq⟩ := hnew c hc
    exact ⟨v, by simp, b, by simp [hb], Ne.symm hbv, heq⟩

lemma q9Colors_disjoint_of_usedSound {v : Nat} {chosen usedColors : List Nat}
    (hnodup : (v :: chosen).Nodup) (hdist : q9EdgeDistinct (v :: chosen))
    (hsound : q9UsedSound chosen usedColors) :
    ∀ c ∈ chosen.map (q9EdgeColorFast v), c ∉ usedColors := by
  intro c hc hmem
  obtain ⟨b, hb, hcb⟩ := by
    simpa only [List.mem_map] using hc
  have hbv : b ≠ v := by
    intro h
    subst b
    exact (List.nodup_cons.mp hnodup).1 hb
  obtain ⟨a, ha, d, hd, had, hcd⟩ := hsound hmem
  have hne : q9EdgeColorFast v b ≠ q9EdgeColorFast a d := by
    apply hdist
    · simp
    · simp [hb]
    · simp [ha]
    · simp [hd]
    · exact Ne.symm hbv
    · exact had
    · intro hsame
      rcases hsame with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact (List.nodup_cons.mp hnodup).1 (by simpa [h1] using ha)
      · exact (List.nodup_cons.mp hnodup).1 (by simpa [h1] using hd)
  exact hne (hcb.trans hcd.symm)

lemma q9GoodPathFast_of_distinct :
    ∀ (xs chosen usedColors : List Nat),
      (xs ++ chosen).Nodup → q9EdgeDistinct (xs ++ chosen) →
      usedColors.Nodup → q9UsedSound chosen usedColors →
      q9GoodPathFast xs chosen (q9Mask usedColors) usedColors := by
  intro xs
  induction xs with
  | nil =>
      intro chosen usedColors hnodup hdist husednodup hsound
      simp [q9GoodPathFast]
  | cons v vs ih =>
      intro chosen usedColors hnodup hdist husednodup hsound
      have htail : (vs ++ chosen).Nodup := hnodup.of_cons
      have hmem : ∀ z, z ∈ v :: chosen → z ∈ (v :: vs) ++ chosen := by
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · simp
        · simp [hz]
      have hvc : q9EdgeDistinct (v :: chosen) := by
        intro a b c d ha hb hc hd hab hcd hsame
        exact hdist (hmem a ha) (hmem b hb) (hmem c hc) (hmem d hd)
          hab hcd hsame
      have hcolors : (chosen.map (q9EdgeColorFast v)).Nodup :=
        q9Colors_nodup (List.nodup_cons.mpr ⟨by
          intro hv
          exact (List.nodup_cons.mp hnodup).1 (by simp [hv]),
          htail.sublist (by simp)⟩) hvc
      have hdisj : ∀ c ∈ chosen.map (q9EdgeColorFast v), c ∉ usedColors :=
        q9Colors_disjoint_of_usedSound
          (List.nodup_cons.mpr ⟨by
            intro hv
            exact (List.nodup_cons.mp hnodup).1 (by simp [hv]),
            htail.sublist (by simp)⟩) hvc hsound
      obtain ⟨used', hadd, hmask⟩ :=
        q9AddMask_eq_mask_append hcolors hdisj
      have hnew : ∀ c ∈ chosen.map (q9EdgeColorFast v),
          ∃ b ∈ chosen, b ≠ v ∧ q9EdgeColorFast v b = c := by
        intro c hc
        obtain ⟨b, hb, hcb⟩ := by
          simpa only [List.mem_map] using hc
        have hbv : b ≠ v := by
          intro h
          subst b
          exact (List.nodup_cons.mp hnodup).1 (by simp [hb])
        exact ⟨b, hb, hbv, hcb⟩
      have hsound' : q9UsedSound (v :: chosen)
          (usedColors ++ chosen.map (q9EdgeColorFast v)) :=
        q9UsedSound_append hsound hnew
      have hnodup' : (usedColors ++ chosen.map (q9EdgeColorFast v)).Nodup := by
        apply List.Nodup.append husednodup hcolors
        exact fun c hc hd => hdisj c hd hc
      have htail' : (vs ++ (v :: chosen)).Nodup := by
        have hvs : vs.Nodup := (List.nodup_append.mp htail).1
        have hchosen : chosen.Nodup := (List.nodup_append.mp htail).2.1
        have hcross : ∀ a ∈ vs, ∀ b ∈ chosen, a ≠ b :=
          (List.nodup_append.mp htail).2.2
        have hvvs : v ∉ vs := by
          intro hv
          exact (List.nodup_cons.mp hnodup).1 (by simp [hv])
        have hvchosen : v ∉ chosen := by
          intro hv
          exact (List.nodup_cons.mp hnodup).1 (by simp [hv])
        apply List.Nodup.append hvs
        · exact List.nodup_cons.mpr ⟨hvchosen, hchosen⟩
        · intro a ha hb
          rcases List.mem_cons.mp hb with rfl | hb
          · exact hvvs (by simp [ha])
          · exact (hcross a ha a hb) rfl
      have hdist' : q9EdgeDistinct (vs ++ (v :: chosen)) := by
        have hmem' : ∀ z, z ∈ vs ++ (v :: chosen) → z ∈ (v :: vs) ++ chosen := by
          intro z hz
          rcases List.mem_append.mp hz with hz | hz
          · simp [hz]
          · rcases List.mem_cons.mp hz with rfl | hz
            · simp
            · simp [hz]
        intro a b c d ha hb hc hd hab hcd hsame
        apply hdist (hmem' a ha) (hmem' b hb) (hmem' c hc) (hmem' d hd)
          hab hcd
        exact hsame
      refine ⟨used', ?_, ?_⟩
      · simpa [q9AddFreshFast] using hadd
      · rw [hmask]
        apply ih (v :: chosen) (usedColors ++ chosen.map (q9EdgeColorFast v))
          htail' hdist' hnodup' hsound'

lemma q9CanSearchFast_of_sublist :
    ∀ {cand xs : List Nat} {depth : Nat} {chosen : List Nat}
      {used : Nat} {usedColors : List Nat},
      xs.Sublist cand → depth = xs.length →
      q9GoodPathFast xs chosen used usedColors →
      q9CanSearchFast cand depth chosen used usedColors := by
  intro cand xs depth chosen used usedColors hsub
  induction hsub generalizing depth chosen used usedColors with
  | slnil =>
      intro hdepth hgood
      simp at hdepth
      subst depth
      simp [q9CanSearchFast]
  | cons a hsub ih =>
      intro hdepth hgood
      cases depth with
      | zero => simp [q9CanSearchFast]
      | succ d =>
          right
          exact ih hdepth hgood
  | cons_cons a hsub ih =>
      intro hdepth hgood
      cases depth with
      | zero => simp at hdepth
      | succ d =>
          simp only [q9CanSearchFast]
          left
          rcases hgood with ⟨used', hused', hpath⟩
          refine ⟨used', hused', ?_⟩
          apply ih
          · simpa using hdepth
          · exact hpath

end Erdos811
