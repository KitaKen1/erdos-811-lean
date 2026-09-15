import Q9FastProof

/-! Bridge from a hypothetical 0-containing q=9 edge-distinct set to the
computed competitive-programming search certificate. -/

namespace Erdos811

lemma q9_no_sublist_edgeDistinct_zero :
    ¬ ∃ xs : List Nat, xs.length = 8 ∧
      xs.Sublist (List.range' 1 72) ∧
      (xs ++ [0]).Nodup ∧ q9EdgeDistinct (xs ++ [0]) := by
  rintro ⟨xs, hlen, hsub, hnodup, hdist⟩
  have hgood : q9GoodPathFast xs [0] 0 [] := by
    have hpath := q9GoodPathFast_of_distinct xs [0] [] hnodup hdist
      (by simp) (by simp [q9UsedSound])
    simpa [q9Mask] using hpath
  have hcan : q9CanSearchFast (List.range' 1 72) 8 [0] 0 [] := by
    apply q9CanSearchFast_of_sublist hsub
    · exact hlen.symm
    · exact hgood
  have hsearch : q9SearchFast (List.range' 1 72) 8 [0] 0 [] = true :=
    (q9SearchFast_iff_canSearchFast (List.range' 1 72) 8 [0] 0 []).2 hcan
  have hfalse : q9SearchFast (List.range' 1 72) 8 [0] 0 [] = false :=
    q9SearchFastResult_false
  simp [hsearch] at hfalse

end Erdos811
