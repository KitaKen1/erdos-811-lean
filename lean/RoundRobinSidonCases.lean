import RoundRobinSidon

/-!
# Search-free round-robin cases

The numerical instances below use only the general weak-Sidon theorem and
small kernel computations.  In particular, they do not depend on the old
`native_decide` clique-search certificates.
-/

namespace Erdos811

private theorem two_nsmul_injective_zmod15 :
    Function.Injective fun x : ZMod 15 => 2 • x := by
  decide

private theorem two_nsmul_injective_zmod21 :
    Function.Injective fun x : ZMod 21 => 2 • x := by
  decide

private theorem two_nsmul_injective_zmod45 :
    Function.Injective fun x : ZMod 45 => 2 • x := by
  decide

private theorem two_nsmul_injective_zmod55 :
    Function.Injective fun x : ZMod 55 => 2 • x := by
  decide

theorem q6_no_rainbow_sidon :
    ¬ HasRainbowCopy (SimpleGraph.completeGraph (Fin 6))
      q6RoundRobinColoring := by
  rintro ⟨f, hf⟩
  apply no_roundRobin_rainbow_embedding_of_sidon_bounds
      (q := 6) (m := 15) (by norm_num)
      two_nsmul_injective_zmod15 (by norm_num) (by norm_num) f
  intro a b c d hab hcd hedges
  apply hf
  · simpa using hab
  · simpa using hcd
  · exact hedges

theorem q7_no_rainbow_sidon :
    ¬ HasRainbowCopy (SimpleGraph.completeGraph (Fin 7))
      q7RoundRobinColoring := by
  rintro ⟨f, hf⟩
  apply no_roundRobin_rainbow_embedding_of_sidon_bounds
      (q := 7) (m := 21) (by norm_num)
      two_nsmul_injective_zmod21 (by norm_num) (by norm_num) f
  intro a b c d hab hcd hedges
  apply hf
  · simpa using hab
  · simpa using hcd
  · exact hedges

theorem q10_no_rainbow_sidon :
    ¬ HasRainbowCopy (SimpleGraph.completeGraph (Fin 10))
      q10RoundRobinColoring := by
  rintro ⟨f, hf⟩
  apply no_roundRobin_rainbow_embedding_of_sidon_bounds
      (q := 10) (m := 45) (by norm_num)
      two_nsmul_injective_zmod45 (by norm_num) (by norm_num) f
  intro a b c d hab hcd hedges
  apply hf
  · simpa using hab
  · simpa using hcd
  · exact hedges

theorem q11_no_rainbow_sidon :
    ¬ HasRainbowCopy (SimpleGraph.completeGraph (Fin 11))
      q11RoundRobinColoring := by
  rintro ⟨f, hf⟩
  apply no_roundRobin_rainbow_embedding_of_sidon_bounds
      (q := 11) (m := 55) (by norm_num)
      two_nsmul_injective_zmod55 (by norm_num) (by norm_num) f
  intro a b c d hab hcd hedges
  apply hf
  · simpa using hab
  · simpa using hcd
  · exact hedges

#print axioms q6_no_rainbow_sidon
#print axioms q7_no_rainbow_sidon
#print axioms q10_no_rainbow_sidon
#print axioms q11_no_rainbow_sidon

end Erdos811
