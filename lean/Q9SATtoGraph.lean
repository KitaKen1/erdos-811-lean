import Q9NoInfR4CNF
import Q9NoInfR5CNF

/-! The small semantic interface between a graph-derived valuation and an
LRAT refutation.  The large proof-producing LRAT targets are intentionally
not imported here: once a branch valuation satisfies every clause, any
`Sat.Fmla.proof` of the empty clause yields `False` immediately.
-/

namespace Erdos811Q9SATtoGraph

open Mathlib.Tactic.Sat

/-
The LRAT bridge does not need a definitional equality between two huge list
parenthesizations.  The following small algebra of `subsumes` proofs lets a
partition certificate be assembled block by block.  In particular, each
finite slice can be audited independently and then composed with
`subsumes_append`.
-/
lemma subsumes_trans {f g h : Sat.Fmla}
    (hfg : f.subsumes g) (hgh : g.subsumes h) : f.subsumes h := by
  exact ⟨fun c hc => hfg.prop c (hgh.prop c hc)⟩

lemma subsumes_append {f a b : Sat.Fmla}
    (ha : f.subsumes a) (hb : f.subsumes b) : f.subsumes (a ++ b) := by
  refine ⟨fun c hc => ?_⟩
  rcases List.mem_append.mp hc with hca | hcb
  · exact ha.prop c hca
  · exact hb.prop c hcb

lemma subsumes_append_left {f a b : Sat.Fmla}
    (h : f.subsumes (a ++ b)) : f.subsumes a := by
  exact Sat.Fmla.subsumes_left f a b h

lemma subsumes_append_right {f a b : Sat.Fmla}
    (h : f.subsumes (a ++ b)) : f.subsumes b := by
  exact Sat.Fmla.subsumes_right f a b h

lemma fmlaAppend_subsumes_append {a b c d : Sat.Fmla}
    (ha : a.subsumes c) (hb : b.subsumes d) :
    (fmlaAppend a b).subsumes (c ++ d) := by
  refine ⟨fun x hx => ?_⟩
  rcases List.mem_append.mp hx with hxc | hxd
  · exact fmlaAppend_mem.mpr (Or.inl (ha.prop x hxc))
  · exact fmlaAppend_mem.mpr (Or.inr (hb.prop x hxd))

/- Lift a component inclusion through an append without changing the target
   parenthesization.  These two small lemmas are the bridge used when a
   collision-tree certificate is inserted into the five-block semantic
   context. -/
lemma fmlaAppend_subsumes_left_component {a b c : Sat.Fmla}
    (h : a.subsumes c) : (fmlaAppend a b).subsumes c := by
  exact ⟨fun x hx => fmlaAppend_mem.mpr (Or.inl (h.prop x hx))⟩

lemma fmlaAppend_subsumes_right_component {a b c : Sat.Fmla}
    (h : b.subsumes c) : (fmlaAppend a b).subsumes c := by
  exact ⟨fun x hx => fmlaAppend_mem.mpr (Or.inr (h.prop x hx))⟩

lemma false_of_fmla_proof {f : Sat.Fmla}
    (hproof : f.proof []) {v : Sat.Valuation}
    (hsat : ∀ c ∈ f, v.satisfies c) : False := by
  have hsf : v.satisfies_fmla f := ⟨hsat⟩
  exact hproof v hsf

lemma false_of_proof_of_context_eq {f g : Sat.Fmla}
    (hctx : f = g) (hproof : g.proof []) {v : Sat.Valuation}
    (hsat : ∀ c ∈ f, v.satisfies c) : False := by
  subst g
  exact false_of_fmla_proof hproof hsat

lemma false_of_proof_of_subsumes {ctx full : Sat.Fmla}
    (hsub : ctx.subsumes full) (hproof : full.proof []) {v : Sat.Valuation}
    (hsat : ∀ c ∈ ctx, v.satisfies c) : False := by
  have hfull : v.satisfies_fmla full := ⟨fun c hc => hsat c (hsub.prop c hc)⟩
  exact hproof v hfull

lemma q9_r4_false_of_unsat
    (hproof : Erdos811Q9NoInfR4CNF.q9_noinf_r4_ctx.proof [])
    {v : Sat.Valuation}
    (hsat : ∀ c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_ctx,
      v.satisfies c) : False := by
  exact false_of_fmla_proof hproof hsat

lemma q9_r5_false_of_unsat
    (hproof : Erdos811Q9NoInfR5CNF.q9_noinf_r5_ctx.proof [])
    {v : Sat.Valuation}
    (hsat : ∀ c ∈ Erdos811Q9NoInfR5CNF.q9_noinf_r5_ctx,
      v.satisfies c) : False := by
  exact false_of_fmla_proof hproof hsat

end Erdos811Q9SATtoGraph

#print axioms Erdos811Q9SATtoGraph.q9_r4_false_of_unsat
#print axioms Erdos811Q9SATtoGraph.q9_r5_false_of_unsat
#print axioms Erdos811Q9SATtoGraph.false_of_proof_of_context_eq
#print axioms Erdos811Q9SATtoGraph.subsumes_trans
#print axioms Erdos811Q9SATtoGraph.subsumes_append
#print axioms Erdos811Q9SATtoGraph.fmlaAppend_subsumes_append
#print axioms Erdos811Q9SATtoGraph.fmlaAppend_subsumes_left_component
#print axioms Erdos811Q9SATtoGraph.fmlaAppend_subsumes_right_component
#print axioms Erdos811Q9SATtoGraph.false_of_proof_of_subsumes
