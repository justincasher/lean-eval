import ChallengeDeps

open LeanEval.Combinatorics

variable {G : Type*} [Group G] (S : Set G)

theorem mulCayley_connected_iff_closure_eq_top (S' : Set G) :
    (SimpleGraph.mulCayley S').Connected ↔ Subgroup.closure S' = ⊤ := by
  sorry
