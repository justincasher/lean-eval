import ChallengeDeps

open LeanEval

variable {n : Type*} [Fintype n] {A : Matrix n n ℝ}

theorem posSemidef_map_exp (hA : A.PosSemidef) :
    (A.map Real.exp).PosSemidef := by
  sorry
