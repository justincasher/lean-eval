import ChallengeDeps
import Submission.Helpers

open LeanEval

variable {n : Type*} [Fintype n] {A : Matrix n n ℝ}

namespace Submission

theorem posSemidef_map_exp (hA : A.PosSemidef) :
    (A.map Real.exp).PosSemidef := by
  sorry

end Submission
