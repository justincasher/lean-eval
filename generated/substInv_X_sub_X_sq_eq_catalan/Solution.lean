import ChallengeDeps
import Submission

open LeanEval.Combinatorics
open PowerSeries

theorem substInv_X_sub_X_sq_eq_catalan (n : ℕ) :
    coeff (n + 1) (substInv ((X : ℚ⟦X⟧) - X ^ 2)) =
      (Nat.choose (2 * n) n : ℚ) / (↑n + 1) := by
  exact Submission.substInv_X_sub_X_sq_eq_catalan n
