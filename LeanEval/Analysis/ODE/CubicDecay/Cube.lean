import Mathlib
import EvalTools.Markers

/-!
Derivative and local Lipschitz estimates for the vector field `z ↦ -z³`. Helper file for
`LeanEval.Analysis.ODE.CubicDecay`.
-/

namespace LeanEval
namespace Analysis
namespace ODE

open scoped NNReal

/-- Derivative of the negated cube (`lem:cube-deriv`): `deriv (z ↦ -z³) z = -3z²`. -/
theorem deriv_neg_cube (z : ℝ) : deriv (fun z : ℝ => -(z ^ 3)) z = -3 * z ^ 2 := by
  sorry

/-- Derivative bound for the cube (`lem:cube-deriv-bound`): for `M ≥ 0` and `z ∈ [-M, M]`,
the derivative of `z ↦ -z³` has nonnegative norm at most `3M²`. -/
theorem nnnorm_deriv_neg_cube_le (M : ℝ) (hM : 0 ≤ M) (z : ℝ) (hz : z ∈ Set.Icc (-M) M) :
    ‖deriv (fun z : ℝ => -(z ^ 3)) z‖₊ ≤ 3 * M.toNNReal ^ 2 := by
  sorry

/-- Local Lipschitz bound for the cube (`lem:cube-lipschitz`): for `M ≥ 0`, the map
`z ↦ -z³` is `3M²`-Lipschitz on `[-M, M]`. -/
theorem cube_lipschitzOnWith (M : ℝ) (hM : 0 ≤ M) :
    LipschitzOnWith (3 * M.toNNReal ^ 2) (fun z : ℝ => -(z ^ 3)) (Set.Icc (-M) M) := by
  sorry

end ODE
end Analysis
end LeanEval
