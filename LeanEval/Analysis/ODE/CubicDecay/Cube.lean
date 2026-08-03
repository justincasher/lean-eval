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
  have h := ((hasDerivAt_pow 3 z).neg).deriv
  simp

/-- Derivative bound for the cube (`lem:cube-deriv-bound`): for `M ≥ 0` and `z ∈ [-M, M]`,
the derivative of `z ↦ -z³` has nonnegative norm at most `3M²`. -/
theorem nnnorm_deriv_neg_cube_le (M : ℝ) (hM : 0 ≤ M) (z : ℝ) (hz : z ∈ Set.Icc (-M) M) :
    ‖deriv (fun z : ℝ => -(z ^ 3)) z‖₊ ≤ 3 * M.toNNReal ^ 2 := by
  rw [deriv_neg_cube]
  apply NNReal.coe_le_coe.mp
  have hMnn : (M.toNNReal : ℝ) = M := by simpa using Real.coe_toNNReal M hM
  have hzsq_le : z ^ 2 ≤ M ^ 2 := by
    nlinarith [hz.1, hz.2, hM]
  calc
    (‖-3 * z ^ 2‖₊ : ℝ) = |-3 * z ^ 2| := by simp
    _ = 3 * z ^ 2 := by
      calc
        |-3 * z ^ 2| = |(-3 : ℝ)| * |z ^ 2| := by rw [abs_mul]
        _ = 3 * |z ^ 2| := by norm_num
        _ = 3 * z ^ 2 := by
          have hzsq_nonneg : 0 ≤ z ^ 2 := sq_nonneg z
          simp [abs_eq_self.mpr hzsq_nonneg]
    _ ≤ 3 * M ^ 2 := by nlinarith
    _ = (3 * M.toNNReal ^ 2 : ℝ) := by simp [hMnn]

/-- Local Lipschitz bound for the cube (`lem:cube-lipschitz`): for `M ≥ 0`, the map
`z ↦ -z³` is `3M²`-Lipschitz on `[-M, M]`. -/
theorem cube_lipschitzOnWith (M : ℝ) (hM : 0 ≤ M) :
    LipschitzOnWith (3 * M.toNNReal ^ 2) (fun z : ℝ => -(z ^ 3)) (Set.Icc (-M) M) := by
  refine Convex.lipschitzOnWith_of_nnnorm_deriv_le
    (fun z hz => by
      fun_prop)
    (fun z hz => nnnorm_deriv_neg_cube_le M hM z hz)
    (convex_Icc (-M) M)

end ODE
end Analysis
end LeanEval
