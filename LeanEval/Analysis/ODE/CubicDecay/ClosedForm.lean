import Mathlib
import EvalTools.Markers

/-!
The closed form `g(t) = (√(1 + 2t))⁻¹` for the IVP `y' = -y³`, `y 0 = 1`, together with
its initial value, derivative, and continuity. Helper file for
`LeanEval.Analysis.ODE.CubicDecay`.
-/

namespace LeanEval
namespace Analysis
namespace ODE

open Filter Topology

/-- Closed form (`def:closed-form`): `g(t) = (√(1 + 2t))⁻¹`. On `{t : 1 + 2t > 0}` this
equals `(1 + 2t)^(-1/2)`. -/
noncomputable def closedForm (t : ℝ) : ℝ := (Real.sqrt (1 + 2 * t))⁻¹

/-- Initial value of the closed form (`lem:closed-form-zero`): `g(0) = 1`. -/
theorem closedForm_zero : closedForm 0 = 1 := by
  sorry

/-- Derivative of the affine square root (`lem:sqrt-affine-deriv`): for `t` with `1 + 2t > 0`,
the map `t ↦ √(1 + 2t)` has derivative `1/√(1 + 2t)` at `t`. -/
theorem sqrt_affine_hasDerivAt (t : ℝ) (ht : 0 < 1 + 2 * t) :
    HasDerivAt (fun t : ℝ => Real.sqrt (1 + 2 * t)) (1 / Real.sqrt (1 + 2 * t)) t := by
  sorry

/-- Cube identity for the closed form (`lem:closed-form-cube-identity`): for `t` with
`1 + 2t > 0`, writing `s = √(1 + 2t)` and `s' = 1/√(1 + 2t)`, one has `-(s'/s²) = -g(t)³`. -/
theorem closedForm_cube_identity (t : ℝ) (ht : 0 < 1 + 2 * t) :
    -((1 / Real.sqrt (1 + 2 * t)) / (Real.sqrt (1 + 2 * t)) ^ 2) = -(closedForm t) ^ 3 := by
  sorry

/-- Closed form solves the ODE (`lem:closed-form-deriv`): for `t` with `1 + 2t > 0`, the
function `g` has derivative `-g(t)³` at `t`. -/
theorem closedForm_hasDerivAt (t : ℝ) (ht : 0 < 1 + 2 * t) :
    HasDerivAt closedForm (-(closedForm t) ^ 3) t := by
  sorry

/-- Continuity of the closed form (`lem:closed-form-continuous`): `g` is continuous on
`[0, ∞)`. -/
theorem closedForm_continuousOn : ContinuousOn closedForm (Set.Ici 0) := by
  sorry

end ODE
end Analysis
end LeanEval
