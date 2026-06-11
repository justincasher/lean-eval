import Mathlib
import EvalTools.Markers
import LeanEval.Analysis.ODE.CubicDecay.ClosedForm

/-!
Asymptotics of the closed form `g(t)·√t → 1/√2` as `t → ∞`. Helper file for
`LeanEval.Analysis.ODE.CubicDecay`.
-/

namespace LeanEval
namespace Analysis
namespace ODE

open Filter Topology

/-- Reciprocal form of the ratio (`lem:ratio-eventually-eq`): for `t > 0`,
`t/(1 + 2t) = 1/(1/t + 2)`. -/
theorem ratio_eq (t : ℝ) (ht : 0 < t) : t / (1 + 2 * t) = 1 / (1 / t + 2) := by
  sorry

/-- Limit of the ratio (`lem:ratio-limit`): `t/(1 + 2t) → 1/2` as `t → ∞`. -/
theorem ratio_tendsto :
    Tendsto (fun t : ℝ => t / (1 + 2 * t)) atTop (𝓝 (1 / 2)) := by
  sorry

/-- Square-root form of the scaled closed form (`lem:closed-form-sqrt-eq`): for `t > 0`,
`g(t)·√t = √(t/(1 + 2t))`. -/
theorem closedForm_mul_sqrt (t : ℝ) (ht : 0 < t) :
    closedForm t * Real.sqrt t = Real.sqrt (t / (1 + 2 * t)) := by
  sorry

/-- Asymptotics of the closed form (`lem:closed-form-asymptotic`): `g(t)·√t → 1/√2` as
`t → ∞`. -/
theorem closedForm_asymptotic :
    Tendsto (fun t : ℝ => closedForm t * Real.sqrt t) atTop (𝓝 (1 / Real.sqrt 2)) := by
  sorry

end ODE
end Analysis
end LeanEval
