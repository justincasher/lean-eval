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
  have h1 : t ≠ 0 := ht.ne'
  have h2 : (1 + 2*t) ≠ 0 := by positivity
  field_simp [h1, h2]

/-- Limit of the ratio (`lem:ratio-limit`): `t/(1 + 2t) → 1/2` as `t → ∞`. -/
theorem ratio_tendsto :
    Tendsto (fun t : ℝ => t / (1 + 2 * t)) atTop (𝓝 (1 / 2)) := by
  have h_eventually : (fun t : ℝ => t / (1 + 2 * t)) =ᶠ[atTop] (fun t : ℝ => 1 / (1 / t + 2)) := by
    refine (eventually_gt_atTop 0).mono fun t ht => ?_
    exact ratio_eq t ht
  have h_inv : Tendsto (fun t : ℝ => 1 / t) atTop (𝓝 (0 : ℝ)) := by
    simpa using tendsto_inv_atTop_zero (𝕜 := ℝ)
  have h_den : Tendsto (fun t : ℝ => (1 / t + 2 : ℝ)) atTop (𝓝 (2 : ℝ)) := by
    simpa [zero_add] using h_inv.add (tendsto_const_nhds (x := (2 : ℝ)))
  have h_main : Tendsto (fun t : ℝ => 1 / (1 / t + 2)) atTop (𝓝 (1 / 2)) :=
    (tendsto_const_nhds (x := (1 : ℝ))).div h_den (by norm_num : (2 : ℝ) ≠ 0)
  exact h_main.congr' h_eventually.symm

/-- Square-root form of the scaled closed form (`lem:closed-form-sqrt-eq`): for `t > 0`,
`g(t)·√t = √(t/(1 + 2t))`. -/
theorem closedForm_mul_sqrt (t : ℝ) (ht : 0 < t) :
    closedForm t * Real.sqrt t = Real.sqrt (t / (1 + 2 * t)) := by
  rw [closedForm, Real.sqrt_div ht.le, div_eq_mul_inv]
  ring

/-- Asymptotics of the closed form (`lem:closed-form-asymptotic`): `g(t)·√t → 1/√2` as
`t → ∞`. -/
theorem closedForm_asymptotic :
    Tendsto (fun t : ℝ => closedForm t * Real.sqrt t) atTop (𝓝 (1 / Real.sqrt 2)) := by
  have hval : (1 : ℝ) / Real.sqrt 2 = Real.sqrt (1 / 2) := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
  have hsqrt_tendsto : Tendsto (fun t : ℝ => Real.sqrt (t / (1 + 2 * t))) atTop (𝓝 (Real.sqrt (1 / 2))) :=
    ratio_tendsto.sqrt
  have hevent : (fun t : ℝ => Real.sqrt (t / (1 + 2 * t))) =ᶠ[atTop] (fun t => closedForm t * Real.sqrt t) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact (closedForm_mul_sqrt t ht).symm
  rw [hval]
  exact hsqrt_tendsto.congr' hevent

end ODE
end Analysis
end LeanEval
