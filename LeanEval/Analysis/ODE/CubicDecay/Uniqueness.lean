import Mathlib
import EvalTools.Markers
import LeanEval.Analysis.ODE.CubicDecay.ClosedForm
import LeanEval.Analysis.ODE.CubicDecay.Cube

/-!
Uniqueness of the solution via Grönwall's trajectory comparison: any solution `y` of
`y' = -y³` with `y 0 = 1`, continuous on `[0, ∞)`, equals the closed form `g`. Helper file
for `LeanEval.Analysis.ODE.CubicDecay`.
-/

namespace LeanEval
namespace Analysis
namespace ODE

open Filter Topology

variable {y : ℝ → ℝ}

/-- Continuity of a solution (`lem:solution-continuous`): a solution `y` is continuous on
`[0, ∞)`. -/
theorem solution_continuousOn
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Set.Ici 0) 0) :
    ContinuousOn y (Set.Ici 0) := by
  sorry

/-- Solution as an `Ici` trajectory (`lem:solution-traj`): for `0 < a ≤ t` and `M` bounding
`|y|` on `[0, t]`, on `[a, t]` the solution has derivative `-y(s)³` within `Ici s`, is
continuous on `[a, t]`, and stays in `[-M, M]`. -/
theorem solution_traj
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Set.Ici 0) 0)
    (a t M : ℝ) (ha : 0 < a) (hat : a ≤ t)
    (hM : ∀ s ∈ Set.Icc (0 : ℝ) t, |y s| ≤ M) :
    (∀ s ∈ Set.Icc a t, HasDerivWithinAt y (-(y s) ^ 3) (Set.Ici s) s) ∧
      ContinuousOn y (Set.Icc a t) ∧
      (∀ s ∈ Set.Icc a t, y s ∈ Set.Icc (-M) M) := by
  sorry

/-- Closed form as an `Ici` trajectory (`lem:closed-form-traj`): for `0 < a ≤ t` and `M`
bounding `|g|` on `[0, t]`, on `[a, t]` the closed form has derivative `-g(s)³` within `Ici s`,
is continuous on `[a, t]`, and stays in `[-M, M]`. -/
theorem closedForm_traj
    (a t M : ℝ) (ha : 0 < a) (hat : a ≤ t)
    (hM : ∀ s ∈ Set.Icc (0 : ℝ) t, |closedForm s| ≤ M) :
    (∀ s ∈ Set.Icc a t, HasDerivWithinAt closedForm (-(closedForm s) ^ 3) (Set.Ici s) s) ∧
      ContinuousOn closedForm (Set.Icc a t) ∧
      (∀ s ∈ Set.Icc a t, closedForm s ∈ Set.Icc (-M) M) := by
  sorry

/-- Grönwall distance bound (`lem:gronwall-bound`): for `t > 0` and `M` bounding `|y|` and
`|g|` on `[0, t]`, every `0 < a ≤ t` satisfies
`|y(t) - g(t)| ≤ |y(a) - g(a)| · exp(3M²(t - a))`. -/
theorem gronwall_bound
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Set.Ici 0) 0)
    (t M : ℝ) (ht : 0 < t)
    (hMy : ∀ s ∈ Set.Icc (0 : ℝ) t, |y s| ≤ M)
    (hMg : ∀ s ∈ Set.Icc (0 : ℝ) t, |closedForm s| ≤ M)
    (a : ℝ) (ha : 0 < a) (hat : a ≤ t) :
    |y t - closedForm t| ≤ |y a - closedForm a| * Real.exp (3 * M ^ 2 * (t - a)) := by
  sorry

/-- Uniform bound on a compact interval (`lem:compact-bound`): for a solution `y` and `t ≥ 0`
there is `M ≥ 0` bounding both `|y|` and `|g|` on `[0, t]`. -/
theorem compact_bound
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Set.Ici 0) 0)
    (t : ℝ) (ht : 0 ≤ t) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ s ∈ Set.Icc (0 : ℝ) t, |y s| ≤ M) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) t, |closedForm s| ≤ M) := by
  sorry

/-- A vanishing right limit forces nonpositivity (`lem:limit-forces-nonpos`): if `h → 0`
along `𝓝[>] 0` and `c ≤ h(a)` for all `a ∈ (0, t]`, then `c ≤ 0`. -/
theorem limit_forces_nonpos {h : ℝ → ℝ} {c t : ℝ} (ht : 0 < t)
    (hlim : Tendsto h (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hle : ∀ a ∈ Set.Ioc (0 : ℝ) t, c ≤ h a) : c ≤ 0 := by
  sorry

/-- The Grönwall bound vanishes at `0⁺` (`lem:gronwall-rhs-tendsto`): the map
`a ↦ |y(a) - g(a)| · exp(3M²(t - a))` tends to `0` along `𝓝[>] 0`. -/
theorem gronwall_rhs_tendsto
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Set.Ici 0) 0)
    (hy0 : y 0 = 1) (t M : ℝ) (ht : 0 < t) :
    Tendsto (fun a : ℝ => |y a - closedForm a| * Real.exp (3 * M ^ 2 * (t - a)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  sorry

/-- Uniqueness (`lem:uniqueness`): any solution `y` equals the closed form on `[0, ∞)`. -/
theorem uniqueness
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Set.Ici 0) 0)
    (hy0 : y 0 = 1) :
    ∀ t : ℝ, 0 ≤ t → y t = closedForm t := by
  sorry

end ODE
end Analysis
end LeanEval
