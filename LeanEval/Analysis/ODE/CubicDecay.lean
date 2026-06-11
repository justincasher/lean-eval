import Mathlib
import EvalTools.Markers

namespace LeanEval
namespace Analysis
namespace ODE

/-!
Polynomial decay of `y' = -y³`.

The differential equation `y'(t) = -(y t)³` with `y 0 = 1` has the explicit solution
`y(t) = 1/√(1 + 2t)` on `[0, ∞)`. This benchmark asks for the asymptotic rate
`y t · √t → 1/√2` as `t → ∞`, given only the ODE and the initial condition.

The interesting content is not the explicit form (a hint) but the asymptotic statement:
the prover must combine an ODE hypothesis with a limit calculation. The ODE pins down `y`
uniquely on `[0, ∞)`, and the asymptotic follows from the closed form.
-/

open Filter Topology
open scoped NNReal

/-! ### The closed form -/

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

/-! ### Uniqueness via Grönwall -/

variable {y : ℝ → ℝ}

/-- Continuity of a solution (`lem:solution-continuous`): a solution `y` is continuous on
`[0, ∞)`. -/
theorem solution_continuousOn
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Set.Ici 0) 0) :
    ContinuousOn y (Set.Ici 0) := by
  sorry

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

/-! ### Asymptotics of the closed form -/

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

/-! ### Main result -/

/-- Asymptotic decay rate for `y' = -y³, y(0) = 1` (`thm:main`): the solution satisfies
`y t · √t → 1/√2` as `t → ∞`. -/
@[eval_problem]
theorem cubic_decay_asymptotic
    (y : ℝ → ℝ) (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Set.Ici 0) 0)
    (hy0 : y 0 = 1) :
    Tendsto (fun t : ℝ => y t * Real.sqrt t) atTop (𝓝 (1 / Real.sqrt 2)) := by
  sorry

end ODE
end Analysis
end LeanEval
