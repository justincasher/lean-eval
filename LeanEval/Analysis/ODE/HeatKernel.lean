import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import EvalTools.Markers

namespace LeanEval
namespace Analysis
namespace ODE

/-!
The Gaussian heat kernel solves the 1D heat equation.

Define
  `u(t, x) = (4 π t)^(-1/2) · ∫_ℝ exp(-(x - y)² / (4 t)) · f(y) dy`
for `t > 0`, and extend by `u(t, x) := f x` for `t ≤ 0`. Then on `(0, ∞) × ℝ` we have
  `∂_t u = ∂_x² u`,
and `u(t, x) → f x` as `t ↓ 0` for every `x`.

This is a substantial benchmark because it exercises differentiation under the integral
sign, the explicit Gaussian integral evaluation, approximate-identity arguments for the
initial trace, and the heat-PDE identity satisfied by the kernel itself.

The PDE statement asserts the existence of the spatial first and second derivatives at
each `(t, x)` with `t > 0`, and equates the time derivative of `u` to the spatial second
derivative. Stating things via `HasDerivAt` (rather than relying on `deriv` returning `0`
silently when the derivative does not exist) ensures the Lean statement matches the
intended PDE.
-/

open Real MeasureTheory

/-! ### Definitions -/

/-- The normalized 1D Gaussian heat kernel `G_t(x) = (4 π t)^(-1/2) · exp(-x² / (4 t))`. -/
noncomputable def gaussianHeatKernel (t x : ℝ) : ℝ :=
  (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) * Real.exp (-(x ^ 2) / (4 * t))

/-- The 1D Gaussian heat kernel. Extended by `f x` for `t ≤ 0` so that it is a global
function `ℝ × ℝ → ℝ`; the PDE statement only constrains its behaviour on `t > 0`. -/
noncomputable def heatSolution (f : ℝ → ℝ) (t x : ℝ) : ℝ :=
  if 0 < t then
    (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) *
      ∫ y : ℝ, Real.exp (-((x - y) ^ 2) / (4 * t)) * f y
  else
    f x

/-! ### The kernel and its derivatives -/

/-- **Convolution form of the solution.** For `t > 0` the constant prefactor can be
pulled inside the integral, exhibiting `heatSolution f t x` as a convolution against the
kernel. -/
theorem heatSolution_eq_kernel_integral (f : ℝ → ℝ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    heatSolution f t x = ∫ y : ℝ, gaussianHeatKernel t (x - y) * f y := by
  sorry

/-- **Translated kernel is integrable.** -/
theorem kernel_translate_integrable {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Integrable (fun y : ℝ => gaussianHeatKernel t (x - y)) := by
  sorry

/-- **Integrand is integrable.** For bounded continuous `f`, the convolution integrand is
integrable. -/
theorem kernel_integrand_integrable {f : ℝ → ℝ} (hf_cont : Continuous f) {M : ℝ}
    (hf_bdd : ∀ x, |f x| ≤ M) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Integrable (fun y : ℝ => gaussianHeatKernel t (x - y) * f y) := by
  sorry

/-- **First spatial derivative of the kernel.** -/
theorem kernel_hasDerivAt_space {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun z : ℝ => gaussianHeatKernel t z)
      (-(x / (2 * t)) * gaussianHeatKernel t x) x := by
  sorry

/-- **Second spatial derivative of the kernel.** -/
theorem kernel_hasDerivAt_space_second {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun z : ℝ => -(z / (2 * t)) * gaussianHeatKernel t z)
      ((x ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * gaussianHeatKernel t x) x := by
  sorry

/-- **Time derivative of the prefactor** `s ↦ (4 π s)^(-1/2)`. -/
theorem prefactor_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => (4 * Real.pi * s)⁻¹ ^ ((1 : ℝ) / 2))
      (-(1 / (2 * t)) * (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2)) t := by
  sorry

/-- **Time derivative of the kernel.** -/
theorem kernel_hasDerivAt_time (x : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => gaussianHeatKernel s x)
      ((x ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * gaussianHeatKernel t x) t := by
  sorry

/-- **Kernel solves the heat equation pointwise.** The second spatial derivative and the
time derivative of the kernel produce the same value. -/
theorem kernel_heat_identity (x : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun z : ℝ => -(z / (2 * t)) * gaussianHeatKernel t z)
        ((x ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * gaussianHeatKernel t x) x ∧
      HasDerivAt (fun s : ℝ => gaussianHeatKernel s x)
        ((x ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * gaussianHeatKernel t x) t := by
  sorry

/-! ### Gaussian domination bounds -/

/-- **Absolute-value-times-Gaussian is integrable.** -/
theorem integrable_abs_mul_gaussian {c : ℝ} (hc : 0 < c) :
    Integrable (fun y : ℝ => |y| * Real.exp (-c * y ^ 2)) := by
  sorry

/-- **Square-times-Gaussian is integrable.** -/
theorem integrable_sq_mul_gaussian {c : ℝ} (hc : 0 < c) :
    Integrable (fun y : ℝ => y ^ 2 * Real.exp (-c * y ^ 2)) := by
  sorry

/-- **Polynomial-times-Gaussian is integrable (centered case).** -/
theorem gaussian_poly_integrable_zero {c : ℝ} (hc : 0 < c) {a b d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) :
    Integrable (fun y : ℝ => (a + b * |y| + d * y ^ 2) * Real.exp (-c * y ^ 2)) := by
  sorry

/-- **Shifted polynomial-times-Gaussian is integrable.** -/
theorem shifted_gaussian_integrable (x₀ : ℝ) {c : ℝ} (hc : 0 < c) {a b d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) :
    Integrable (fun y : ℝ =>
      (a + b * |y - x₀| + d * (y - x₀) ^ 2) * Real.exp (-c * (y - x₀) ^ 2)) := by
  sorry

/-- **A uniform quadratic lower bound.** -/
theorem gaussian_quadratic_lower_bound {x x₀ : ℝ} (h : |x - x₀| ≤ 1) (y : ℝ) :
    (1 / 2) * (y - x₀) ^ 2 - 2 ≤ (x - y) ^ 2 := by
  sorry

/-- **Gaussian exponential domination.** -/
theorem gaussian_exp_domination {x x₀ : ℝ} (h : |x - x₀| ≤ 1) {t : ℝ} (ht : 0 < t) (y : ℝ) :
    Real.exp (-((x - y) ^ 2) / (4 * t)) ≤
      Real.exp (1 / (2 * t)) * Real.exp (-((y - x₀) ^ 2) / (8 * t)) := by
  sorry

/-- **Pointwise estimate for the first spatial derivative.** -/
theorem bound_space_pointwise {f : ℝ → ℝ} {M : ℝ} (hf_bdd : ∀ x, |f x| ≤ M)
    {t : ℝ} (ht : 0 < t) (x₀ : ℝ) {x : ℝ} (hx : |x - x₀| ≤ 1) (y : ℝ) :
    |-((x - y) / (2 * t)) * gaussianHeatKernel t (x - y) * f y| ≤
      M / (2 * t) * (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) * Real.exp (1 / (2 * t)) *
        (1 + |y - x₀|) * Real.exp (-((y - x₀) ^ 2) / (8 * t)) := by
  sorry

/-- **Uniform domination of the first spatial derivative.** -/
theorem bound_space {f : ℝ → ℝ} {M : ℝ} (hf_bdd : ∀ x, |f x| ≤ M)
    {t : ℝ} (ht : 0 < t) (x₀ : ℝ) :
    ∃ g : ℝ → ℝ, Integrable g ∧
      ∀ x : ℝ, |x - x₀| ≤ 1 → ∀ y : ℝ,
        |-((x - y) / (2 * t)) * gaussianHeatKernel t (x - y) * f y| ≤ g y := by
  sorry

/-- **Pointwise estimate for the second spatial derivative.** -/
theorem bound_space_second_pointwise {f : ℝ → ℝ} {M : ℝ} (hf_bdd : ∀ x, |f x| ≤ M)
    {t : ℝ} (ht : 0 < t) (x₀ : ℝ) {x : ℝ} (hx : |x - x₀| ≤ 1) (y : ℝ) :
    |((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * gaussianHeatKernel t (x - y) * f y| ≤
      M * (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) * Real.exp (1 / (2 * t)) *
        ((1 + |y - x₀|) ^ 2 / (4 * t ^ 2) + 1 / (2 * t)) *
        Real.exp (-((y - x₀) ^ 2) / (8 * t)) := by
  sorry

/-- **Uniform domination of the second spatial derivative.** -/
theorem bound_space_second {f : ℝ → ℝ} {M : ℝ} (hf_bdd : ∀ x, |f x| ≤ M)
    {t : ℝ} (ht : 0 < t) (x₀ : ℝ) :
    ∃ g : ℝ → ℝ, Integrable g ∧
      ∀ x : ℝ, |x - x₀| ≤ 1 → ∀ y : ℝ,
        |((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * gaussianHeatKernel t (x - y) * f y| ≤ g y := by
  sorry

/-- **Pointwise estimate for the time derivative.** -/
theorem bound_time_pointwise {f : ℝ → ℝ} {M : ℝ} (hf_bdd : ∀ x, |f x| ≤ M)
    {t₀ : ℝ} (ht₀ : 0 < t₀) (x₀ : ℝ) {s : ℝ} (hs : s ∈ Set.Ioo (t₀ / 2) (2 * t₀)) (y : ℝ) :
    |((x₀ - y) ^ 2 / (4 * s ^ 2) - 1 / (2 * s)) * gaussianHeatKernel s (x₀ - y) * f y| ≤
      M * (2 * Real.pi * t₀)⁻¹ ^ ((1 : ℝ) / 2) *
        ((x₀ - y) ^ 2 / t₀ ^ 2 + 1 / t₀) *
        Real.exp (-((x₀ - y) ^ 2) / (8 * t₀)) := by
  sorry

/-- **Uniform domination of the time derivative.** -/
theorem bound_time {f : ℝ → ℝ} {M : ℝ} (hf_bdd : ∀ x, |f x| ≤ M)
    {t₀ : ℝ} (ht₀ : 0 < t₀) (x₀ : ℝ) :
    ∃ g : ℝ → ℝ, Integrable g ∧
      ∀ s : ℝ, s ∈ Set.Ioo (t₀ / 2) (2 * t₀) → ∀ y : ℝ,
        |((x₀ - y) ^ 2 / (4 * s ^ 2) - 1 / (2 * s)) * gaussianHeatKernel s (x₀ - y) * f y| ≤ g y := by
  sorry

/-! ### Differentiation under the integral sign -/

/-- **Shifted, scaled kernel has a derivative.** -/
theorem shift_scale_hasDerivAt {k : ℝ → ℝ} {y c d v : ℝ} (hk : HasDerivAt k d (c - y)) :
    HasDerivAt (fun z : ℝ => k (z - y) * v) (d * v) c := by
  sorry

/-- **Integrand is a.e. strongly measurable.** -/
theorem shift_scale_aestronglyMeasurable {k : ℝ → ℝ} (hk : Continuous k)
    {f : ℝ → ℝ} (hf : Continuous f) (z : ℝ) :
    AEStronglyMeasurable (fun y : ℝ => k (z - y) * f y) volume := by
  sorry

/-- **Differentiation under the integral sign, packaged** (the Leibniz rule
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` applied at a base point with an
explicit neighborhood `s` of `r₀`). -/
theorem hasDerivAt_under_integral {F F' : ℝ → ℝ → ℝ} {r₀ : ℝ} {s : Set ℝ}
    (hs : s ∈ nhds r₀) {g : ℝ → ℝ} (hg : Integrable g)
    (hF₀ : Integrable (fun y => F r₀ y))
    (hmeas : ∀ r ∈ s, AEStronglyMeasurable (fun y => F r y) volume)
    (hbound : ∀ y : ℝ, ∀ r ∈ s, |F' r y| ≤ g y)
    (hderiv : ∀ y : ℝ, ∀ r ∈ s, HasDerivAt (fun r' => F r' y) (F' r y) r) :
    Integrable (fun y => F' r₀ y) ∧
      HasDerivAt (fun r => ∫ y : ℝ, F r y) (∫ y : ℝ, F' r₀ y) r₀ := by
  sorry

/-- **First spatial derivative of the solution.** -/
theorem hasDerivAt_space {f : ℝ → ℝ} (hf_cont : Continuous f) {M : ℝ}
    (hf_bdd : ∀ x, |f x| ≤ M) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun z : ℝ => heatSolution f t z)
      (∫ y : ℝ, -((x - y) / (2 * t)) * gaussianHeatKernel t (x - y) * f y) x := by
  sorry

/-- **Second spatial derivative of the solution.** -/
theorem hasDerivAt_space_second {f : ℝ → ℝ} (hf_cont : Continuous f) {M : ℝ}
    (hf_bdd : ∀ x, |f x| ≤ M) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt
      (fun z : ℝ => ∫ y : ℝ, -((z - y) / (2 * t)) * gaussianHeatKernel t (z - y) * f y)
      (∫ y : ℝ, ((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * gaussianHeatKernel t (x - y) * f y) x := by
  sorry

/-- **Solution agrees with the kernel integral near positive times.** -/
theorem heatSolution_eventuallyEq_kernel_integral (f : ℝ → ℝ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    (fun s : ℝ => heatSolution f s x) =ᶠ[nhds t]
      fun s : ℝ => ∫ y : ℝ, gaussianHeatKernel s (x - y) * f y := by
  sorry

/-- **Time derivative of the solution.** -/
theorem hasDerivAt_time {f : ℝ → ℝ} (hf_cont : Continuous f) {M : ℝ}
    (hf_bdd : ∀ x, |f x| ≤ M) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s : ℝ => heatSolution f s x)
      (∫ y : ℝ, ((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * gaussianHeatKernel t (x - y) * f y) t := by
  sorry

/-- **Time derivative equals the second spatial derivative.** Both `hasDerivAt_time` and
`hasDerivAt_space_second` produce the same integral value. -/
theorem time_eq_space_second (f : ℝ → ℝ) (t x : ℝ) :
    (∫ y : ℝ, ((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * gaussianHeatKernel t (x - y) * f y) =
      ∫ y : ℝ, ((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * gaussianHeatKernel t (x - y) * f y := by
  sorry

/-! ### The PDE on `(0, ∞) × ℝ` -/

/-- **Heat equation half.** On `(0, ∞) × ℝ` the spatial first and second derivatives of
`heatSolution f` exist and the time derivative equals the second spatial derivative. -/
theorem pde_part {f : ℝ → ℝ} (hf_cont : Continuous f) {M : ℝ}
    (hf_bdd : ∀ x, |f x| ≤ M) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ∃ ux : ℝ → ℝ, ∃ uxx : ℝ,
      (∀ z : ℝ, HasDerivAt (fun z' => heatSolution f t z') (ux z) z) ∧
        HasDerivAt ux uxx x ∧
        HasDerivAt (fun s => heatSolution f s x) uxx t := by
  sorry

/-! ### Recovery of the initial datum as `t ↓ 0` -/

/-- **Total Gaussian mass.** -/
theorem gaussian_total_mass : ∫ z : ℝ, Real.exp (-z ^ 2) = Real.sqrt Real.pi := by
  sorry

/-- **Exponent simplifies under the scaling substitution.** -/
theorem gaussian_exponent_simplify {t : ℝ} (ht : 0 < t) (z : ℝ) :
    Real.exp (-((2 * Real.sqrt t * z) ^ 2) / (4 * t)) = Real.exp (-z ^ 2) := by
  sorry

/-- **Change of variables in the solution** via `y = x - 2 √t z`. -/
theorem heatSolution_change_of_variables (f : ℝ → ℝ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    heatSolution f t x =
      (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) * (2 * Real.sqrt t) *
        ∫ z : ℝ, Real.exp (-z ^ 2) * f (x - 2 * Real.sqrt t * z) := by
  sorry

/-- **Substitution form of the solution.** -/
theorem heatSolution_eq_subst (f : ℝ → ℝ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    heatSolution f t x =
      Real.pi⁻¹ ^ ((1 : ℝ) / 2) * ∫ z : ℝ, Real.exp (-z ^ 2) * f (x - 2 * Real.sqrt t * z) := by
  sorry

/-- **Dominating bound for the substituted integrand.** -/
theorem subst_integrand_bound {f : ℝ → ℝ} {M : ℝ} (hf_bdd : ∀ x, |f x| ≤ M) (t x : ℝ) :
    (∀ z : ℝ, |Real.exp (-z ^ 2) * f (x - 2 * Real.sqrt t * z)| ≤ M * Real.exp (-z ^ 2)) ∧
      Integrable (fun z : ℝ => M * Real.exp (-z ^ 2)) := by
  sorry

/-- **Pointwise convergence of the substituted integrand** as `t ↓ 0`. -/
theorem subst_integrand_tendsto {f : ℝ → ℝ} (hf_cont : Continuous f) (x z : ℝ) :
    Filter.Tendsto (fun t : ℝ => Real.exp (-z ^ 2) * f (x - 2 * Real.sqrt t * z))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.exp (-z ^ 2) * f x)) := by
  sorry

/-- **Gaussian integral of a constant.** -/
theorem gaussian_integral_const_mul (c : ℝ) :
    ∫ z : ℝ, Real.exp (-z ^ 2) * c = Real.sqrt Real.pi * c := by
  sorry

/-- **Convergence of the substituted integral** as `t ↓ 0`. -/
theorem subst_integral_tendsto {f : ℝ → ℝ} (hf_cont : Continuous f) {M : ℝ}
    (hf_bdd : ∀ x, |f x| ≤ M) (x : ℝ) :
    Filter.Tendsto (fun t : ℝ => ∫ z : ℝ, Real.exp (-z ^ 2) * f (x - 2 * Real.sqrt t * z))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.sqrt Real.pi * f x)) := by
  sorry

/-- **Initial-condition half.** `heatSolution f t x → f x` as `t ↓ 0`. -/
theorem initial_condition {f : ℝ → ℝ} (hf_cont : Continuous f) {M : ℝ}
    (hf_bdd : ∀ x, |f x| ≤ M) (x : ℝ) :
    Filter.Tendsto (fun t : ℝ => heatSolution f t x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f x)) := by
  sorry

/-! ### Main theorem -/

/-- **The Gaussian heat kernel solves the heat equation.**

For continuous bounded `f : ℝ → ℝ`, the heat-kernel convolution `u := heatSolution f`
satisfies the 1D heat equation `∂_t u = ∂_x² u` on `(0, ∞) × ℝ` (in the sense that the
required spatial derivatives exist and equal the time derivative), and `u(t, x) → f x`
as `t ↓ 0` for every `x`. -/
@[eval_problem]
theorem heat_kernel_solves_heat_equation
    (f : ℝ → ℝ) (hf_cont : Continuous f) (hf_bdd : ∃ M : ℝ, ∀ x, |f x| ≤ M) :
    -- The PDE on (0, ∞) × ℝ.
    (∀ t : ℝ, 0 < t → ∀ x : ℝ, ∃ ux : ℝ → ℝ, ∃ uxx : ℝ,
        (∀ y : ℝ, HasDerivAt (fun z => heatSolution f t z) (ux y) y) ∧
        HasDerivAt ux uxx x ∧
        HasDerivAt (fun s => heatSolution f s x) uxx t) ∧
    -- Initial condition recovered as a one-sided limit at t = 0.
    (∀ x : ℝ,
        Filter.Tendsto (fun t : ℝ => heatSolution f t x)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (f x))) := by
  sorry

end ODE
end Analysis
end LeanEval
