import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
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
  rw [heatSolution, if_pos ht]
  unfold gaussianHeatKernel
  rw [← integral_const_mul]
  simp [mul_assoc]

/-- **Translated kernel is integrable.** -/
theorem kernel_translate_integrable {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Integrable (fun y : ℝ => gaussianHeatKernel t (x - y)) := by
  have hpos : 0 < 1 / (4 * t) := by
    refine div_pos (by norm_num) (mul_pos (by norm_num) ht)
  have h_gaussian : Integrable (fun z : ℝ => Real.exp (-(z ^ 2 / (4 * t)))) := by
    have : (fun z : ℝ => Real.exp (-(z ^ 2 / (4 * t)))) =
          (fun z : ℝ => Real.exp (-(1 / (4 * t)) * z ^ 2)) := by
      ext z; simp [div_eq_mul_inv, mul_comm, mul_left_comm]
    rw [this]
    exact integrable_exp_neg_mul_sq hpos
  have h_kernel : Integrable (fun z : ℝ => gaussianHeatKernel t z) := by
    dsimp [gaussianHeatKernel]
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm] using
      h_gaussian.const_mul ((4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2))
  exact h_kernel.comp_sub_left x

/-- **Integrand is integrable.** For bounded continuous `f`, the convolution integrand is
integrable. -/
theorem kernel_integrand_integrable {f : ℝ → ℝ} (hf_cont : Continuous f) {M : ℝ}
    (hf_bdd : ∀ x, |f x| ≤ M) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Integrable (fun y : ℝ => gaussianHeatKernel t (x - y) * f y) := by
  have h_int : Integrable (fun y : ℝ => gaussianHeatKernel t (x - y)) :=
    kernel_translate_integrable ht x
  have h_meas : AEStronglyMeasurable f volume :=
    hf_cont.aestronglyMeasurable (μ := volume)
  have h_bound : ∀ᵐ y ∂volume, ‖f y‖ ≤ M := by
    filter_upwards [] with y
    simpa [Real.norm_eq_abs] using hf_bdd y
  simpa [mul_comm] using h_int.bdd_mul h_meas h_bound

/-- **First spatial derivative of the kernel.** -/
theorem kernel_hasDerivAt_space {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun z : ℝ => gaussianHeatKernel t z)
      (-(x / (2 * t)) * gaussianHeatKernel t x) x := by
  -- derivative of g(z) = -(z^2)/(4t) at x is -(x/(2t))
  have hg : HasDerivAt (fun z : ℝ => -(z ^ 2) / (4 * t)) (-(x / (2 * t))) x := by
    have hsq : HasDerivAt (fun z : ℝ => z ^ 2) (2*x) x := by
      simpa using hasDerivAt_pow 2 x
    have hneg : HasDerivAt (fun z : ℝ => -(z ^ 2)) (-(2*x)) x := by simpa using hsq.neg
    have hdiv : HasDerivAt (fun z : ℝ => -(z ^ 2) / (4 * t)) (-(2*x) / (4*t)) x :=
      hneg.div_const (4*t)
    have h_eq : -(2*x) / (4*t) = -(x / (2*t)) := by
      field_simp [show t ≠ 0 from by linarith]
      ring
    simpa [h_eq] using hdiv
  -- derivative of exp(g(z)) at x is exp(g(x))*g'(x) via chain rule
  have h_exp : HasDerivAt (fun z : ℝ => Real.exp (-(z ^ 2) / (4 * t)))
      (Real.exp (-(x ^ 2) / (4 * t)) * (-(x / (2 * t)))) x :=
    hg.exp
  -- scale by the constant prefactor C = (4*π*t)^(-1/2)
  have hG : HasDerivAt (fun z : ℝ => gaussianHeatKernel t z)
      ((4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) * (Real.exp (-(x ^ 2) / (4 * t)) * (-(x / (2 * t))))) x := by
    simpa [gaussianHeatKernel] using
      (h_exp.const_mul ((4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2)))
  -- simplify C*(exp(g(x))*g'(x)) to -(x/(2t))*G_t(x)
  simpa [gaussianHeatKernel, mul_comm, mul_left_comm, mul_assoc] using hG

/-- **Second spatial derivative of the kernel.** -/
theorem kernel_hasDerivAt_space_second {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun z : ℝ => -(z / (2 * t)) * gaussianHeatKernel t z)
      ((x ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * gaussianHeatKernel t x) x := by
  have hc : HasDerivAt (fun z : ℝ => -(z / (2 * t))) (-(1 / (2 * t))) x := by
    have : (fun z : ℝ => -(z / (2 * t))) = (fun z : ℝ => (-(1 / (2 * t))) * z) := by
      ext z; ring
    rw [this]
    exact hasDerivAt_const_mul (-(1 / (2 * t)))
  have hd : HasDerivAt (fun z : ℝ => gaussianHeatKernel t z)
      (-(x / (2 * t)) * gaussianHeatKernel t x) x :=
    kernel_hasDerivAt_space ht x
  have hprod := hc.mul hd
  have hfun : ((fun z : ℝ => -(z / (2 * t))) * (fun z : ℝ => gaussianHeatKernel t z)) =
      (fun z : ℝ => -(z / (2 * t)) * gaussianHeatKernel t z) := by
    simp [Pi.mul_def]
  have hderiv : (-(t⁻¹ * 2⁻¹ * gaussianHeatKernel t x) +
      x / (2 * t) * (x / (2 * t) * gaussianHeatKernel t x)) =
    ((x ^ 2 / (4 * t ^ 2) - t⁻¹ * 2⁻¹) * gaussianHeatKernel t x) := by
    have ht_ne : t ≠ 0 := by linarith
    field_simp [ht_ne]
    ring
  simpa [hfun, hderiv] using hprod

/-- **Time derivative of the prefactor** `s ↦ (4 π s)^(-1/2)`. -/
theorem prefactor_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => (4 * Real.pi * s)⁻¹ ^ ((1 : ℝ) / 2))
      (-(1 / (2 * t)) * (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2)) t := by
  have ht_ne_zero : t ≠ 0 := by linarith
  have h4πt_pos : 4 * Real.pi * t > 0 := by positivity
  have h4πt_ne_zero : 4 * Real.pi * t ≠ 0 := by linarith
  -- Derivative of the inner linear function s ↦ 4π*s
  have h_inner : HasDerivAt (fun s : ℝ => 4 * Real.pi * s) (4 * Real.pi) t := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using (hasDerivAt_id t).const_mul (4 * Real.pi)
  -- Derivative of the outer real-power function x ↦ x^((-1)/2) at the point 4π*t
  have h_outer : HasDerivAt (fun x : ℝ => x ^ ((-1 : ℝ) / 2))
      (((-1 : ℝ) / 2) * (4 * Real.pi * t) ^ (((-1 : ℝ) / 2) - 1)) (4 * Real.pi * t) :=
    Real.hasDerivAt_rpow_const (x := 4 * Real.pi * t) (h := Or.inl h4πt_ne_zero) (p := (-1 : ℝ) / 2)
  -- Chain rule: derivative of s ↦ (4π*s)^((-1)/2) at t
  have h_comp : HasDerivAt (fun s : ℝ => (4 * Real.pi * s) ^ ((-1 : ℝ) / 2))
      (((-1 : ℝ) / 2) * (4 * Real.pi * t) ^ (((-1 : ℝ) / 2) - 1) * (4 * Real.pi)) t :=
    h_outer.comp t h_inner
  -- Algebraic simplification of the derivative expression
  have h_alg : (((-1 : ℝ) / 2) * (4 * Real.pi * t) ^ (((-1 : ℝ) / 2) - 1)) * (4 * Real.pi) =
      -(1 / (2 * t)) * ((4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2)) := by
    calc
      (((-1 : ℝ) / 2) * (4 * Real.pi * t) ^ (((-1 : ℝ) / 2) - 1)) * (4 * Real.pi) =
          ((-1 : ℝ) / 2) * ((4 * Real.pi * t) ^ (((-1 : ℝ) / 2) - 1)) * (4 * Real.pi) := by ring
      _ = ((-1 : ℝ) / 2) * (4 * Real.pi) * (4 * Real.pi * t) ^ (((-1 : ℝ) / 2) - 1) := by ring
      _ = ((-1 : ℝ) / 2) * (4 * Real.pi) * (4 * Real.pi * t) ^ ((-3 : ℝ) / 2) := by ring
      _ = (-(1 / (2 * t))) * ((4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2)) := by
        -- Key identity: (4π) * (4π*t)^(-3/2) = (1/t) * (4π*t)^(-1/2)
        have h_key : (4 * Real.pi) * (4 * Real.pi * t) ^ ((-3 : ℝ) / 2) =
            (1 / t) * ((4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2)) := by
          -- Multiply both sides by (4π*t)^(3/2) · (4π*t)^(1/2) = (4π*t)^(2)
          have h_nonzero : (4 * Real.pi * t) ^ ((3 : ℝ) / 2) ≠ 0 :=
            ((Real.rpow_ne_zero (by positivity : 0 ≤ 4 * Real.pi * t) (by norm_num : (3 : ℝ)/2 ≠ 0)).mpr (by positivity))
          apply mul_right_cancel₀ h_nonzero
          calc
            ((4 * Real.pi) * (4 * Real.pi * t) ^ ((-3 : ℝ) / 2)) * (4 * Real.pi * t) ^ ((3 : ℝ) / 2) =
                (4 * Real.pi) * ((4 * Real.pi * t) ^ ((-3 : ℝ) / 2) * (4 * Real.pi * t) ^ ((3 : ℝ) / 2)) := by ring
            _ = (4 * Real.pi) * (4 * Real.pi * t) ^ (((-3 : ℝ) / 2) + ((3 : ℝ) / 2)) := by
              rw [Real.rpow_add h4πt_pos]
            _ = (4 * Real.pi) * (4 * Real.pi * t) ^ (0 : ℝ) := by ring
            _ = (4 * Real.pi) * 1 := by rw [Real.rpow_zero]
            _ = 4 * Real.pi := by ring
            _ = (1 / t) * (4 * Real.pi * t) := by field_simp [ht_ne_zero]; ring
            _ = (1 / t) * ((4 * Real.pi * t) ^ (1 : ℝ)) := by norm_num
            _ = (1 / t) * ((4 * Real.pi * t) ^ (((-1 : ℝ) / 2) + ((3 : ℝ) / 2))) := by ring
            _ = (1 / t) * ((4 * Real.pi * t) ^ ((-1 : ℝ) / 2) * (4 * Real.pi * t) ^ ((3 : ℝ) / 2)) := by
              rw [Real.rpow_add h4πt_pos]
            _ = ((1 / t) * (4 * Real.pi * t) ^ ((-1 : ℝ) / 2)) * (4 * Real.pi * t) ^ ((3 : ℝ) / 2) := by ring
            _ = ((1 / t) * ((4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2))) * (4 * Real.pi * t) ^ ((3 : ℝ) / 2) := by
              have h_eq_rpow : (4 * Real.pi * t) ^ ((-1 : ℝ) / 2) = (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) := by
                calc
                  (4 * Real.pi * t) ^ ((-1 : ℝ) / 2) = (4 * Real.pi * t) ^ (-((1 : ℝ) / 2)) := by ring
                  _ = ((4 * Real.pi * t) ^ ((1 : ℝ) / 2))⁻¹ := by
                    rw [Real.rpow_neg (by positivity : 0 ≤ 4 * Real.pi * t) _]
                  _ = (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) := by
                    rw [Real.inv_rpow (by positivity : 0 ≤ 4 * Real.pi * t) _]
              rw [h_eq_rpow]
        -- Use the key identity inside the product
        have h_prod : ((-1 : ℝ) / 2) * (4 * Real.pi) * (4 * Real.pi * t) ^ ((-3 : ℝ) / 2) =
            (-(1 / (2 * t))) * ((4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2)) := by
          calc
            ((-1 : ℝ) / 2) * (4 * Real.pi) * (4 * Real.pi * t) ^ ((-3 : ℝ) / 2) =
                ((-1 : ℝ) / 2) * ((4 * Real.pi) * (4 * Real.pi * t) ^ ((-3 : ℝ) / 2)) := by ring
            _ = ((-1 : ℝ) / 2) * ((1 / t) * ((4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2))) := by rw [h_key]
            _ = (-(1 / (2 * t))) * ((4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2)) := by ring
        exact h_prod
  -- Rewrite the chain-rule output to the target derivative
  have h_comp' : HasDerivAt (fun s : ℝ => (4 * Real.pi * s) ^ ((-1 : ℝ) / 2))
      (-(1 / (2 * t)) * ((4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2))) t := by
    rw [h_alg] at h_comp
    exact h_comp
  -- Show the original function equals (4π*s)^((-1)/2) near t, then conclude by congr
  have h_eq : (fun s : ℝ => (4 * Real.pi * s)⁻¹ ^ ((1 : ℝ) / 2)) =ᶠ[nhds t]
      (fun s : ℝ => (4 * Real.pi * s) ^ ((-1 : ℝ) / 2)) := by
    have h_mem : Set.Ioo (0 : ℝ) (2*t) ∈ nhds t := by
      refine IsOpen.mem_nhds isOpen_Ioo ?_
      exact Set.mem_Ioo.mpr ⟨by linarith, by nlinarith⟩
    filter_upwards [h_mem] with s hs
    have hs_pos : s > 0 := hs.1
    have h_nonneg : 0 ≤ 4 * Real.pi * s := by positivity
    calc
      (4 * Real.pi * s)⁻¹ ^ ((1 : ℝ) / 2) = ((4 * Real.pi * s) ^ ((1 : ℝ) / 2))⁻¹ := by
        rw [Real.inv_rpow h_nonneg _]
      _ = (4 * Real.pi * s) ^ (-((1 : ℝ) / 2)) := by
        rw [Real.rpow_neg h_nonneg _]
      _ = (4 * Real.pi * s) ^ ((-1 : ℝ) / 2) := by
        have h_exponent : -((1 : ℝ) / 2) = (-1 : ℝ) / 2 := by ring
        rw [h_exponent]
  -- Combine: h_comp' gives HasDerivAt for (4π*s)^((-1)/2), we need it for (4π*s)⁻¹ ^ (1/2)
  -- which is eventually equal near t
  refine h_comp'.congr_of_eventuallyEq h_eq

/-- **Time derivative of the kernel.** -/
theorem kernel_hasDerivAt_time (x : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => gaussianHeatKernel s x)
      ((x ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * gaussianHeatKernel t x) t := by
  have ht_ne : t ≠ 0 := by linarith
  -- derivative of the prefactor A(s) = (4πs)⁻¹ ^ (1/2)
  have hA : HasDerivAt (fun s : ℝ => (4 * Real.pi * s)⁻¹ ^ ((1 : ℝ) / 2))
    (-(1 / (2 * t)) * (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2)) t :=
    prefactor_hasDerivAt ht
  -- derivative of the inner function C(s) = -x²/(4s)
  have hC : HasDerivAt (fun s : ℝ => -(x ^ 2) / (4 * s)) (x ^ 2 / (4 * t ^ 2)) t := by
    have h_inv : HasDerivAt (fun s : ℝ => s⁻¹) (-(t ^ 2)⁻¹) t := hasDerivAt_inv ht_ne
    have h_const_mul : HasDerivAt (fun s : ℝ => (-(x ^ 2) / 4) * s⁻¹) (((-(x ^ 2) / 4) * (-(t ^ 2)⁻¹))) t :=
      HasDerivAt.const_mul (-(x ^ 2) / 4) h_inv
    have h_fun_eq : (fun s : ℝ => -(x ^ 2) / (4 * s)) = (fun s : ℝ => (-(x ^ 2) / 4) * s⁻¹) := by
      ext s; ring
    have h_deriv_eq : (-(x ^ 2) / 4) * (-(t ^ 2)⁻¹) = x ^ 2 / (4 * t ^ 2) := by
      ring
    rw [h_fun_eq]
    rw [← h_deriv_eq]
    exact h_const_mul
  -- derivative of the exponential factor B(s) = exp(C(s))
  have hB : HasDerivAt (fun s : ℝ => Real.exp (-(x ^ 2) / (4 * s)))
    (Real.exp (-(x ^ 2) / (4 * t)) * (x ^ 2 / (4 * t ^ 2))) t :=
    HasDerivAt.exp hC
  -- product rule: gaussianHeatKernel s x = A(s) * B(s)
  have h_product := HasDerivAt.mul hA hB
  -- h_product : HasDerivAt (A * B) (A' * B(t) + A(t) * B') t
  -- verify the derivative expression matches the target
  have h_deriv_eq : (-(1 / (2 * t)) * (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2)) * Real.exp (-(x ^ 2) / (4 * t)) +
      (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) * (Real.exp (-(x ^ 2) / (4 * t)) * (x ^ 2 / (4 * t ^ 2))) =
      ((x ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * gaussianHeatKernel t x) := by
    dsimp [gaussianHeatKernel]
    ring
  rw [h_deriv_eq] at h_product
  simpa [gaussianHeatKernel] using h_product

/-- **Kernel solves the heat equation pointwise.** The second spatial derivative and the
time derivative of the kernel produce the same value. -/
theorem kernel_heat_identity (x : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun z : ℝ => -(z / (2 * t)) * gaussianHeatKernel t z)
        ((x ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * gaussianHeatKernel t x) x ∧
      HasDerivAt (fun s : ℝ => gaussianHeatKernel s x)
        ((x ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * gaussianHeatKernel t x) t := by
  exact ⟨kernel_hasDerivAt_space_second ht x, kernel_hasDerivAt_time x ht⟩

/-! ### Gaussian domination bounds -/

/-- **Absolute-value-times-Gaussian is integrable.** -/
theorem integrable_abs_mul_gaussian {c : ℝ} (hc : 0 < c) :
    Integrable (fun y : ℝ => |y| * Real.exp (-c * y ^ 2)) := by
  have h_int : Integrable (fun y : ℝ => y * Real.exp (-c * y ^ 2)) :=
    integrable_mul_exp_neg_mul_sq hc
  have h_eq : (fun y : ℝ => |y| * Real.exp (-c * y ^ 2)) =
      (fun y : ℝ => |y * Real.exp (-c * y ^ 2)|) := by
    ext y
    calc
      |y| * Real.exp (-c * y ^ 2) = |y| * |Real.exp (-c * y ^ 2)| := by
        simp
      _ = |y * Real.exp (-c * y ^ 2)| := by rw [abs_mul]
  rw [h_eq]
  exact h_int.abs

/-- **Square-times-Gaussian is integrable.** -/
theorem integrable_sq_mul_gaussian {c : ℝ} (hc : 0 < c) :
    Integrable (fun y : ℝ => y ^ 2 * Real.exp (-c * y ^ 2)) := by
  have h_int : Integrable (fun y : ℝ => y ^ (2 : ℝ) * Real.exp (-c * y ^ 2)) :=
    integrable_rpow_mul_exp_neg_mul_sq hc (by norm_num : (-1 : ℝ) < (2 : ℝ))
  simpa [Real.rpow_two] using h_int

/-- **Polynomial-times-Gaussian is integrable (centered case).** -/
theorem gaussian_poly_integrable_zero {c : ℝ} (hc : 0 < c) {a b d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) :
    Integrable (fun y : ℝ => (a + b * |y| + d * y ^ 2) * Real.exp (-c * y ^ 2)) := by
  have h_exp : Integrable (fun y : ℝ => Real.exp (-c * y ^ 2)) :=
    integrable_exp_neg_mul_sq hc
  have h_abs : Integrable (fun y : ℝ => |y| * Real.exp (-c * y ^ 2)) :=
    integrable_abs_mul_gaussian hc
  have h_sq : Integrable (fun y : ℝ => y ^ 2 * Real.exp (-c * y ^ 2)) :=
    integrable_sq_mul_gaussian hc
  simpa [mul_add, add_mul, mul_assoc, add_assoc] using
    (h_exp.const_mul a).add ((h_abs.const_mul b).add (h_sq.const_mul d))

/-- **Shifted polynomial-times-Gaussian is integrable.** -/
theorem shifted_gaussian_integrable (x₀ : ℝ) {c : ℝ} (hc : 0 < c) {a b d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) :
    Integrable (fun y : ℝ =>
      (a + b * |y - x₀| + d * (y - x₀) ^ 2) * Real.exp (-c * (y - x₀) ^ 2)) := by
  refine (gaussian_poly_integrable_zero hc ha hb hd).comp_sub_right x₀

/-- **A uniform quadratic lower bound.** -/
theorem gaussian_quadratic_lower_bound {x x₀ : ℝ} (h : |x - x₀| ≤ 1) (y : ℝ) :
    (1 / 2) * (y - x₀) ^ 2 - 2 ≤ (x - y) ^ 2 := by
  have hsq : (x - x₀) ^ 2 ≤ 1 := by
    have h_abs : |x - x₀| ≤ |(1 : ℝ)| := by simpa [abs_one] using h
    have h' : (x - x₀) ^ 2 ≤ (1 : ℝ) ^ 2 := sq_le_sq.mpr h_abs
    simpa using h'
  have h_sq_nonneg : 0 ≤ ((x₀ - y) + 2 * (x - x₀)) ^ 2 := pow_two_nonneg _
  nlinarith

/-- **Gaussian exponential domination.** -/
theorem gaussian_exp_domination {x x₀ : ℝ} (h : |x - x₀| ≤ 1) {t : ℝ} (ht : 0 < t) (y : ℝ) :
    Real.exp (-((x - y) ^ 2) / (4 * t)) ≤
      Real.exp (1 / (2 * t)) * Real.exp (-((y - x₀) ^ 2) / (8 * t)) := by
  have hineq : (1/2 : ℝ) * (y - x₀) ^ 2 - 2 ≤ (x - y) ^ 2 :=
    gaussian_quadratic_lower_bound h y
  have hineq' : -((x - y) ^ 2) / (4 * t) ≤ -((y - x₀) ^ 2) / (8 * t) + 1 / (2 * t) := by
    have hpos : 8 * t ≠ 0 := by nlinarith
    field_simp [hpos]
    nlinarith
  calc
    Real.exp (-((x - y) ^ 2) / (4 * t)) ≤ Real.exp (-((y - x₀) ^ 2) / (8 * t) + 1 / (2 * t)) :=
      Real.exp_le_exp.mpr hineq'
    _ = Real.exp (-((y - x₀) ^ 2) / (8 * t)) * Real.exp (1 / (2 * t)) := by rw [Real.exp_add]
    _ = Real.exp (1 / (2 * t)) * Real.exp (-((y - x₀) ^ 2) / (8 * t)) := mul_comm _ _

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
  have hM_nonneg : 0 ≤ M := by
    have h0 := hf_bdd 0
    have h_abs_nonneg : 0 ≤ |f 0| := abs_nonneg _
    linarith
  set α := M / (2 * t) * (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) * Real.exp (1 / (2 * t)) with hα
  have hα_nonneg : 0 ≤ α := by
    dsimp [α]
    positivity
  set g := fun y : ℝ => α * (1 + |y - x₀|) * Real.exp (-((y - x₀) ^ 2) / (8 * t)) with hg_def
  have hg_int : Integrable g := by
    dsimp [g]
    have hc_pos : 0 < 1 / (8 * t) := by
      positivity
    have h_eq : (fun y : ℝ => α * (1 + |y - x₀|) * Real.exp (-((y - x₀) ^ 2) / (8 * t))) =
               (fun y : ℝ => (α + α * |y - x₀| + 0 * (y - x₀) ^ 2) *
                 Real.exp (-(1 / (8 * t)) * (y - x₀) ^ 2)) := by
      ext y
      have h_exp_eq : -((y - x₀) ^ 2) / (8 * t) = -(1 / (8 * t)) * (y - x₀) ^ 2 := by
        ring
      calc
        α * (1 + |y - x₀|) * Real.exp (-((y - x₀) ^ 2) / (8 * t))
            = (α + α * |y - x₀|) * Real.exp (-((y - x₀) ^ 2) / (8 * t)) := by ring
        _ = (α + α * |y - x₀|) * Real.exp (-(1 / (8 * t)) * (y - x₀) ^ 2) := by rw [h_exp_eq]
        _ = (α + α * |y - x₀| + 0 * (y - x₀) ^ 2) * Real.exp (-(1 / (8 * t)) * (y - x₀) ^ 2) := by ring
    rw [h_eq]
    refine shifted_gaussian_integrable x₀ (by positivity) hα_nonneg hα_nonneg (by norm_num)
  refine ⟨g, hg_int, λ x hx y => ?_⟩
  have h_bound := bound_space_pointwise hf_bdd ht x₀ hx y
  simpa [g, α] using h_bound

/-- **Pointwise estimate for the second spatial derivative.** -/
theorem bound_space_second_pointwise {f : ℝ → ℝ} {M : ℝ} (hf_bdd : ∀ x, |f x| ≤ M)
    {t : ℝ} (ht : 0 < t) (x₀ : ℝ) {x : ℝ} (hx : |x - x₀| ≤ 1) (y : ℝ) :
    |((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * gaussianHeatKernel t (x - y) * f y| ≤
      M * (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) * Real.exp (1 / (2 * t)) *
        ((1 + |y - x₀|) ^ 2 / (4 * t ^ 2) + 1 / (2 * t)) *
        Real.exp (-((y - x₀) ^ 2) / (8 * t)) := by
  have hG_nonneg : 0 ≤ gaussianHeatKernel t (x - y) := by
    unfold gaussianHeatKernel; positivity
  have hM_nonneg : 0 ≤ M := by
    have := hf_bdd x₀
    linarith [abs_nonneg (f x₀), this]
  -- triangle inequality: |x-y| ≤ |x-x₀| + |x₀-y|
  have h_tri : |x - y| ≤ 1 + |y - x₀| := by
    have h_eq : (x - x₀) - (y - x₀) = x - y := by ring
    have h_abs_sub : |(x - x₀) - (y - x₀)| ≤ |x - x₀| + |y - x₀| := abs_sub (x - x₀) (y - x₀)
    have h_bound : |x - x₀| + |y - x₀| ≤ 1 + |y - x₀| := by nlinarith
    calc
      |x - y| = |(x - x₀) - (y - x₀)| := by rw [h_eq]
      _ ≤ |x - x₀| + |y - x₀| := h_abs_sub
      _ ≤ 1 + |y - x₀| := h_bound
  -- square both sides (both nonnegative) and use (x-y)^2 = |x-y|^2
  have h_sq_bound : (x - y) ^ 2 ≤ (1 + |y - x₀|) ^ 2 := by
    have h_nonneg_abs : 0 ≤ |x - y| := abs_nonneg _
    have h_nonneg_sum : 0 ≤ 1 + |y - x₀| := by positivity
    have h_sq_abs : |x - y| ^ 2 ≤ (1 + |y - x₀|) ^ 2 := by
      simpa [pow_two] using mul_self_le_mul_self h_nonneg_abs h_tri
    simpa [sq_abs] using h_sq_abs
  -- bound |(x-y)^2/(4t^2) - 1/(2t)|
  have h_quad_bound : |(x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)| ≤
      (1 + |y - x₀|) ^ 2 / (4 * t ^ 2) + 1 / (2 * t) := by
    have h_sum_nonneg : 0 ≤ (x - y) ^ 2 / (4 * t ^ 2) := by positivity
    have h_t_pos : 0 ≤ 1 / (2 * t) := by positivity
    calc
      |(x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)| ≤
          |(x - y) ^ 2 / (4 * t ^ 2)| + |1 / (2 * t)| := abs_sub _ _
      _ = (x - y) ^ 2 / (4 * t ^ 2) + 1 / (2 * t) := by
        rw [abs_of_nonneg h_sum_nonneg, abs_of_nonneg h_t_pos]
      _ ≤ (1 + |y - x₀|) ^ 2 / (4 * t ^ 2) + 1 / (2 * t) := by
        have htemp : (x - y) ^ 2 / (4 * t ^ 2) ≤ (1 + |y - x₀|) ^ 2 / (4 * t ^ 2) := by
          gcongr
        nlinarith
  -- exponential bound from gaussian_exp_domination
  have h_exp_bound : Real.exp (-((x - y) ^ 2) / (4 * t)) ≤
      Real.exp (1 / (2 * t)) * Real.exp (-((y - x₀) ^ 2) / (8 * t)) :=
    gaussian_exp_domination hx ht y
  -- constant prefactor nonnegative
  have h_C_nonneg : 0 ≤ (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) := by
    positivity
  -- full prefactor (constant * exp) bound
  have h_prefactor_bound : (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) * Real.exp (-((x - y) ^ 2) / (4 * t)) ≤
      (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) * (Real.exp (1 / (2 * t)) * Real.exp (-((y - x₀) ^ 2) / (8 * t))) :=
    mul_le_mul_of_nonneg_left h_exp_bound h_C_nonneg
  -- auxiliary nonnegativity result for the quad factor
  have hQ_nonneg : 0 ≤ ((1 + |y - x₀|) ^ 2 / (4 * t ^ 2) + 1 / (2 * t)) := by positivity
  -- main calculation
  have h_abs_nonneg : 0 ≤ |(x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)| := abs_nonneg _
  have h_prod_nonneg : 0 ≤ |(x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)| * gaussianHeatKernel t (x - y) :=
    mul_nonneg h_abs_nonneg hG_nonneg
  calc
    |((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * gaussianHeatKernel t (x - y) * f y|
        = |((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * gaussianHeatKernel t (x - y)| * |f y| := by
      rw [abs_mul]
    _ = |((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t))| * |gaussianHeatKernel t (x - y)| * |f y| := by rw [abs_mul]
    _ = |((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t))| * gaussianHeatKernel t (x - y) * |f y| := by
      rw [abs_of_nonneg hG_nonneg]
    _ ≤ |((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t))| * gaussianHeatKernel t (x - y) * M := by
      refine mul_le_mul_of_nonneg_left (hf_bdd y) ?_
      -- need 0 ≤ |A| * G
      exact mul_nonneg (abs_nonneg _) hG_nonneg
    _ ≤ ((1 + |y - x₀|) ^ 2 / (4 * t ^ 2) + 1 / (2 * t)) * gaussianHeatKernel t (x - y) * M := by
      have hGM_nonneg : 0 ≤ gaussianHeatKernel t (x - y) * M := mul_nonneg hG_nonneg hM_nonneg
      calc
        |(x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)| * gaussianHeatKernel t (x - y) * M
            = (|(x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)| * gaussianHeatKernel t (x - y)) * M := by ring
        _ = |(x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)| * (gaussianHeatKernel t (x - y) * M) := by ring
        _ ≤ ((1 + |y - x₀|) ^ 2 / (4 * t ^ 2) + 1 / (2 * t)) * (gaussianHeatKernel t (x - y) * M) :=
          mul_le_mul_of_nonneg_right h_quad_bound hGM_nonneg
        _ = ((1 + |y - x₀|) ^ 2 / (4 * t ^ 2) + 1 / (2 * t)) * gaussianHeatKernel t (x - y) * M := by ring
    _ = M * ((1 + |y - x₀|) ^ 2 / (4 * t ^ 2) + 1 / (2 * t)) * gaussianHeatKernel t (x - y) := by ring
    _ = M * ((1 + |y - x₀|) ^ 2 / (4 * t ^ 2) + 1 / (2 * t)) *
        ((4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) * Real.exp (-((x - y) ^ 2) / (4 * t))) := by
      simp [gaussianHeatKernel]
    _ ≤ M * ((1 + |y - x₀|) ^ 2 / (4 * t ^ 2) + 1 / (2 * t)) *
        ((4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) * (Real.exp (1 / (2 * t)) * Real.exp (-((y - x₀) ^ 2) / (8 * t)))) := by
      have hL_nonneg : 0 ≤ M * ((1 + |y - x₀|) ^ 2 / (4 * t ^ 2) + 1 / (2 * t)) :=
        mul_nonneg hM_nonneg hQ_nonneg
      exact mul_le_mul_of_nonneg_left h_prefactor_bound hL_nonneg
    _ = M * (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) * Real.exp (1 / (2 * t)) *
        ((1 + |y - x₀|) ^ 2 / (4 * t ^ 2) + 1 / (2 * t)) *
        Real.exp (-((y - x₀) ^ 2) / (8 * t)) := by ring

/-- **Uniform domination of the second spatial derivative.** -/
theorem bound_space_second {f : ℝ → ℝ} {M : ℝ} (hf_bdd : ∀ x, |f x| ≤ M)
    {t : ℝ} (ht : 0 < t) (x₀ : ℝ) :
    ∃ g : ℝ → ℝ, Integrable g ∧
      ∀ x : ℝ, |x - x₀| ≤ 1 → ∀ y : ℝ,
        |((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * gaussianHeatKernel t (x - y) * f y| ≤ g y := by
  have hM_nonneg : 0 ≤ M := by
    have h0 : |f 0| ≤ M := hf_bdd 0
    have hpos : 0 ≤ |f 0| := abs_nonneg _
    linarith
  set C := M * (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) * Real.exp (1 / (2 * t)) with hC
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  set g := fun y : ℝ => C * (((1 + |y - x₀|) ^ 2) / (4 * t ^ 2) + 1 / (2 * t)) *
    Real.exp (-((y - x₀) ^ 2) / (8 * t)) with hg
  have hg_int : Integrable g := by
    rw [hg]
    set d := C / (4 * t ^ 2) with hd
    set b := C / (2 * t ^ 2) with hb
    set a := C * (1 / (4 * t ^ 2) + 1 / (2 * t)) with ha
    have hd_nonneg : 0 ≤ d := div_nonneg hC_nonneg (by positivity)
    have hb_nonneg : 0 ≤ b := div_nonneg hC_nonneg (by positivity)
    have ha_nonneg : 0 ≤ a := mul_nonneg hC_nonneg (by positivity)
    have hc_pos : 0 < 1 / (8 * t) := by positivity
    have h_eq : (fun y : ℝ => C * (((1 + |y - x₀|) ^ 2) / (4 * t ^ 2) + 1 / (2 * t)) *
        Real.exp (-((y - x₀) ^ 2) / (8 * t))) =
      (fun y : ℝ => (a + b * |y - x₀| + d * (y - x₀) ^ 2) *
        Real.exp (-((1 / (8 * t)) * (y - x₀) ^ 2))) := by
      ext y
      dsimp [a, b, d]
      have h_exp_eq : Real.exp (-((y - x₀) ^ 2) / (8 * t)) = Real.exp (-((1 / (8 * t)) * (y - x₀) ^ 2)) := by
        congr 1
        ring
      rw [h_exp_eq]
      have h_coeff : C * (((1 + |y - x₀|) ^ 2) / (4 * t ^ 2) + 1 / (2 * t)) =
          C * (1 / (4 * t ^ 2) + 1 / (2 * t)) + C / (2 * t ^ 2) * |y - x₀| + C / (4 * t ^ 2) * (y - x₀) ^ 2 := by
        field_simp [show t ≠ 0 from by linarith]
        nlinarith [sq_abs (y - x₀)]
      rw [h_coeff]
    rw [h_eq]
    simpa [mul_assoc] using shifted_gaussian_integrable x₀ hc_pos ha_nonneg hb_nonneg hd_nonneg
  have h_bound : ∀ x : ℝ, |x - x₀| ≤ 1 → ∀ y : ℝ,
      |((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * gaussianHeatKernel t (x - y) * f y| ≤ g y := by
    intro x hx y
    have h_pt := bound_space_second_pointwise hf_bdd ht x₀ hx y
    dsimp [g, C]
    simpa [mul_assoc] using h_pt
  exact ⟨g, hg_int, h_bound⟩

/-- **Pointwise estimate for the time derivative.** -/
theorem bound_time_pointwise {f : ℝ → ℝ} {M : ℝ} (hf_bdd : ∀ x, |f x| ≤ M)
    {t₀ : ℝ} (ht₀ : 0 < t₀) (x₀ : ℝ) {s : ℝ} (hs : s ∈ Set.Ioo (t₀ / 2) (2 * t₀)) (y : ℝ) :
    |((x₀ - y) ^ 2 / (4 * s ^ 2) - 1 / (2 * s)) * gaussianHeatKernel s (x₀ - y) * f y| ≤
      M * (2 * Real.pi * t₀)⁻¹ ^ ((1 : ℝ) / 2) *
        ((x₀ - y) ^ 2 / t₀ ^ 2 + 1 / t₀) *
        Real.exp (-((x₀ - y) ^ 2) / (8 * t₀)) := by
  rcases hs with ⟨hs_left, hs_right⟩
  have hs_pos : 0 < s := by linarith
  have hM_nonneg : 0 ≤ M := by
    have h0 : |f 0| ≤ M := hf_bdd 0
    have h0_nonneg : 0 ≤ |f 0| := abs_nonneg _
    linarith
  set h := x₀ - y with hh

  -- gaussianHeatKernel s h > 0
  have h_kernel_pos : 0 < gaussianHeatKernel s h := by
    dsimp [gaussianHeatKernel]
    positivity

  have h_kernel_nonneg : 0 ≤ gaussianHeatKernel s h := by linarith

  -- Decompose the absolute value
  have h_abs_factor : |((x₀ - y) ^ 2 / (4 * s ^ 2) - 1 / (2 * s)) * gaussianHeatKernel s (x₀ - y) * f y| =
      |h ^ 2 / (4 * s ^ 2) - 1 / (2 * s)| * gaussianHeatKernel s h * |f y| := by
    calc
      |((x₀ - y) ^ 2 / (4 * s ^ 2) - 1 / (2 * s)) * gaussianHeatKernel s (x₀ - y) * f y| =
          |((h ^ 2 / (4 * s ^ 2) - 1 / (2 * s)) * gaussianHeatKernel s h * f y)| := by
        dsimp [h]
      _ = |(h ^ 2 / (4 * s ^ 2) - 1 / (2 * s)) * gaussianHeatKernel s h| * |f y| := by rw [abs_mul]
      _ = |h ^ 2 / (4 * s ^ 2) - 1 / (2 * s)| * |gaussianHeatKernel s h| * |f y| := by rw [abs_mul]
      _ = |h ^ 2 / (4 * s ^ 2) - 1 / (2 * s)| * gaussianHeatKernel s h * |f y| := by
        rw [abs_of_pos h_kernel_pos]

  -- Polynomial bound via triangle inequality
  have h_poly_bound : |h ^ 2 / (4 * s ^ 2) - 1 / (2 * s)| ≤ h ^ 2 / t₀ ^ 2 + 1 / t₀ := by
    calc
      |h ^ 2 / (4 * s ^ 2) - 1 / (2 * s)| ≤ |h ^ 2 / (4 * s ^ 2)| + |1 / (2 * s)| := abs_sub _ _
      _ = h ^ 2 / (4 * s ^ 2) + 1 / (2 * s) := by
        rw [abs_of_nonneg (by positivity : 0 ≤ h ^ 2 / (4 * s ^ 2))]
        rw [abs_of_nonneg (by positivity : 0 ≤ 1 / (2 * s))]
      _ ≤ h ^ 2 / t₀ ^ 2 + 1 / t₀ := by
        have h1 : h ^ 2 / (4 * s ^ 2) ≤ h ^ 2 / t₀ ^ 2 := by
          by_cases hzero : h = 0
          · simp [hzero]
          · have hsq_pos : 0 < h ^ 2 := sq_pos_iff.mpr hzero
            have h_denom_sq : 4 * s ^ 2 ≥ t₀ ^ 2 := by nlinarith
            calc
              h ^ 2 / (4 * s ^ 2) = h ^ 2 * (1 / (4 * s ^ 2)) := by ring
              _ ≤ h ^ 2 * (1 / t₀ ^ 2) := by
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                exact (one_div_le_one_div (by positivity) (by positivity)).mpr h_denom_sq
              _ = h ^ 2 / t₀ ^ 2 := by ring
        have h2 : 1 / (2 * s) ≤ 1 / t₀ := by
          have h_denom : 2 * s ≥ t₀ := by linarith
          exact (one_div_le_one_div (by positivity) (by positivity)).mpr h_denom
        nlinarith

  -- Prefactor bound: (4πs)⁻¹ ^ (1/2) ≤ (2πt₀)⁻¹ ^ (1/2)
  have h_prefactor : (4 * Real.pi * s)⁻¹ ^ ((1 : ℝ) / 2) ≤ (2 * Real.pi * t₀)⁻¹ ^ ((1 : ℝ) / 2) := by
    have h_inv_ineq : (4 * Real.pi * s)⁻¹ ≤ (2 * Real.pi * t₀)⁻¹ := by
      have h_base_ineq : 2 * Real.pi * t₀ ≤ 4 * Real.pi * s := by
        have : t₀ < 2 * s := by linarith
        nlinarith [Real.pi_pos]
      simpa [one_div] using
        (one_div_le_one_div (by positivity : 0 < 4 * Real.pi * s) (by positivity : 0 < 2 * Real.pi * t₀)).mpr h_base_ineq
    have h_exp_nonneg : 0 ≤ (1 : ℝ) / 2 := by norm_num
    exact Real.rpow_le_rpow (by positivity) h_inv_ineq h_exp_nonneg

  -- Exponential bound: exp(-h²/(4s)) ≤ exp(-h²/(8t₀))
  have h_exp_bound : Real.exp (-(h ^ 2) / (4 * s)) ≤ Real.exp (-(h ^ 2) / (8 * t₀)) := by
    refine Real.exp_le_exp.mpr ?_
    by_cases hzero : h = 0
    · simp [hzero]
    · have hsq_pos : 0 < h ^ 2 := sq_pos_iff.mpr hzero
      have h_div_ineq : 1 / (8 * t₀) ≤ 1 / (4 * s) :=
        (one_div_le_one_div (by positivity : 0 < 8 * t₀) (by positivity : 0 < 4 * s)).mpr (by nlinarith)
      have h_sq_ineq : h ^ 2 / (8 * t₀) ≤ h ^ 2 / (4 * s) := by
        calc
          h ^ 2 / (8 * t₀) = h ^ 2 * (1 / (8 * t₀)) := by ring
          _ ≤ h ^ 2 * (1 / (4 * s)) := mul_le_mul_of_nonneg_left h_div_ineq (by positivity)
          _ = h ^ 2 / (4 * s) := by ring
      calc
        -(h ^ 2) / (4 * s) = -((h ^ 2) / (4 * s)) := by ring
        _ ≤ -((h ^ 2) / (8 * t₀)) := neg_le_neg h_sq_ineq
        _ = -(h ^ 2) / (8 * t₀) := by ring

  -- Put it all together
  calc
    |((x₀ - y) ^ 2 / (4 * s ^ 2) - 1 / (2 * s)) * gaussianHeatKernel s (x₀ - y) * f y| =
        |h ^ 2 / (4 * s ^ 2) - 1 / (2 * s)| * gaussianHeatKernel s h * |f y| := h_abs_factor
    _ = |f y| * (|h ^ 2 / (4 * s ^ 2) - 1 / (2 * s)| * gaussianHeatKernel s h) := by ring
    _ ≤ M * (|h ^ 2 / (4 * s ^ 2) - 1 / (2 * s)| * gaussianHeatKernel s h) :=
      mul_le_mul_of_nonneg_right (hf_bdd y) (mul_nonneg (abs_nonneg _) h_kernel_nonneg)
    _ = |h ^ 2 / (4 * s ^ 2) - 1 / (2 * s)| * gaussianHeatKernel s h * M := by ring
    _ = (|h ^ 2 / (4 * s ^ 2) - 1 / (2 * s)| * gaussianHeatKernel s h) * M := by ring
    _ ≤ ((h ^ 2 / t₀ ^ 2 + 1 / t₀) * gaussianHeatKernel s h) * M := by
      refine mul_le_mul_of_nonneg_right ?_ hM_nonneg
      refine mul_le_mul_of_nonneg_right h_poly_bound h_kernel_nonneg
    _ = (h ^ 2 / t₀ ^ 2 + 1 / t₀) * gaussianHeatKernel s h * M := by ring
    _ = (h ^ 2 / t₀ ^ 2 + 1 / t₀) * ((4 * Real.pi * s)⁻¹ ^ ((1 : ℝ) / 2) * Real.exp (-(h ^ 2) / (4 * s))) * M := rfl
    _ = (h ^ 2 / t₀ ^ 2 + 1 / t₀) * ((4 * Real.pi * s)⁻¹ ^ ((1 : ℝ) / 2) * Real.exp (-(h ^ 2) / (4 * s)) * M) := by ring
    _ ≤ (h ^ 2 / t₀ ^ 2 + 1 / t₀) * (((2 * Real.pi * t₀)⁻¹ ^ ((1 : ℝ) / 2)) * Real.exp (-(h ^ 2) / (8 * t₀)) * M) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity : 0 ≤ h ^ 2 / t₀ ^ 2 + 1 / t₀)
      have h_mul : (4 * Real.pi * s)⁻¹ ^ ((1 : ℝ) / 2) * Real.exp (-(h ^ 2) / (4 * s)) ≤
                 (2 * Real.pi * t₀)⁻¹ ^ ((1 : ℝ) / 2) * Real.exp (-(h ^ 2) / (8 * t₀)) := by
        refine mul_le_mul h_prefactor h_exp_bound (by positivity) (by positivity)
      refine mul_le_mul_of_nonneg_right h_mul hM_nonneg
    _ = (h ^ 2 / t₀ ^ 2 + 1 / t₀) * ((2 * Real.pi * t₀)⁻¹ ^ ((1 : ℝ) / 2) * Real.exp (-(h ^ 2) / (8 * t₀))) * M := by ring
    _ = M * (2 * Real.pi * t₀)⁻¹ ^ ((1 : ℝ) / 2) * (h ^ 2 / t₀ ^ 2 + 1 / t₀) *
        Real.exp (-(h ^ 2) / (8 * t₀)) := by ring
    _ = M * (2 * Real.pi * t₀)⁻¹ ^ ((1 : ℝ) / 2) * ((x₀ - y) ^ 2 / t₀ ^ 2 + 1 / t₀) *
        Real.exp (-((x₀ - y) ^ 2) / (8 * t₀)) := by simp [h]

/-- **Uniform domination of the time derivative.** -/
theorem bound_time {f : ℝ → ℝ} {M : ℝ} (hf_bdd : ∀ x, |f x| ≤ M)
    {t₀ : ℝ} (ht₀ : 0 < t₀) (x₀ : ℝ) :
    ∃ g : ℝ → ℝ, Integrable g ∧
      ∀ s : ℝ, s ∈ Set.Ioo (t₀ / 2) (2 * t₀) → ∀ y : ℝ,
        |((x₀ - y) ^ 2 / (4 * s ^ 2) - 1 / (2 * s)) * gaussianHeatKernel s (x₀ - y) * f y| ≤ g y := by
  set g := fun y : ℝ => M * (2 * Real.pi * t₀)⁻¹ ^ ((1 : ℝ) / 2) *
    ((x₀ - y) ^ 2 / t₀ ^ 2 + 1 / t₀) * Real.exp (-((x₀ - y) ^ 2) / (8 * t₀)) with hg_def
  have hg_bound : ∀ s : ℝ, s ∈ Set.Ioo (t₀ / 2) (2 * t₀) → ∀ y : ℝ,
    |((x₀ - y) ^ 2 / (4 * s ^ 2) - 1 / (2 * s)) * gaussianHeatKernel s (x₀ - y) * f y| ≤ g y := by
    intro s hs y
    dsimp [g]
    exact bound_time_pointwise hf_bdd ht₀ x₀ hs y
  have hg_int : Integrable g := by
    dsimp [g]
    have hc : 0 < 1 / (8 * t₀) := by
      refine div_pos (by norm_num) (mul_pos (by norm_num) ht₀)
    have ha : 0 ≤ 1 / t₀ := by
      have ht₀' : 0 ≤ t₀ := by linarith
      exact div_nonneg (by norm_num) ht₀'
    have hb : 0 ≤ (0 : ℝ) := by norm_num
    have hd : 0 ≤ 1 / (t₀ ^ 2) := by
      have ht₀_sq_nonneg : 0 ≤ t₀ ^ 2 := pow_two_nonneg t₀
      exact div_nonneg (by norm_num) ht₀_sq_nonneg
    have h_int_core : Integrable (fun y : ℝ => ((x₀ - y) ^ 2 / t₀ ^ 2 + 1 / t₀) *
      Real.exp (-((x₀ - y) ^ 2) / (8 * t₀))) := by
      have h_eq : (fun y : ℝ => ((x₀ - y) ^ 2 / t₀ ^ 2 + 1 / t₀) *
        Real.exp (-((x₀ - y) ^ 2) / (8 * t₀))) =
        (fun y : ℝ => ((1 / t₀) + (0 : ℝ) * |y - x₀| + (1 / (t₀ ^ 2)) * (y - x₀) ^ 2) *
          Real.exp (-(1 / (8 * t₀)) * (y - x₀) ^ 2)) := by
        ext y
        have ht₀_ne : t₀ ≠ 0 := by linarith
        have h_poly : (x₀ - y) ^ 2 / t₀ ^ 2 + 1 / t₀ = 1 / t₀ + (1 / (t₀ ^ 2)) * (y - x₀) ^ 2 := by
          field_simp [ht₀_ne]
          ring
        have h_exp : -((x₀ - y) ^ 2) / (8 * t₀) = -(1 / (8 * t₀)) * (y - x₀) ^ 2 := by
          field_simp [ht₀_ne]
          ring
        calc
          ((x₀ - y) ^ 2 / t₀ ^ 2 + 1 / t₀) * Real.exp (-((x₀ - y) ^ 2) / (8 * t₀))
              = (1 / t₀ + (1 / (t₀ ^ 2)) * (y - x₀) ^ 2) *
                Real.exp (-((x₀ - y) ^ 2) / (8 * t₀)) := by rw [h_poly]
          _ = (1 / t₀ + (1 / (t₀ ^ 2)) * (y - x₀) ^ 2) *
              Real.exp (-(1 / (8 * t₀)) * (y - x₀) ^ 2) := by rw [h_exp]
          _ = ((1 / t₀) + (0 : ℝ) * |y - x₀| + (1 / (t₀ ^ 2)) * (y - x₀) ^ 2) *
              Real.exp (-(1 / (8 * t₀)) * (y - x₀) ^ 2) := by ring
      rw [h_eq]
      exact shifted_gaussian_integrable x₀ hc ha hb hd
    have hM_nonneg : 0 ≤ M := by
      have h0 := hf_bdd x₀
      have h_abs_nonneg : 0 ≤ |f x₀| := abs_nonneg _
      linarith
    have h_pref_nonneg : 0 ≤ (2 * Real.pi * t₀)⁻¹ ^ ((1 : ℝ) / 2) := by
      have hpos : 0 < (2 * Real.pi * t₀)⁻¹ := by
        refine inv_pos.mpr (mul_pos (mul_pos (by norm_num) Real.pi_pos) ht₀)
      have hpos_rpow : 0 < ((2 * Real.pi * t₀)⁻¹ : ℝ) ^ ((1 : ℝ) / 2) :=
        Real.rpow_pos_of_pos hpos _
      exact hpos_rpow.le
    simpa [mul_assoc] using
      h_int_core.const_mul (M * (2 * Real.pi * t₀)⁻¹ ^ ((1 : ℝ) / 2))
  exact ⟨g, hg_int, hg_bound⟩

/-! ### Differentiation under the integral sign -/

/-- **Shifted, scaled kernel has a derivative.** -/
theorem shift_scale_hasDerivAt {k : ℝ → ℝ} {y c d v : ℝ} (hk : HasDerivAt k d (c - y)) :
    HasDerivAt (fun z : ℝ => k (z - y) * v) (d * v) c :=
  (hk.comp_sub_const c y).mul_const v

/-- **Integrand is a.e. strongly measurable.** -/
theorem shift_scale_aestronglyMeasurable {k : ℝ → ℝ} (hk : Continuous k)
    {f : ℝ → ℝ} (hf : Continuous f) (z : ℝ) :
    AEStronglyMeasurable (fun y : ℝ => k (z - y) * f y) volume := by
  have h_cont : Continuous (fun y : ℝ => k (z - y) * f y) := by
    refine (hk.comp ?_).mul hf
    exact continuous_const.sub continuous_id
  exact h_cont.aestronglyMeasurable

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
  -- Rewrite heatSolution as an integral against the kernel
  have h_eq : (fun z : ℝ => heatSolution f t z) = (fun z : ℝ =>
      ∫ y : ℝ, gaussianHeatKernel t (z - y) * f y) := by
    ext z
    rw [heatSolution_eq_kernel_integral f ht z]
  rw [h_eq]
  -- Set up the integrand and its derivative
  set F := fun (r y : ℝ) => gaussianHeatKernel t (r - y) * f y with hF_def
  set F' := fun (r y : ℝ) => -((r - y) / (2 * t)) * gaussianHeatKernel t (r - y) * f y with hF'_def
  set s := Metric.closedBall x 1 with hs_def
  have hs : s ∈ nhds x := by
    simpa [hs_def] using Metric.closedBall_mem_nhds x (by norm_num : (0 : ℝ) < 1)
  -- Obtain the integrable dominating function g from bound_space
  rcases bound_space hf_bdd ht x with ⟨g, hg_int, h_bound⟩
  -- Hypothesis (1): integrability of F at the base point x
  have hF₀ : Integrable (fun y => F x y) := by
    dsimp [F]
    exact kernel_integrand_integrable hf_cont hf_bdd ht x
  -- Hypothesis (2): a.e. strong measurability of F(r,·) for each r ∈ s
  have hk_cont : Continuous (gaussianHeatKernel t) := by
    unfold gaussianHeatKernel
    refine (continuous_const.mul ?_)
    refine Real.continuous_exp.comp ?_
    have : (fun z : ℝ => -(z ^ 2) / (4 * t)) = (fun z : ℝ => (-(1 : ℝ) / (4 * t)) * (z ^ 2)) := by
      ext z; ring
    rw [this]
    exact continuous_const.mul (continuous_id.pow 2)
  have hmeas : ∀ r ∈ s, AEStronglyMeasurable (fun y => F r y) volume := by
    intro r hr
    dsimp [F]
    exact shift_scale_aestronglyMeasurable hk_cont hf_cont r
  -- Hypothesis (3): uniform domination bound
  have hbound' : ∀ y : ℝ, ∀ r ∈ s, |F' r y| ≤ g y := by
    intro y r hr
    dsimp [F']
    have hdist : dist r x ≤ 1 := Metric.mem_closedBall.mp hr
    have hx : |r - x| ≤ 1 := by simpa [dist_eq] using hdist
    exact h_bound r hx y
  -- Hypothesis (4): pointwise derivative
  have hderiv : ∀ y : ℝ, ∀ r ∈ s, HasDerivAt (fun r' => F r' y) (F' r y) r := by
    intro y r hr
    dsimp [F, F']
    have hk_deriv : HasDerivAt (gaussianHeatKernel t)
        (-((r - y) / (2 * t)) * gaussianHeatKernel t (r - y)) (r - y) :=
      kernel_hasDerivAt_space ht (r - y)
    exact shift_scale_hasDerivAt hk_deriv
  -- Apply the Leibniz rule
  have h_result := hasDerivAt_under_integral hs hg_int hF₀ hmeas hbound' hderiv
  exact h_result.2

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
  have h_mem : Set.Ioi (0 : ℝ) ∈ nhds t :=
    isOpen_Ioi.mem_nhds ht
  refine Filter.eventuallyEq_of_mem h_mem ?_
  intro s hs
  have hs_pos : 0 < s := hs
  simpa using heatSolution_eq_kernel_integral f hs_pos x

/-- **Time derivative of the solution.** -/
lemma continuous_gaussianHeatKernel (t : ℝ) (ht : 0 < t) : Continuous (gaussianHeatKernel t) := by
  unfold gaussianHeatKernel
  have h_exp_cont : Continuous (fun (x : ℝ) => Real.exp (-(x ^ 2) / (4 * t))) := by
    refine Real.continuous_exp.comp ?_
    continuity
  exact (continuous_const.mul h_exp_cont)

theorem hasDerivAt_time {f : ℝ → ℝ} (hf_cont : Continuous f) {M : ℝ}
    (hf_bdd : ∀ x, |f x| ≤ M) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s : ℝ => heatSolution f s x)
      (∫ y : ℝ, ((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * gaussianHeatKernel t (x - y) * f y) t := by
  -- Transfer via eventual equality: it suffices to differentiate the kernel integral
  have h_eq : (fun s : ℝ => heatSolution f s x) =ᶠ[nhds t]
      fun s : ℝ => ∫ y : ℝ, gaussianHeatKernel s (x - y) * f y :=
    heatSolution_eventuallyEq_kernel_integral f ht x
  apply h_eq.hasDerivAt_iff.mpr
  -- Set up the neighborhood s_set = (t/2, 2*t)
  let s_set : Set ℝ := Set.Ioo (t/2) (2*t)
  have hs_set : s_set ∈ nhds t := by
    refine IsOpen.mem_nhds isOpen_Ioo ?_
    exact Set.mem_Ioo.mpr ⟨by nlinarith, by nlinarith⟩
  have hpos : ∀ s ∈ s_set, 0 < s := by
    intro s hs
    have hlow : t/2 < s := hs.1
    nlinarith
  -- The integrable bound from bound_time
  rcases bound_time hf_bdd ht x with ⟨g, hg_int, hg_bound⟩
  -- Define F(s, y) = gaussianHeatKernel s (x - y) * f y
  set F := fun (s y : ℝ) => gaussianHeatKernel s (x - y) * f y with hF
  set F' := fun (s y : ℝ) => ((x - y) ^ 2 / (4 * s ^ 2) - 1 / (2 * s)) * gaussianHeatKernel s (x - y) * f y with hF'
  -- Apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
  have hF_meas : ∀ᶠ s in nhds t, AEStronglyMeasurable (F s) volume := by
    filter_upwards [hs_set] with s hs
    have hs_pos : 0 < s := hpos s hs
    dsimp [F]
    exact shift_scale_aestronglyMeasurable (continuous_gaussianHeatKernel s hs_pos) hf_cont x
  have hF_int : Integrable (F t) volume := by
    dsimp [F]
    exact kernel_integrand_integrable hf_cont hf_bdd ht x
  have hF'_meas : AEStronglyMeasurable (F' t) volume := by
    dsimp [F']
    have h_cont : Continuous (fun y : ℝ => ((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) *
        gaussianHeatKernel t (x - y) * f y) := by
      have h_sq_cont : Continuous (fun (y : ℝ) => ((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) := by
        continuity
      have hG_cont : Continuous (fun (y : ℝ) => gaussianHeatKernel t (x - y)) :=
        (continuous_gaussianHeatKernel t ht).comp (continuous_const.sub continuous_id)
      exact (h_sq_cont.mul hG_cont).mul hf_cont
    exact h_cont.aestronglyMeasurable
  have h_bound : ∀ᵐ y ∂volume, ∀ s ∈ s_set, |F' s y| ≤ g y := by
    filter_upwards [] with y s hs
    dsimp [F']
    exact hg_bound s hs y
  have h_diff : ∀ᵐ y ∂volume, ∀ s ∈ s_set, HasDerivAt (fun r : ℝ => F r y) (F' s y) s := by
    filter_upwards [] with y s hs
    have hs_pos : 0 < s := hpos s hs
    dsimp [F, F']
    have hkernel_deriv : HasDerivAt (fun r : ℝ => gaussianHeatKernel r (x - y))
      (((x - y) ^ 2 / (4 * s ^ 2) - 1 / (2 * s)) * gaussianHeatKernel s (x - y)) s :=
      kernel_hasDerivAt_time (x - y) hs_pos
    simpa [mul_assoc] using hkernel_deriv.mul_const (f y)
  have h_result := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := s_set) (hs_set) (hF_meas) (hF_int) (hF'_meas) (h_bound) (hg_int) (h_diff)
  -- Extract the second component: HasDerivAt (fun s => ∫ y, F s y) (∫ y, F' t y) t
  exact h_result.2

/-- **Time derivative equals the second spatial derivative.** Both `hasDerivAt_time` and
`hasDerivAt_space_second` produce the same integral value. -/
theorem time_eq_space_second (f : ℝ → ℝ) (t x : ℝ) :
    (∫ y : ℝ, ((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * gaussianHeatKernel t (x - y) * f y) =
      ∫ y : ℝ, ((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * gaussianHeatKernel t (x - y) * f y :=
  rfl

/-! ### The PDE on `(0, ∞) × ℝ` -/

/-- **Heat equation half.** On `(0, ∞) × ℝ` the spatial first and second derivatives of
`heatSolution f` exist and the time derivative equals the second spatial derivative. -/
theorem pde_part {f : ℝ → ℝ} (hf_cont : Continuous f) {M : ℝ}
    (hf_bdd : ∀ x, |f x| ≤ M) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ∃ ux : ℝ → ℝ, ∃ uxx : ℝ,
      (∀ z : ℝ, HasDerivAt (fun z' => heatSolution f t z') (ux z) z) ∧
        HasDerivAt ux uxx x ∧
        HasDerivAt (fun s => heatSolution f s x) uxx t := by
  set ux : ℝ → ℝ := fun z => ∫ y : ℝ, -((z - y) / (2 * t)) * gaussianHeatKernel t (z - y) * f y with hux
  set uxx : ℝ := ∫ y : ℝ, ((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * gaussianHeatKernel t (x - y) * f y with huxx
  refine ⟨ux, uxx, ?_, ?_, ?_⟩
  · intro z
    simpa [hux] using hasDerivAt_space hf_cont hf_bdd ht z
  · simpa [hux, huxx] using hasDerivAt_space_second hf_cont hf_bdd ht x
  · simpa [huxx] using hasDerivAt_time hf_cont hf_bdd ht x

/-! ### Recovery of the initial datum as `t ↓ 0` -/

/-- **Total Gaussian mass.** -/
theorem gaussian_total_mass : ∫ z : ℝ, Real.exp (-z ^ 2) = Real.sqrt Real.pi := by
  have h := integral_gaussian (1 : ℝ)
  -- integral_gaussian b : ∫ x, exp(-b * x^2) = √(π / b)
  -- With b = 1: exp(-1*z^2) = exp(-z^2) and √(π/1) = √π
  simpa [one_mul, div_one] using h

/-- **Exponent simplifies under the scaling substitution.** -/
theorem gaussian_exponent_simplify {t : ℝ} (ht : 0 < t) (z : ℝ) :
    Real.exp (-((2 * Real.sqrt t * z) ^ 2) / (4 * t)) = Real.exp (-z ^ 2) := by
  have h_sq : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht.le
  calc
    Real.exp (-((2 * Real.sqrt t * z) ^ 2) / (4 * t))
        = Real.exp (-((4 * ((Real.sqrt t) ^ 2) * z ^ 2)) / (4 * t)) := by ring
    _ = Real.exp (-((4 * t * z ^ 2)) / (4 * t)) := by rw [h_sq]
    _ = Real.exp (-(z ^ 2)) := by
      field_simp [show t ≠ 0 from by linarith]

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
  rw [heatSolution_change_of_variables f ht x]
  have h_simplify : (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) * (2 * Real.sqrt t) = Real.pi⁻¹ ^ ((1 : ℝ) / 2) := by
    have h_nonneg_L : 0 ≤ (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) * (2 * Real.sqrt t) := by
      positivity
    have h_nonneg_R : 0 ≤ Real.pi⁻¹ ^ ((1 : ℝ) / 2) := by
      positivity
    have h_sq_eq : ((4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) * (2 * Real.sqrt t)) ^ 2 = (Real.pi⁻¹ ^ ((1 : ℝ) / 2)) ^ 2 := by
      calc
        ((4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) * (2 * Real.sqrt t)) ^ 2
            = ((4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2)) ^ 2 * (2 * Real.sqrt t) ^ 2 := by ring
        _ = ((4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) * ((2 * Real.sqrt t) ^ 2) := by norm_num
        _ = ((4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) * (4 * t) := by
          have h_sq : (2 * Real.sqrt t) ^ 2 = 4 * t := by
            calc
              (2 * Real.sqrt t) ^ 2 = 4 * (Real.sqrt t) ^ 2 := by ring
              _ = 4 * t := by rw [Real.sq_sqrt (by linarith : 0 ≤ t)]
          rw [h_sq]
        _ = ((4 * Real.pi * t)⁻¹) ^ (((1 : ℝ) / 2) * (2 : ℝ)) * (4 * t) := by
          rw [Real.rpow_mul (by positivity : 0 ≤ (4 * Real.pi * t)⁻¹) ((1 : ℝ) / 2) (2 : ℝ)]
        _ = ((4 * Real.pi * t)⁻¹) ^ (1 : ℝ) * (4 * t) := by
          have h_exp : ((1 : ℝ) / 2) * (2 : ℝ) = (1 : ℝ) := by ring
          rw [h_exp]
        _ = (4 * Real.pi * t)⁻¹ * (4 * t) := by simp
        _ = (Real.pi)⁻¹ := by
          field_simp [show t ≠ 0 from by linarith, (by positivity : Real.pi ≠ 0)]
        _ = (Real.pi⁻¹ ^ ((1 : ℝ) / 2)) ^ 2 := by
          calc
            (Real.pi)⁻¹ = (Real.pi⁻¹ ^ (1 : ℝ)) := by simp
            _ = (Real.pi⁻¹ ^ (((1 : ℝ) / 2) * (2 : ℝ))) := by
              congr 1; ring
            _ = (Real.pi⁻¹ ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) := by
              rw [Real.rpow_mul (by positivity : 0 ≤ Real.pi⁻¹) ((1 : ℝ) / 2) (2 : ℝ)]
            _ = (Real.pi⁻¹ ^ ((1 : ℝ) / 2)) ^ 2 := by norm_num
    exact (sq_eq_sq₀ h_nonneg_L h_nonneg_R).mp h_sq_eq
  rw [h_simplify]

/-- **Dominating bound for the substituted integrand.** -/
theorem subst_integrand_bound {f : ℝ → ℝ} {M : ℝ} (hf_bdd : ∀ x, |f x| ≤ M) (t x : ℝ) :
    (∀ z : ℝ, |Real.exp (-z ^ 2) * f (x - 2 * Real.sqrt t * z)| ≤ M * Real.exp (-z ^ 2)) ∧
      Integrable (fun z : ℝ => M * Real.exp (-z ^ 2)) := by
  refine ⟨?_, ?_⟩
  · intro z
    have h_exp_pos : 0 < Real.exp (-z ^ 2) := Real.exp_pos _
    have h_exp_nonneg : 0 ≤ Real.exp (-z ^ 2) := by linarith
    have h_f_bound : |f (x - 2 * Real.sqrt t * z)| ≤ M := hf_bdd _
    calc
      |Real.exp (-z ^ 2) * f (x - 2 * Real.sqrt t * z)|
          = |Real.exp (-z ^ 2)| * |f (x - 2 * Real.sqrt t * z)| := by rw [abs_mul]
      _ = Real.exp (-z ^ 2) * |f (x - 2 * Real.sqrt t * z)| := by
        rw [abs_of_pos h_exp_pos]
      _ ≤ Real.exp (-z ^ 2) * M := mul_le_mul_of_nonneg_left h_f_bound h_exp_nonneg
      _ = M * Real.exp (-z ^ 2) := mul_comm _ _
  · have h_int_exp : Integrable (fun z : ℝ => Real.exp (-z ^ 2)) := by
      have : (fun z : ℝ => Real.exp (-z ^ 2)) = (fun z : ℝ => Real.exp (-(1 : ℝ) * z ^ 2)) := by
        ext z; simp
      rw [this]
      exact integrable_exp_neg_mul_sq (b := 1) (by norm_num : (0 : ℝ) < 1)
    exact h_int_exp.const_mul M

/-- **Pointwise convergence of the substituted integrand** as `t ↓ 0`. -/
theorem subst_integrand_tendsto {f : ℝ → ℝ} (hf_cont : Continuous f) (x z : ℝ) :
    Filter.Tendsto (fun t : ℝ => Real.exp (-z ^ 2) * f (x - 2 * Real.sqrt t * z))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.exp (-z ^ 2) * f x)) := by
  -- sqrt t → 0 as t → 0⁺, because sqrt is continuous at 0
  have h_sqrt_tendsto' : Filter.Tendsto Real.sqrt (nhds 0) (nhds 0) := by
    simpa [Real.sqrt_zero] using Real.continuous_sqrt.tendsto 0
  have h_sqrt_tendsto : Filter.Tendsto Real.sqrt (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    h_sqrt_tendsto'.mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)) : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds (0 : ℝ))
  -- then 2 * sqrt t * z → 0
  have h_2sz_tendsto : Filter.Tendsto (fun t : ℝ => 2 * Real.sqrt t * z) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using h_sqrt_tendsto.const_mul (2 * z)
  -- so x - 2 * sqrt t * z → x
  have h_x_minus : Filter.Tendsto (fun t : ℝ => x - 2 * Real.sqrt t * z) (nhdsWithin 0 (Set.Ioi 0)) (nhds x) := by
    simpa [sub_zero] using
      Filter.Tendsto.sub (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => x) _ _) h_2sz_tendsto
  -- by continuity of f, f(x - 2*sqrt t*z) → f(x)
  have h_f : Filter.Tendsto (fun t : ℝ => f (x - 2 * Real.sqrt t * z)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (f x)) :=
    hf_cont.tendsto x |>.comp h_x_minus
  -- multiply by the constant exp(-z²)
  simpa using h_f.const_mul (Real.exp (-z ^ 2))

/-- **Gaussian integral of a constant.** -/
theorem gaussian_integral_const_mul (c : ℝ) :
    ∫ z : ℝ, Real.exp (-z ^ 2) * c = Real.sqrt Real.pi * c := by
  calc
    ∫ z : ℝ, Real.exp (-z ^ 2) * c = (∫ z : ℝ, Real.exp (-z ^ 2)) * c := by
      rw [integral_mul_const]
    _ = Real.sqrt Real.pi * c := by rw [gaussian_total_mass]

/-- **Convergence of the substituted integral** as `t ↓ 0`. -/
theorem subst_integral_tendsto {f : ℝ → ℝ} (hf_cont : Continuous f) {M : ℝ}
    (hf_bdd : ∀ x, |f x| ≤ M) (x : ℝ) :
    Filter.Tendsto (fun t : ℝ => ∫ z : ℝ, Real.exp (-z ^ 2) * f (x - 2 * Real.sqrt t * z))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (Real.sqrt Real.pi * f x)) := by
  set l := (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ) with hl
  have hl_count : l.IsCountablyGenerated := by
    dsimp [l]; infer_instance
  have h_integrand_bound : ∀ t : ℝ, ∀ z : ℝ,
      |Real.exp (-z ^ 2) * f (x - 2 * Real.sqrt t * z)| ≤ M * Real.exp (-z ^ 2) :=
    fun t z => (subst_integrand_bound hf_bdd t x).1 z
  have h_int_bound : Integrable (fun z : ℝ => M * Real.exp (-z ^ 2)) :=
    (subst_integrand_bound hf_bdd 0 x).2
  have hF_meas : ∀ᶠ t in l, AEStronglyMeasurable (fun z : ℝ => Real.exp (-z ^ 2) * f (x - 2 * Real.sqrt t * z)) volume := by
    have h_cont : ∀ t : ℝ, Continuous (fun z : ℝ => Real.exp (-z ^ 2) * f (x - 2 * Real.sqrt t * z)) := by
      intro t
      have h_arg : Continuous (fun z : ℝ => x - 2 * Real.sqrt t * z) :=
        continuous_const.sub ((continuous_const.mul continuous_id))
      have h_zsq : Continuous (fun (z : ℝ) => -z ^ 2) :=
        (continuous_id.pow 2).neg
      have h_exp : Continuous (fun z : ℝ => Real.exp (-z ^ 2)) :=
        Real.continuous_exp.comp h_zsq
      exact h_exp.mul (hf_cont.comp h_arg)
    filter_upwards [] with t
    exact (h_cont t).aestronglyMeasurable
  have h_bound_f : ∀ᶠ t in l, ∀ᵐ z ∂volume,
      ‖Real.exp (-z ^ 2) * f (x - 2 * Real.sqrt t * z)‖ ≤ M * Real.exp (-z ^ 2) := by
    filter_upwards [] with t
    filter_upwards [] with z
    simpa [Real.norm_eq_abs] using h_integrand_bound t z
  have h_lim : ∀ᵐ z ∂volume,
      Filter.Tendsto (fun t : ℝ => Real.exp (-z ^ 2) * f (x - 2 * Real.sqrt t * z))
        l (nhds (Real.exp (-z ^ 2) * f x)) := by
    filter_upwards [] with z
    exact subst_integrand_tendsto hf_cont x z
  have h_tendsto := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun z : ℝ => M * Real.exp (-z ^ 2))
    hF_meas h_bound_f h_int_bound h_lim
  simpa [gaussian_integral_const_mul (f x)] using h_tendsto

/-- **Initial-condition half.** `heatSolution f t x → f x` as `t ↓ 0`. -/
theorem initial_condition {f : ℝ → ℝ} (hf_cont : Continuous f) {M : ℝ}
    (hf_bdd : ∀ x, |f x| ≤ M) (x : ℝ) :
    Filter.Tendsto (fun t : ℝ => heatSolution f t x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f x)) := by
  -- On positive t, heatSolution equals the substitution form
  have h_event : (fun t : ℝ => heatSolution f t x) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun t : ℝ => Real.pi⁻¹ ^ ((1 : ℝ) / 2) * ∫ z : ℝ, Real.exp (-z ^ 2) * f (x - 2 * Real.sqrt t * z)) := by
    have h_mem : Set.Ioo (0 : ℝ) (1 : ℝ) ∈ nhdsWithin 0 (Set.Ioi 0) := by
      rw [nhdsWithin, Filter.mem_inf_principal]
      have h_eq : { x : ℝ | x ∈ Set.Ioi 0 → x ∈ Set.Ioo (0 : ℝ) (1 : ℝ) } = Set.Iio 1 := by
        ext x; constructor
        · intro h
          by_cases hx : x < 1
          · exact hx
          · have hx' : 1 ≤ x := by linarith
            have hpos : 0 < x := by linarith
            have : x ∈ Set.Ioo (0 : ℝ) (1 : ℝ) := h hpos
            rcases this with ⟨_, hlt⟩
            linarith
        · intro hx hx0
          exact ⟨hx0, hx⟩
      rw [h_eq]
      exact isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) < (1 : ℝ))
    filter_upwards [h_mem] with t ht
    have ht_pos : 0 < t := ht.1
    rw [heatSolution_eq_subst f ht_pos x]
  -- Simplify the constant factor: π⁻¹^(1/2) * √π * f x = f x
  have h_simp : Real.pi⁻¹ ^ ((1 : ℝ) / 2) * (Real.sqrt Real.pi * f x) = f x := by
    calc
      Real.pi⁻¹ ^ ((1 : ℝ) / 2) * (Real.sqrt Real.pi * f x) =
          ((Real.pi⁻¹ ^ ((1 : ℝ) / 2)) * Real.sqrt Real.pi) * f x := by ring
      _ = ((Real.pi⁻¹ ^ ((1 : ℝ) / 2)) * Real.pi ^ ((1 : ℝ) / 2)) * f x := by
        rw [Real.sqrt_eq_rpow]
      _ = ((Real.pi⁻¹ * Real.pi) ^ ((1 : ℝ) / 2)) * f x := by
        rw [Real.mul_rpow (by positivity : 0 ≤ Real.pi⁻¹) (by positivity : 0 ≤ Real.pi)]
      _ = (1 ^ ((1 : ℝ) / 2)) * f x := by
        field_simp [show Real.pi ≠ 0 from Real.pi_pos.ne.symm]
      _ = 1 * f x := by norm_num
      _ = f x := by norm_num
  have h_tendsto : Filter.Tendsto (fun t : ℝ => Real.pi⁻¹ ^ ((1 : ℝ) / 2) *
      ∫ z : ℝ, Real.exp (-z ^ 2) * f (x - 2 * Real.sqrt t * z))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f x)) := by
    have h_int_tendsto : Filter.Tendsto (fun t : ℝ => ∫ z : ℝ, Real.exp (-z ^ 2) * f (x - 2 * Real.sqrt t * z))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.sqrt Real.pi * f x)) :=
      subst_integral_tendsto hf_cont hf_bdd x
    have h_mul_tendsto : Filter.Tendsto (fun t : ℝ => Real.pi⁻¹ ^ ((1 : ℝ) / 2) *
        ∫ z : ℝ, Real.exp (-z ^ 2) * f (x - 2 * Real.sqrt t * z))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.pi⁻¹ ^ ((1 : ℝ) / 2) * (Real.sqrt Real.pi * f x))) :=
      Filter.Tendsto.const_mul (Real.pi⁻¹ ^ ((1 : ℝ) / 2)) h_int_tendsto
    rw [h_simp] at h_mul_tendsto
    exact h_mul_tendsto
  exact h_tendsto.congr' h_event.symm

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
  rcases hf_bdd with ⟨M, hM⟩
  refine ⟨?_, ?_⟩
  · intro t ht x
    exact pde_part hf_cont hM ht x
  · exact initial_condition hf_cont hM

end ODE
end Analysis
end LeanEval
