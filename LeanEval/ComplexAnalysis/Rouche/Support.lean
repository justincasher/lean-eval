import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Supporting lemmas for Rouché's theorem via zero counting

This file collects the supporting lemmas of the blueprint
`rouche-theorem-via-zero-counting`. The conclusion theorem `thm:rouche` lives in
`LeanEval/ComplexAnalysis/Rouche.lean`.

Throughout, for a radius `R`, the closed disk is `Metric.closedBall 0 R`, the open
disk is `Metric.ball 0 R` and the boundary circle is `{z : ‖z‖ = R}`. The divisor
`divisor h (Metric.closedBall 0 R)` is the zero/pole divisor of `h` on the closed
disk; its positive part `⁺` counts zeros and its negative part `⁻` counts poles.
-/

namespace LeanEval
namespace ComplexAnalysis

open MeromorphicOn

/-! ## Behaviour on the boundary circle -/

/-- `f` does not vanish on the circle. -/
theorem f_ne_zero_sphere {f g : ℂ → ℂ} {R : ℝ}
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖)
    {z : ℂ} (hz : ‖z‖ = R) : f z ≠ 0 := by
  sorry

/-- `f + g` does not vanish on the circle. -/
theorem fg_ne_zero_sphere {f g : ℂ → ℂ} {R : ℝ}
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖)
    {z : ℂ} (hz : ‖z‖ = R) : (f + g) z ≠ 0 := by
  sorry

/-- `f` is analytic and nonzero near the circle: its meromorphic order is `0`. -/
theorem f_analytic_sphere {f g : ℂ → ℂ} {R : ℝ}
    (hf : MeromorphicNFOn f Set.univ)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖)
    {z : ℂ} (hz : ‖z‖ = R) :
    meromorphicOrderAt f z = 0 ∧ AnalyticAt ℂ f z ∧ f z ≠ 0 := by
  sorry

/-- `f + g` is analytic and nonzero near the circle: its meromorphic order is `0`. -/
theorem fg_analytic_sphere {f g : ℂ → ℂ} {R : ℝ}
    (hf : MeromorphicNFOn f Set.univ)
    (hg : AnalyticOn ℂ g Set.univ)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖)
    {z : ℂ} (hz : ‖z‖ = R) :
    AnalyticAt ℂ (f + g) z ∧ (f + g) z ≠ 0 ∧ meromorphicOrderAt (f + g) z = 0 := by
  sorry

/-- A point of `D` where `h` has meromorphic order `0` is off the divisor. -/
theorem divisor_eq_zero_of_orderZero {h : ℂ → ℂ} {R : ℝ}
    (hh : MeromorphicOn h Set.univ)
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) R)
    (horder : meromorphicOrderAt h z = 0) :
    (divisor h (Metric.closedBall 0 R)) z = 0 := by
  sorry

/-- `f`'s divisor vanishes on the circle. -/
theorem divisor_f_zero_sphere {f g : ℂ → ℂ} {R : ℝ}
    (hf : MeromorphicNFOn f Set.univ)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖)
    {z : ℂ} (hz : ‖z‖ = R) :
    (divisor f (Metric.closedBall 0 R)) z = 0 := by
  sorry

/-- `f + g`'s divisor vanishes on the circle. -/
theorem divisor_fg_zero_sphere {f g : ℂ → ℂ} {R : ℝ}
    (hf : MeromorphicNFOn f Set.univ)
    (hg : AnalyticOn ℂ g Set.univ)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖)
    {z : ℂ} (hz : ‖z‖ = R) :
    (divisor (f + g) (Metric.closedBall 0 R)) z = 0 := by
  sorry

/-- The divisors of `f` and `f + g` are supported in the open disk. -/
theorem divisor_support_open {f g : ℂ → ℂ} {R : ℝ}
    (hf : MeromorphicNFOn f Set.univ)
    (hg : AnalyticOn ℂ g Set.univ)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖) :
    (divisor f (Metric.closedBall 0 R)).support ⊆ Metric.ball 0 R ∧
      (divisor (f + g) (Metric.closedBall 0 R)).support ⊆ Metric.ball 0 R := by
  sorry

/-! ## The argument principle -/

/-- Logarithmic derivative of a single power factor `(· - u) ^ n`. -/
theorem logDeriv_zpow_shift (u : ℂ) (n : ℤ) {z : ℂ} (hz : z ≠ u) :
    logDeriv (fun w => (w - u) ^ n) z = (n : ℂ) * (z - u)⁻¹ := by
  sorry

/-- Logarithmic derivative of a factorized rational function. -/
theorem logDeriv_factorizedRational {d : ℂ → ℤ} (hd : Function.HasFiniteSupport d)
    {z : ℂ} (hz : z ∉ Function.support d) :
    logDeriv (∏ᶠ u, (fun w => w - u) ^ d u) z = ∑ᶠ u, (d u : ℂ) * (z - u)⁻¹ := by
  sorry

/-- Each simple pole `(· - u)⁻¹` with `u` in the open disk is circle-integrable. -/
theorem circleIntegrable_sub_inv {R : ℝ} {u : ℂ} (hu : u ∈ Metric.ball (0 : ℂ) R) :
    CircleIntegrable (fun z => (z - u)⁻¹) 0 R := by
  sorry

/-- Cauchy integral of a single simple pole. -/
theorem circleIntegral_sub_inv {R : ℝ} {u : ℂ} (hu : u ∈ Metric.ball (0 : ℂ) R) :
    (∮ z in C(0, R), (z - u)⁻¹) = 2 * (Real.pi : ℂ) * Complex.I := by
  sorry

/-- Contour integral of a finite sum of simple poles. -/
theorem circleIntegral_sum_inv {R : ℝ} {d : ℂ → ℤ} (hd : Function.HasFiniteSupport d)
    (hsupp : Function.support d ⊆ Metric.ball (0 : ℂ) R) :
    (∮ z in C(0, R), ∑ᶠ u, (d u : ℂ) * (z - u)⁻¹)
      = (∑ᶠ u, (d u : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I) := by
  sorry

/-- Contour integral of the logarithmic derivative of a unit (analytic and nowhere
zero on the closed disk) vanishes. -/
theorem circleIntegral_logDeriv_unit {R : ℝ} {U : ℂ → ℂ}
    (hUana : AnalyticOnNhd ℂ U (Metric.closedBall 0 R))
    (hU0 : ∀ z ∈ Metric.closedBall (0 : ℂ) R, U z ≠ 0) :
    (∮ z in C(0, R), logDeriv U z) = 0 := by
  sorry

/-- The factorization `h = φ · U` holds on a punctured neighbourhood of each point
of the circle. -/
theorem factorization_eventuallyEq {h : ℂ → ℂ} {R : ℝ}
    (hh : MeromorphicOn h Set.univ)
    (horder : ∀ z : ℂ, ‖z‖ = R → meromorphicOrderAt h z = 0)
    {U : ℂ → ℂ} (hUana : AnalyticOnNhd ℂ U (Metric.closedBall 0 R))
    (hU0 : ∀ z ∈ Metric.closedBall (0 : ℂ) R, U z ≠ 0)
    (hfact : h =ᶠ[Filter.codiscreteWithin (Metric.closedBall 0 R)]
      (∏ᶠ u, (fun x => x - u) ^ (divisor h (Metric.closedBall 0 R)) u) • U)
    {z : ℂ} (hz : ‖z‖ = R) :
    h =ᶠ[nhdsWithin z {z}ᶜ]
      (∏ᶠ u, (fun x => x - u) ^ (divisor h (Metric.closedBall 0 R)) u) • U := by
  sorry

/-- Factorization of the logarithmic derivative on the circle. -/
theorem factorization_logDeriv {h : ℂ → ℂ} {R : ℝ}
    (hh : MeromorphicOn h Set.univ)
    (horder : ∀ z : ℂ, ‖z‖ = R → meromorphicOrderAt h z = 0)
    {U : ℂ → ℂ} (hUana : AnalyticOnNhd ℂ U (Metric.closedBall 0 R))
    (hU0 : ∀ z ∈ Metric.closedBall (0 : ℂ) R, U z ≠ 0)
    (hfact : h =ᶠ[Filter.codiscreteWithin (Metric.closedBall 0 R)]
      (∏ᶠ u, (fun x => x - u) ^ (divisor h (Metric.closedBall 0 R)) u) • U)
    {z : ℂ} (hz : ‖z‖ = R) :
    logDeriv h z
      = logDeriv (∏ᶠ u, (fun x => x - u) ^ (divisor h (Metric.closedBall 0 R)) u) z
        + logDeriv U z := by
  sorry

/-- A bound strictly above a finite set of reals all larger than `R`. -/
theorem exists_lt_of_finite {R : ℝ} {A : Finset ℝ} (hA : ∀ a ∈ A, R < a) :
    ∃ R' : ℝ, R < R' ∧ ∀ a ∈ A, R' ≤ a := by
  sorry

/-- A zero/pole-free annulus just outside the circle: there is `R' > R` such that
the divisor of `h` on the larger disk is still supported in the open disk of
radius `R`. -/
theorem annulus_zero_free {h : ℂ → ℂ} {R : ℝ}
    (hh : MeromorphicOn h Set.univ)
    (horder : ∀ z : ℂ, ‖z‖ = R → meromorphicOrderAt h z = 0) :
    ∃ R' : ℝ, R < R' ∧ (divisor h (Metric.ball 0 R')).support ⊆ Metric.ball 0 R := by
  sorry

/-- A meromorphic function that is not identically zero has finite order at every
point. -/
theorem order_ne_top {h : ℂ → ℂ}
    (hh : MeromorphicOn h Set.univ)
    (hne : ∃ z, meromorphicOrderAt h z ≠ ⊤) (z : ℂ) :
    meromorphicOrderAt h z ≠ ⊤ := by
  sorry

/-- The factorized rational of `h` on the larger disk `B'` restricts to the
factorized rational on the closed disk `D`, provided the divisor on `B'` is
supported in `D`. -/
theorem factorizedRational_restrict {h : ℂ → ℂ} {R R' : ℝ}
    (hh : MeromorphicOn h Set.univ)
    (hsub : Metric.closedBall (0 : ℂ) R ⊆ Metric.ball 0 R')
    (hsupp : (divisor h (Metric.ball 0 R')).support ⊆ Metric.closedBall 0 R) :
    (∏ᶠ u, (fun x => x - u) ^ (divisor h (Metric.ball 0 R')) u)
      = (∏ᶠ u, (fun x => x - u) ^ (divisor h (Metric.closedBall 0 R)) u) := by
  sorry

/-- Existence of the factorization `h = φ · U` with `φ` the factorized rational of
`divisor h D` and `U` analytic and nowhere zero on the closed disk. -/
theorem factorization_existence {h : ℂ → ℂ} {R : ℝ}
    (hh : MeromorphicOn h Set.univ)
    (hne : ∃ z, meromorphicOrderAt h z ≠ ⊤)
    (horder : ∀ z : ℂ, ‖z‖ = R → meromorphicOrderAt h z = 0) :
    ∃ U : ℂ → ℂ, AnalyticOnNhd ℂ U (Metric.closedBall 0 R) ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) R, U z ≠ 0) ∧
      h =ᶠ[Filter.codiscreteWithin (Metric.closedBall 0 R)]
        (∏ᶠ u, (fun x => x - u) ^ (divisor h (Metric.closedBall 0 R)) u) • U := by
  sorry

/-- Splitting the contour integral of `logDeriv h` along the factorization
`h = φ · U`. -/
theorem argument_principle_integral_split {h : ℂ → ℂ} {R : ℝ}
    (hh : MeromorphicOn h Set.univ)
    (horder : ∀ z : ℂ, ‖z‖ = R → meromorphicOrderAt h z = 0)
    {U : ℂ → ℂ} (hUana : AnalyticOnNhd ℂ U (Metric.closedBall 0 R))
    (hU0 : ∀ z ∈ Metric.closedBall (0 : ℂ) R, U z ≠ 0)
    (hfact : h =ᶠ[Filter.codiscreteWithin (Metric.closedBall 0 R)]
      (∏ᶠ u, (fun x => x - u) ^ (divisor h (Metric.closedBall 0 R)) u) • U) :
    (∮ z in C(0, R), logDeriv h z)
      = (∮ z in C(0, R),
          logDeriv (∏ᶠ u, (fun x => x - u) ^ (divisor h (Metric.closedBall 0 R)) u) z)
        + (∮ z in C(0, R), logDeriv U z) := by
  sorry

/-- Contour integral of `logDeriv φ` where `φ` is the factorized rational of
`divisor h D`, supported in the open disk. -/
theorem circleIntegral_logDeriv_factorizedRational {h : ℂ → ℂ} {R : ℝ}
    (hsupp : (divisor h (Metric.closedBall 0 R)).support ⊆ Metric.ball 0 R) :
    (∮ z in C(0, R),
        logDeriv (∏ᶠ u, (fun x => x - u) ^ (divisor h (Metric.closedBall 0 R)) u) z)
      = (∑ᶠ u, ((divisor h (Metric.closedBall 0 R)) u : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I) := by
  sorry

/-- Integral evaluation of the logarithmic derivative. -/
theorem argument_principle_integral {h : ℂ → ℂ} {R : ℝ}
    (hh : MeromorphicOn h Set.univ)
    (hne : ∃ z, meromorphicOrderAt h z ≠ ⊤)
    (horder : ∀ z : ℂ, ‖z‖ = R → meromorphicOrderAt h z = 0) :
    (∮ z in C(0, R), logDeriv h z)
      = (∑ᶠ u, ((divisor h (Metric.closedBall 0 R)) u : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I) := by
  sorry

/-- Argument principle, zero-counting form: the signed mass of the divisor equals
the normalized contour integral of the logarithmic derivative. -/
theorem argument_principle {h : ℂ → ℂ} {R : ℝ}
    (hh : MeromorphicOn h Set.univ)
    (hne : ∃ z, meromorphicOrderAt h z ≠ ⊤)
    (horder : ∀ z : ℂ, ‖z‖ = R → meromorphicOrderAt h z = 0) :
    ((∑ᶠ z, (divisor h (Metric.closedBall 0 R)) z : ℤ) : ℂ)
      = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * (∮ z in C(0, R), logDeriv h z) := by
  sorry

/-! ## Vanishing winding of `(f + g) / f` -/

/-- The quotient `F = (f + g) / f` maps the circle into the slit plane. -/
theorem F_slitPlane {f g : ℂ → ℂ} {R : ℝ}
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖)
    {z : ℂ} (hz : ‖z‖ = R) :
    ‖((f + g) / f) z - 1‖ < 1 ∧ ((f + g) / f) z ∈ Complex.slitPlane := by
  sorry

/-- `F = (f + g) / f` is differentiable and nonzero on the circle. -/
theorem F_hasDerivAt {f g : ℂ → ℂ} {R : ℝ}
    (hf : MeromorphicNFOn f Set.univ)
    (hg : AnalyticOn ℂ g Set.univ)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖)
    {z : ℂ} (hz : ‖z‖ = R) :
    DifferentiableAt ℂ ((f + g) / f) z ∧ ((f + g) / f) z ≠ 0 := by
  sorry

/-- `Complex.log ∘ F` is a primitive of `logDeriv F` within the circle. -/
theorem winding_hasDerivWithinAt {f g : ℂ → ℂ} {R : ℝ}
    (hf : MeromorphicNFOn f Set.univ)
    (hg : AnalyticOn ℂ g Set.univ)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖)
    {z : ℂ} (hz : ‖z‖ = R) :
    HasDerivWithinAt (fun w => Complex.log (((f + g) / f) w))
      (logDeriv ((f + g) / f) z) (Metric.sphere 0 R) z := by
  sorry

/-- The winding contour integral of `logDeriv ((f + g) / f)` vanishes. -/
theorem winding_cancel {f g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : MeromorphicNFOn f Set.univ)
    (hg : AnalyticOn ℂ g Set.univ)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖) :
    (∮ z in C(0, R), logDeriv ((f + g) / f) z) = 0 := by
  sorry

/-- Pointwise split of `logDeriv ((f + g) / f)` on the circle. -/
theorem logDeriv_div_pointwise {f g : ℂ → ℂ} {R : ℝ}
    (hf : MeromorphicNFOn f Set.univ)
    (hg : AnalyticOn ℂ g Set.univ)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖)
    {z : ℂ} (hz : ‖z‖ = R) :
    logDeriv ((f + g) / f) z = logDeriv (f + g) z - logDeriv f z := by
  sorry

/-- The logarithmic derivatives `logDeriv f` and `logDeriv (f + g)` are
circle-integrable. -/
theorem logDeriv_circleIntegrable {f g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : MeromorphicNFOn f Set.univ)
    (hg : AnalyticOn ℂ g Set.univ)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖) :
    CircleIntegrable (logDeriv f) 0 R ∧ CircleIntegrable (logDeriv (f + g)) 0 R := by
  sorry

/-- Equality of the two winding integrals. -/
theorem logDeriv_diff {f g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : MeromorphicNFOn f Set.univ)
    (hg : AnalyticOn ℂ g Set.univ)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖) :
    (∮ z in C(0, R), logDeriv (f + g) z) = (∮ z in C(0, R), logDeriv f z) := by
  sorry

/-! ## Matching pole divisors and conclusion -/

/-- Nonnegative order of `f` is preserved by adding the analytic `g`. -/
theorem order_nonneg_of_pole {f g : ℂ → ℂ}
    (hf : MeromorphicNFOn f Set.univ)
    (hg : AnalyticOn ℂ g Set.univ) (z : ℂ)
    (h : 0 ≤ meromorphicOrderAt f z) : 0 ≤ meromorphicOrderAt (f + g) z := by
  sorry

/-- At a pole of `f` the order of `f + g` equals that of `f`. -/
theorem order_eq_at_pole {f g : ℂ → ℂ}
    (hf : MeromorphicNFOn f Set.univ)
    (hg : AnalyticOn ℂ g Set.univ) (z : ℂ)
    (h : meromorphicOrderAt f z < 0) :
    meromorphicOrderAt (f + g) z = meromorphicOrderAt f z := by
  sorry

/-- `f` and `f + g` have the same pole divisor (negative part). -/
theorem negPart_eq {f g : ℂ → ℂ} {R : ℝ}
    (hf : MeromorphicNFOn f Set.univ)
    (hg : AnalyticOn ℂ g Set.univ)
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) R) :
    ((divisor (f + g) (Metric.closedBall 0 R))⁻) z
      = ((divisor f (Metric.closedBall 0 R))⁻) z := by
  sorry

/-- The argument principle applies to both `f` and `f + g`: each is meromorphic on
`ℂ`, not identically zero, and has order `0` on the circle. -/
theorem orderZero_bundle {f g : ℂ → ℂ} {R : ℝ}
    (hf : MeromorphicNFOn f Set.univ)
    (hg : AnalyticOn ℂ g Set.univ)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖) :
    (MeromorphicOn f Set.univ ∧ (∃ z, meromorphicOrderAt f z ≠ ⊤) ∧
        ∀ z : ℂ, ‖z‖ = R → meromorphicOrderAt f z = 0) ∧
      (MeromorphicOn (f + g) Set.univ ∧ (∃ z, meromorphicOrderAt (f + g) z ≠ ⊤) ∧
        ∀ z : ℂ, ‖z‖ = R → meromorphicOrderAt (f + g) z = 0) := by
  sorry

/-- The positive-part mass decomposes as the signed mass plus the negative-part
mass. -/
theorem posPart_mass_decomp {h : ℂ → ℂ} {R : ℝ} :
    (∑ᶠ z, ((divisor h (Metric.closedBall 0 R))⁺) z)
      = (∑ᶠ z, (divisor h (Metric.closedBall 0 R)) z)
        + (∑ᶠ z, ((divisor h (Metric.closedBall 0 R))⁻) z) := by
  sorry

end ComplexAnalysis
end LeanEval
