import Mathlib
import EvalTools.Markers

namespace LeanEval
namespace Analysis

/-!
# Euler–Lagrange equation

§44 of Oliver Knill's *Some Fundamental Theorems in Mathematics* (the additional
statement of the calculus-of-variations section). A sufficiently regular
stationary path `x` of the action `I(y) = ∫_a^b L(t, y(t), y'(t)) dt` satisfies
the Euler–Lagrange equation `∂L/∂x = (d/dt)(∂L/∂x')` pointwise on `(a, b)`.

mathlib has the fundamental lemma of the calculus of variations
(`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` and neighbours), but it
has no notion of a variational extremum of an action functional and no
Euler–Lagrange theorem (`grep -i 'euler.*lagrange'` in mathlib finds nothing in
the analytic sense). Here a path is a variational extremum when the first
variation of the action vanishes against every smooth compactly supported
perturbation, and the conclusion is the classical pointwise equation for `C²`
data.
-/

open MeasureTheory Set
open scoped ContDiff

/-- `∂L/∂x` along the path `x` at time `t`: the derivative of the partial map
`y ↦ L t y (x' t)` at `y = x t`. -/
noncomputable def lagrangianPartialX
    (L : ℝ → ℝ → ℝ → ℝ) (x : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv (fun y => L t y (deriv x t)) (x t)

/-- `∂L/∂x'` along the path `x` at time `t`: the derivative of the partial map
`z ↦ L t (x t) z` at `z = x' t`. -/
noncomputable def lagrangianPartialV
    (L : ℝ → ℝ → ℝ → ℝ) (x : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv (fun z => L t (x t) z) (deriv x t)

/-- A `C¹` path `x : ℝ → ℝ` is a **variational extremum** of the action
`I(y) := ∫_a^b L(t, y(t), y'(t)) dt` on `(a, b)` if for every smooth compactly
supported variation `h` with `tsupport h ⊆ (a, b)`, the first variation
`d/dε|_{ε=0} ∫_a^b L(t, x(t) + ε h(t), x'(t) + ε h'(t)) dt` vanishes. -/
def IsVariationalExtremum
    (a b : ℝ) (L : ℝ → ℝ → ℝ → ℝ) (x : ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 x ∧
  ∀ h : ℝ → ℝ, ContDiff ℝ ∞ h → HasCompactSupport h →
    tsupport h ⊆ Set.Ioo a b →
    deriv (fun ε : ℝ => ∫ t in Set.Ioo a b,
        L t (x t + ε * h t) (deriv x t + ε * deriv h t)) 0 = 0

/-- Shifted spatial partial `∂_x L_ε` along the configuration `x + ε h`: the
derivative of `y ↦ L t y (x' t + ε h' t)` at `y = x t + ε h t`. At `ε = 0` it
reduces to `lagrangianPartialX L x`. -/
noncomputable def lagrangianPartialXShifted
    (L : ℝ → ℝ → ℝ → ℝ) (x h : ℝ → ℝ) (ε t : ℝ) : ℝ :=
  deriv (fun y => L t y (deriv x t + ε * deriv h t)) (x t + ε * h t)

/-- Shifted velocity partial `∂_{x'} L_ε` along the configuration `x + ε h`: the
derivative of `z ↦ L t (x t + ε h t) z` at `z = x' t + ε h' t`. At `ε = 0` it
reduces to `lagrangianPartialV L x`. -/
noncomputable def lagrangianPartialVShifted
    (L : ℝ → ℝ → ℝ → ℝ) (x h : ℝ → ℝ) (ε t : ℝ) : ℝ :=
  deriv (fun z => L t (x t + ε * h t) z) (deriv x t + ε * deriv h t)

/-! ### Regularity of the partials along the path -/

/-- **Directional derivative equals the Fréchet derivative on that direction.**
For `f` differentiable at `p` and a direction `d`, the derivative of the line
`ε ↦ f (p + ε • d)` at `0` is `fderiv ℝ f p d`. -/
theorem directional_deriv_eq_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (p d : E) (hf : DifferentiableAt ℝ f p) :
    deriv (fun ε : ℝ => f (p + ε • d)) 0 = fderiv ℝ f p d := by
  sorry

/-- **A partial derivative of a `C²` function is `C¹`.** For a `C²` function
`F : ℝ × ℝ × ℝ → ℝ` and a fixed direction `e`, the map `p ↦ fderiv ℝ F p e`
(which, for `e` a basis vector, is the slice/partial derivative in that slot) is
`C¹` on `ℝ³`; in particular it is continuous. -/
theorem partialDeriv_contDiff
    (F : ℝ × ℝ × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (e : ℝ × ℝ × ℝ) :
    ContDiff ℝ 1 (fun p => fderiv ℝ F p e) := by
  sorry

/-- **The curve `(t, x(t), x'(t))` is `C¹`.** -/
theorem curve_contDiff (x : ℝ → ℝ) (hx : ContDiff ℝ 2 x) :
    ContDiff ℝ 1 (fun t : ℝ => (t, x t, deriv x t)) := by
  sorry

/-- **The velocity partial along `x` is `C¹`.** If `L` and `x` are `C²`, then
`t ↦ ∂_{x'} L(t)` is `C¹`; in particular it is differentiable everywhere and its
derivative is continuous. -/
theorem lagrangianPartialV_contDiff
    (L : ℝ → ℝ → ℝ → ℝ) (x : ℝ → ℝ)
    (hL : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2))
    (hx : ContDiff ℝ 2 x) :
    ContDiff ℝ 1 (lagrangianPartialV L x) := by
  sorry

/-- **The spatial partial along `x` is continuous.** -/
theorem lagrangianPartialX_continuous
    (L : ℝ → ℝ → ℝ → ℝ) (x : ℝ → ℝ)
    (hL : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2))
    (hx : ContDiff ℝ 2 x) :
    Continuous (lagrangianPartialX L x) := by
  sorry

/-- **The Euler–Lagrange defect is continuous.** The defect
`D(t) = ∂_x L(t) - (d/dt) ∂_{x'} L(t)` is continuous on `ℝ`. -/
theorem el_defect_continuous
    (L : ℝ → ℝ → ℝ → ℝ) (x : ℝ → ℝ)
    (hL : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2))
    (hx : ContDiff ℝ 2 x) :
    Continuous (fun t => lagrangianPartialX L x t - deriv (lagrangianPartialV L x) t) := by
  sorry

/-! ### The first variation -/

/-- **Continuous with compact support is integrable.** (A restatement of
`Continuous.integrable_of_hasCompactSupport`.) -/
theorem continuous_compactSupport_integrable
    {f : ℝ → ℝ} (hf : Continuous f) (hsupp : HasCompactSupport f) :
    Integrable f := by
  sorry

/-- **Coordinate decomposition of a bivariate Fréchet derivative.** For
`Φ : ℝ × ℝ → ℝ` differentiable at `(y₀, z₀)`, the Fréchet derivative on `(u, v)`
splits into the two slice (partial) derivatives. -/
theorem fderiv_decomp
    (Φ : ℝ × ℝ → ℝ) (y₀ z₀ : ℝ) (hΦ : DifferentiableAt ℝ Φ (y₀, z₀)) (u v : ℝ) :
    fderiv ℝ Φ (y₀, z₀) (u, v)
      = deriv (fun y => Φ (y, z₀)) y₀ * u + deriv (fun z => Φ (y₀, z)) z₀ * v := by
  sorry

/-- **Derivative of the shifted-configuration curve.** For fixed `t` and `h`, the
curve `ε ↦ (x t + ε h t, x' t + ε h' t)` has derivative `(h t, h' t)` at every
`ε`. -/
theorem variation_curve_hasDerivAt (x h : ℝ → ℝ) (t ε : ℝ) :
    HasDerivAt (fun e : ℝ => (x t + e * h t, deriv x t + e * deriv h t))
      (h t, deriv h t) ε := by
  sorry

/-- **Pointwise `ε`-derivative of the integrand at a shifted configuration.** If
`L` is differentiable at the shifted configuration, then
`ε ↦ L(t, x t + ε h t, x' t + ε h' t)` has derivative
`∂_x L_{ε₀}(t) · h t + ∂_{x'} L_{ε₀}(t) · h' t` at `ε = ε₀`. -/
theorem integrand_hasDerivAt
    (L : ℝ → ℝ → ℝ → ℝ) (x h : ℝ → ℝ) (t ε₀ : ℝ)
    (hL : DifferentiableAt ℝ (fun p : ℝ × ℝ => L t p.1 p.2)
            (x t + ε₀ * h t, deriv x t + ε₀ * deriv h t)) :
    HasDerivAt (fun ε : ℝ => L t (x t + ε * h t) (deriv x t + ε * deriv h t))
      (lagrangianPartialXShifted L x h ε₀ t * h t
        + lagrangianPartialVShifted L x h ε₀ t * deriv h t) ε₀ := by
  sorry

/-- **The `ε`-derivative integrand is supported in `tsupport h`.** For each `ε`
the integrand `t ↦ ∂_x L_ε(t) · h t + ∂_{x'} L_ε(t) · h' t` is supported in
`tsupport h`. -/
theorem deriv_integrand_support
    (L : ℝ → ℝ → ℝ → ℝ) (x h : ℝ → ℝ) (hh : HasCompactSupport h) (ε : ℝ) :
    Function.support (fun t => lagrangianPartialXShifted L x h ε t * h t
        + lagrangianPartialVShifted L x h ε t * deriv h t) ⊆ tsupport h := by
  sorry

/-- **Uniform bound of the shifted partials over the `ε`-tube.** For `L, x` `C²`,
`h` smooth with compact support, and `r > 0`, there is a single constant `M`
bounding both shifted partials over `tsupport h × [-r, r]`. -/
theorem tube_bound
    (L : ℝ → ℝ → ℝ → ℝ) (x h : ℝ → ℝ)
    (hL : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2))
    (hx : ContDiff ℝ 2 x) (hh : ContDiff ℝ ∞ h) (hhsupp : HasCompactSupport h)
    {r : ℝ} (hr : 0 < r) :
    ∃ M : ℝ, ∀ ε : ℝ, |ε| ≤ r → ∀ t ∈ tsupport h,
      |lagrangianPartialXShifted L x h ε t| ≤ M
        ∧ |lagrangianPartialVShifted L x h ε t| ≤ M := by
  sorry

/-- **Integrable dominating bound for the `ε`-derivative.** Under the standing
hypotheses there is an integrable `g ≥ 0` dominating the `ε`-derivative integrand
pointwise, uniformly for `|ε| ≤ r`. -/
theorem dominating_bound
    {a b : ℝ} (L : ℝ → ℝ → ℝ → ℝ) (x h : ℝ → ℝ)
    (hL : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2))
    (hx : ContDiff ℝ 2 x) (hh : ContDiff ℝ ∞ h) (hhsupp : HasCompactSupport h)
    (hsub : tsupport h ⊆ Set.Ioo a b) {r : ℝ} (hr : 0 < r) :
    ∃ g : ℝ → ℝ, Integrable g ∧ (∀ t, 0 ≤ g t) ∧
      ∀ ε : ℝ, |ε| ≤ r → ∀ t,
        |lagrangianPartialXShifted L x h ε t * h t
            + lagrangianPartialVShifted L x h ε t * deriv h t| ≤ g t := by
  sorry

/-- **A.e.-measurability of the integrand family.** For every `ε` both the
integrand and its `ε`-derivative are a.e.-strongly-measurable on `(a, b)`. -/
theorem integrand_aestronglyMeasurable
    {a b : ℝ} (L : ℝ → ℝ → ℝ → ℝ) (x h : ℝ → ℝ)
    (hL : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2))
    (hx : ContDiff ℝ 2 x) (hh : ContDiff ℝ ∞ h) :
    (∀ ε : ℝ, AEStronglyMeasurable
        (fun t => L t (x t + ε * h t) (deriv x t + ε * deriv h t))
        (volume.restrict (Set.Ioo a b)))
    ∧ (∀ ε : ℝ, AEStronglyMeasurable
        (fun t => lagrangianPartialXShifted L x h ε t * h t
            + lagrangianPartialVShifted L x h ε t * deriv h t)
        (volume.restrict (Set.Ioo a b))) := by
  sorry

/-- **Integrability of the base integrand.** For `a < b` and `L, x` `C²`, the
`ε = 0` integrand `t ↦ L(t, x t, x' t)` is integrable on `(a, b)`. -/
theorem base_integrand_integrable
    {a b : ℝ} (hab : a < b) (L : ℝ → ℝ → ℝ → ℝ) (x : ℝ → ℝ)
    (hL : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2))
    (hx : ContDiff ℝ 2 x) :
    IntegrableOn (fun t => L t (x t) (deriv x t)) (Set.Ioo a b) := by
  sorry

/-- **First variation as an integral.** Under the standing hypotheses, the first
variation equals `∫_{(a,b)} (∂_x L(t) h t + ∂_{x'} L(t) h' t) dt`. -/
theorem first_variation
    {a b : ℝ} (L : ℝ → ℝ → ℝ → ℝ) (x h : ℝ → ℝ)
    (hL : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2))
    (hx : ContDiff ℝ 2 x) (hh : ContDiff ℝ ∞ h) (hhsupp : HasCompactSupport h)
    (hsub : tsupport h ⊆ Set.Ioo a b) :
    deriv (fun ε : ℝ => ∫ t in Set.Ioo a b,
        L t (x t + ε * h t) (deriv x t + ε * deriv h t)) 0
      = ∫ t in Set.Ioo a b,
          (lagrangianPartialX L x t * h t + lagrangianPartialV L x t * deriv h t) := by
  sorry

/-! ### Integration by parts and the weak equation -/

/-- **A compactly supported variation vanishes at the endpoints.** -/
theorem boundary_vanishing
    {a b : ℝ} (h : ℝ → ℝ) (hsub : tsupport h ⊆ Set.Ioo a b) :
    h a = 0 ∧ h b = 0 := by
  sorry

/-- **Integral over `(a, b)` as an interval integral.** For `a ≤ b` and `f`
integrable on `(a, b)`, the set integral over `(a, b)` equals `∫ a..b`. -/
theorem ioo_interval_conversion
    {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) (hf : IntegrableOn f (Set.Ioo a b)) :
    ∫ t in Set.Ioo a b, f t = ∫ t in a..b, f t := by
  sorry

/-- **Differentiability and interval-integrability for integration by parts.**
`∂_{x'} L` and `h` have derivatives everywhere, and the two product integrands
are interval-integrable on `[a, b]`. -/
theorem ibp_hypotheses
    {a b : ℝ} (L : ℝ → ℝ → ℝ → ℝ) (x h : ℝ → ℝ)
    (hL : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2))
    (hx : ContDiff ℝ 2 x) (hh : ContDiff ℝ ∞ h) :
    (∀ t : ℝ, HasDerivAt (lagrangianPartialV L x) (deriv (lagrangianPartialV L x) t) t)
    ∧ (∀ t : ℝ, HasDerivAt h (deriv h t) t)
    ∧ IntervalIntegrable (fun t => lagrangianPartialV L x t * deriv h t) volume a b
    ∧ IntervalIntegrable (fun t => deriv (lagrangianPartialV L x) t * h t) volume a b := by
  sorry

/-- **Integration by parts for the velocity term.** -/
theorem integration_by_parts
    {a b : ℝ} (hab : a < b) (L : ℝ → ℝ → ℝ → ℝ) (x h : ℝ → ℝ)
    (hL : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2))
    (hx : ContDiff ℝ 2 x) (hh : ContDiff ℝ ∞ h) (hhsupp : HasCompactSupport h)
    (hsub : tsupport h ⊆ Set.Ioo a b) :
    (∫ t in Set.Ioo a b, lagrangianPartialV L x t * deriv h t)
      = - ∫ t in Set.Ioo a b, deriv (lagrangianPartialV L x) t * h t := by
  sorry

/-- **The weak-equation integrands are integrable.** Each of `∂_x L · h`,
`∂_{x'} L · h'`, and `(d/dt ∂_{x'} L) · h` is continuous with compact support,
hence integrable. -/
theorem weak_el_integrands_integrable
    (L : ℝ → ℝ → ℝ → ℝ) (x h : ℝ → ℝ)
    (hL : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2))
    (hx : ContDiff ℝ 2 x) (hh : ContDiff ℝ ∞ h) (hhsupp : HasCompactSupport h) :
    Integrable (fun t => lagrangianPartialX L x t * h t)
    ∧ Integrable (fun t => lagrangianPartialV L x t * deriv h t)
    ∧ Integrable (fun t => deriv (lagrangianPartialV L x) t * h t) := by
  sorry

/-- **Weak Euler–Lagrange equation.** For a variational extremum `x`, the defect
tested against any admissible `h` integrates to zero over `(a, b)`. -/
theorem weak_euler_lagrange
    {a b : ℝ} (hab : a < b) (L : ℝ → ℝ → ℝ → ℝ) (x : ℝ → ℝ)
    (hL : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2))
    (hx : ContDiff ℝ 2 x) (hxe : IsVariationalExtremum a b L x)
    (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h) (hhsupp : HasCompactSupport h)
    (hsub : tsupport h ⊆ Set.Ioo a b) :
    (∫ t in Set.Ioo a b,
      (lagrangianPartialX L x t - deriv (lagrangianPartialV L x) t) * h t) = 0 := by
  sorry

/-- **Weak equation in `∫ g • f` shape over the full measure.** The defect tested
against any admissible `h` integrates to zero against the full volume measure, in
the form required by the fundamental lemma of the calculus of variations. -/
theorem defect_test_integral_vanishes
    {a b : ℝ} (hab : a < b) (L : ℝ → ℝ → ℝ → ℝ) (x : ℝ → ℝ)
    (hL : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2))
    (hx : ContDiff ℝ 2 x) (hxe : IsVariationalExtremum a b L x) :
    ∀ h : ℝ → ℝ, ContDiff ℝ ∞ h → HasCompactSupport h → tsupport h ⊆ Set.Ioo a b →
      (∫ t, h t • (lagrangianPartialX L x t - deriv (lagrangianPartialV L x) t)) = 0 := by
  sorry

/-- **Euler–Lagrange equation** (§44). On an interval `a < b`, every `C²`
variational extremum `x` of the action `I(y) = ∫_a^b L(t, y(t), y'(t)) dt`, with
`C²` Lagrangian `L`, satisfies the pointwise equation
`∂L/∂x (t, x(t), x'(t)) = (d/dt)(∂L/∂x' (t, x(t), x'(t)))` on `(a, b)`. -/
@[eval_problem]
theorem euler_lagrange_equation
    {a b : ℝ} (L : ℝ → ℝ → ℝ → ℝ) (x : ℝ → ℝ) (_hab : a < b)
    (_hL : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2))
    (_hx : ContDiff ℝ 2 x)
    (_hxe : IsVariationalExtremum a b L x) :
    ∀ t ∈ Set.Ioo a b,
      lagrangianPartialX L x t = deriv (lagrangianPartialV L x) t := by
  sorry

end Analysis
end LeanEval
