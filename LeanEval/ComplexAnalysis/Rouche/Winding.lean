import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import LeanEval.ComplexAnalysis.Rouche.Boundary

/-!
# Vanishing winding of `(f + g) / f`

The quotient `F = (f + g) / f` maps the boundary circle into the slit plane, hence
`Complex.log ∘ F` is a primitive of `logDeriv F` and the winding contour integral of
`logDeriv ((f + g) / f)` vanishes. This yields equality of the two winding integrals
of `logDeriv f` and `logDeriv (f + g)`.
-/

namespace LeanEval
namespace ComplexAnalysis

open MeromorphicOn

/-! ## Vanishing winding of `(f + g) / f` -/

/-- The quotient `F = (f + g) / f` maps the circle into the slit plane. -/
theorem F_slitPlane {f g : ℂ → ℂ} {R : ℝ}
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖)
    {z : ℂ} (hz : ‖z‖ = R) :
    ‖((f + g) / f) z - 1‖ < 1 ∧ ((f + g) / f) z ∈ Complex.slitPlane := by
  have hfz_ne : f z ≠ 0 := f_ne_zero_sphere hbound hz
  have hcalc : ((f + g) / f) z - 1 = g z / f z := by
    calc
      ((f + g) / f) z - 1 = ((f + g) z / f z) - 1 := rfl
      _ = ((f z + g z) / f z) - 1 := by rfl
      _ = g z / f z := by
        field_simp [hfz_ne]
        ring
  have h_norm_lt_one : ‖((f + g) / f) z - 1‖ < 1 := by
    rw [hcalc]
    calc
      ‖g z / f z‖ = ‖g z‖ / ‖f z‖ := by rw [norm_div]
      _ < 1 := by
        have hpos : 0 < ‖f z‖ := norm_pos_iff.mpr hfz_ne
        have hg_lt_f : ‖g z‖ < ‖f z‖ := hbound z hz
        exact (div_lt_one hpos).mpr hg_lt_f
  have h_mem_ball : ((f + g) / f) z ∈ Metric.ball (1 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_eq_norm]
    exact h_norm_lt_one
  have h_slitPlane : ((f + g) / f) z ∈ Complex.slitPlane :=
    Complex.ball_one_subset_slitPlane h_mem_ball
  exact ⟨h_norm_lt_one, h_slitPlane⟩

/-- `F = (f + g) / f` is differentiable and nonzero on the circle. -/
theorem F_hasDerivAt {f g : ℂ → ℂ} {R : ℝ}
    (hf : MeromorphicNFOn f Set.univ)
    (hg : AnalyticOn ℂ g Set.univ)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖)
    {z : ℂ} (hz : ‖z‖ = R) :
    DifferentiableAt ℂ ((f + g) / f) z ∧ ((f + g) / f) z ≠ 0 := by
  have ha_f := f_analytic_sphere hf hbound hz
  have ha_fg := fg_analytic_sphere hf hg hbound hz
  have h_diff_f : DifferentiableAt ℂ f z := ha_f.right.left.differentiableAt
  have h_diff_fg : DifferentiableAt ℂ (f + g) z := ha_fg.left.differentiableAt
  have h_diff : DifferentiableAt ℂ ((f + g) / f) z :=
    DifferentiableAt.div h_diff_fg h_diff_f ha_f.right.right
  have h_ne_zero : ((f + g) / f) z ≠ 0 := by
    have h_fz_ne : f z ≠ 0 := ha_f.right.right
    have h_fgz_ne : (f + g) z ≠ 0 := ha_fg.right.left
    simpa [Pi.div_apply] using div_ne_zero h_fgz_ne h_fz_ne
  exact ⟨h_diff, h_ne_zero⟩

/-- `Complex.log ∘ F` is a primitive of `logDeriv F` within the circle. -/
theorem winding_hasDerivWithinAt {f g : ℂ → ℂ} {R : ℝ}
    (hf : MeromorphicNFOn f Set.univ)
    (hg : AnalyticOn ℂ g Set.univ)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖)
    {z : ℂ} (hz : ‖z‖ = R) :
    HasDerivWithinAt (fun w => Complex.log (((f + g) / f) w))
      (logDeriv ((f + g) / f) z) (Metric.sphere 0 R) z := by
  have hF_pair := F_hasDerivAt hf hg hbound hz
  have hF_diff : DifferentiableAt ℂ ((f + g) / f) z := hF_pair.1
  have hF_slit : ((f + g) / f) z ∈ Complex.slitPlane := (F_slitPlane hbound hz).2
  have hF_deriv : HasDerivAt ((f + g) / f) (deriv ((f + g) / f) z) z :=
    hF_diff.hasDerivAt
  have h_log : HasDerivAt (fun w => Complex.log (((f + g) / f) w))
      (deriv ((f + g) / f) z / ((f + g) / f) z) z :=
    HasDerivAt.clog hF_deriv hF_slit
  simpa [logDeriv_apply] using h_log.hasDerivWithinAt

/-- The winding contour integral of `logDeriv ((f + g) / f)` vanishes. -/
theorem winding_cancel {f g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : MeromorphicNFOn f Set.univ)
    (hg : AnalyticOn ℂ g Set.univ)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖) :
    (∮ z in C(0, R), logDeriv ((f + g) / f) z) = 0 := by
  have hsphere_eq : ∀ z : ℂ, z ∈ Metric.sphere (0 : ℂ) R ↔ ‖z‖ = R := by
    intro z; simp
  refine circleIntegral.integral_eq_zero_of_hasDerivWithinAt (hR.le)
    (f := fun w => Complex.log (((f + g) / f) w)) ?_
  intro z hz
  rw [hsphere_eq] at hz
  exact winding_hasDerivWithinAt hf hg hbound hz

/-- Pointwise split of `logDeriv ((f + g) / f)` on the circle. -/
theorem logDeriv_div_pointwise {f g : ℂ → ℂ} {R : ℝ}
    (hf : MeromorphicNFOn f Set.univ)
    (hg : AnalyticOn ℂ g Set.univ)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖)
    {z : ℂ} (hz : ‖z‖ = R) :
    logDeriv ((f + g) / f) z = logDeriv (f + g) z - logDeriv f z := by
  have hf_analytic := (f_analytic_sphere hf hbound hz).right.left
  have hf_ne : f z ≠ 0 := (f_analytic_sphere hf hbound hz).right.right
  have hfg_analytic := (fg_analytic_sphere hf hg hbound hz).left
  have hfg_ne : (f + g) z ≠ 0 := (fg_analytic_sphere hf hg hbound hz).right.left
  have hdf : DifferentiableAt ℂ f z := hf_analytic.differentiableAt
  have hdfg : DifferentiableAt ℂ (f + g) z := hfg_analytic.differentiableAt
  have h := logDeriv_div (x := z) (hf := hfg_ne) (hg := hf_ne) (hdf := hdfg) (hdg := hdf)
  simpa [Pi.div_apply] using h

/-- The logarithmic derivatives `logDeriv f` and `logDeriv (f + g)` are
circle-integrable. -/
theorem logDeriv_circleIntegrable {f g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : MeromorphicNFOn f Set.univ)
    (hg : AnalyticOn ℂ g Set.univ)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖) :
    CircleIntegrable (logDeriv f) 0 R ∧ CircleIntegrable (logDeriv (f + g)) 0 R := by
  have hR_nonneg : 0 ≤ R := le_of_lt hR
  have hcont_logDeriv_f : ContinuousOn (logDeriv f) (Metric.sphere (0 : ℂ) R) := by
    intro z hz
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hz
    rcases f_analytic_sphere hf hbound hz with ⟨_, han, hne⟩
    have h_cont_deriv : ContinuousAt (deriv f) z := han.deriv.continuousAt
    have h_cont_f : ContinuousAt f z := han.continuousAt
    have h_cont_inv : ContinuousAt (fun x : ℂ => (f x)⁻¹) z :=
      (continuousAt_inv₀ hne).comp h_cont_f
    have h_cont_log : ContinuousAt (fun x : ℂ => deriv f x * (f x)⁻¹) z :=
      h_cont_deriv.mul h_cont_inv
    have h_log_eq : logDeriv f = fun x : ℂ => deriv f x * (f x)⁻¹ := by
      ext x; simp [logDeriv_apply, div_eq_mul_inv]
    rw [h_log_eq]
    exact h_cont_log.continuousWithinAt
  have hcont_logDeriv_fg : ContinuousOn (logDeriv (f + g)) (Metric.sphere (0 : ℂ) R) := by
    intro z hz
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hz
    rcases fg_analytic_sphere hf hg hbound hz with ⟨han, hne, _⟩
    have h_cont_deriv : ContinuousAt (deriv (f + g)) z := han.deriv.continuousAt
    have h_cont_fg : ContinuousAt (f + g) z := han.continuousAt
    have h_cont_inv : ContinuousAt (fun x : ℂ => ((f + g) x)⁻¹) z :=
      (continuousAt_inv₀ hne).comp h_cont_fg
    have h_cont_log : ContinuousAt (fun x : ℂ => deriv (f + g) x * ((f + g) x)⁻¹) z :=
      h_cont_deriv.mul h_cont_inv
    have h_log_eq : logDeriv (f + g) = fun x : ℂ => deriv (f + g) x * ((f + g) x)⁻¹ := by
      ext x; simp [logDeriv_apply, div_eq_mul_inv]
    rw [h_log_eq]
    exact h_cont_log.continuousWithinAt
  refine ⟨hcont_logDeriv_f.circleIntegrable hR_nonneg, hcont_logDeriv_fg.circleIntegrable hR_nonneg⟩

/-- Equality of the two winding integrals. -/
theorem logDeriv_diff {f g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : MeromorphicNFOn f Set.univ)
    (hg : AnalyticOn ℂ g Set.univ)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖) :
    (∮ z in C(0, R), logDeriv (f + g) z) = (∮ z in C(0, R), logDeriv f z) := by
  rcases logDeriv_circleIntegrable hR hf hg hbound with ⟨hf_int, hfg_int⟩
  have h_sub_zero : (∮ z in C(0, R), logDeriv (f + g) z) - (∮ z in C(0, R), logDeriv f z) = 0 := by
    calc
      (∮ z in C(0, R), logDeriv (f + g) z) - (∮ z in C(0, R), logDeriv f z)
          = (∮ z in C(0, R), (logDeriv (f + g) z - logDeriv f z)) := by
        rw [circleIntegral.integral_sub hfg_int hf_int]
      _ = (∮ z in C(0, R), logDeriv ((f + g) / f) z) := by
        refine circleIntegral.integral_congr hR.le ?_
        intro z hz
        rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hz
        rw [logDeriv_div_pointwise hf hg hbound hz]
      _ = 0 := winding_cancel hR hf hg hbound
  exact sub_eq_zero.mp h_sub_zero

end ComplexAnalysis
end LeanEval
