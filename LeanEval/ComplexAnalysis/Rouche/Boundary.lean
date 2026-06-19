import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Behaviour on the boundary circle (Rouché via zero counting)

Supporting lemmas of the blueprint `rouche-theorem-via-zero-counting` describing the
behaviour of `f`, `g`, `f + g` and their divisors on the boundary circle `{z : ‖z‖ = R}`.

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
  have hpos : 0 < ‖f z‖ := by
    have hlt : ‖g z‖ < ‖f z‖ := hbound z hz
    have hnonneg : 0 ≤ ‖g z‖ := norm_nonneg _
    linarith
  exact norm_pos_iff.mp hpos

/-- `f + g` does not vanish on the circle. -/
theorem fg_ne_zero_sphere {f g : ℂ → ℂ} {R : ℝ}
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖)
    {z : ℂ} (hz : ‖z‖ = R) : (f + g) z ≠ 0 := by
  have hpos : 0 < ‖(f + g) z‖ := by
    have hpos' : 0 < ‖f z‖ - ‖g z‖ := by linarith [hbound z hz]
    have hineq : |‖f z‖ - ‖-g z‖| ≤ ‖(f z) - (-g z)‖ := abs_norm_sub_norm_le (f z) (-g z)
    have h_abs : |‖f z‖ - ‖g z‖| = ‖f z‖ - ‖g z‖ := abs_of_pos hpos'
    have h_norm_neg : ‖-g z‖ = ‖g z‖ := norm_neg _
    calc
      0 < ‖f z‖ - ‖g z‖ := hpos'
      _ = |‖f z‖ - ‖g z‖| := by symm; exact h_abs
      _ = |‖f z‖ - ‖-g z‖| := by rw [h_norm_neg]
      _ ≤ ‖(f z) - (-g z)‖ := hineq
      _ = ‖(f + g) z‖ := by simp [Pi.add_apply]
  exact norm_pos_iff.mp hpos

/-- `f` is analytic and nonzero near the circle: its meromorphic order is `0`. -/
theorem f_analytic_sphere {f g : ℂ → ℂ} {R : ℝ}
    (hf : MeromorphicNFOn f Set.univ)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖)
    {z : ℂ} (hz : ‖z‖ = R) :
    meromorphicOrderAt f z = 0 ∧ AnalyticAt ℂ f z ∧ f z ≠ 0 := by
  have hfz : MeromorphicNFAt f z := hf (Set.mem_univ z)
  have hfz_ne : f z ≠ 0 := by
    intro hzero
    have hzero_norm : ‖f z‖ = 0 := by simp [hzero]
    have hlt : ‖g z‖ < 0 := by
      calc
        ‖g z‖ < ‖f z‖ := hbound z hz
        _ = 0 := hzero_norm
    have h_nonneg : 0 ≤ ‖g z‖ := norm_nonneg _
    linarith
  have horder : meromorphicOrderAt f z = 0 :=
    (hfz.meromorphicOrderAt_eq_zero_iff.mpr hfz_ne)
  have hanalytic : AnalyticAt ℂ f z :=
    (hfz.meromorphicOrderAt_nonneg_iff_analyticAt).mp (by
      simp [horder])
  exact ⟨horder, hanalytic, hfz_ne⟩

/-- `f + g` is analytic and nonzero near the circle: its meromorphic order is `0`. -/
theorem fg_analytic_sphere {f g : ℂ → ℂ} {R : ℝ}
    (hf : MeromorphicNFOn f Set.univ)
    (hg : AnalyticOn ℂ g Set.univ)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖)
    {z : ℂ} (hz : ‖z‖ = R) :
    AnalyticAt ℂ (f + g) z ∧ (f + g) z ≠ 0 ∧ meromorphicOrderAt (f + g) z = 0 := by
  have h_f_analytic : AnalyticAt ℂ f z :=
    (f_analytic_sphere hf hbound hz).right.left
  have h_g_analytic : AnalyticAt ℂ g z :=
    hg.analyticAt (isOpen_univ.mem_nhds (Set.mem_univ z))
  have h_sum_analytic : AnalyticAt ℂ (f + g) z :=
    AnalyticAt.add h_f_analytic h_g_analytic
  have h_sum_ne_zero : (f + g) z ≠ 0 :=
    fg_ne_zero_sphere hbound hz
  have h_meromorphicOrder_zero : meromorphicOrderAt (f + g) z = 0 := by
    rw [h_sum_analytic.meromorphicOrderAt_eq,
      (h_sum_analytic.analyticOrderAt_eq_zero.mpr h_sum_ne_zero)]
    simp
  exact ⟨h_sum_analytic, h_sum_ne_zero, h_meromorphicOrder_zero⟩

/-- A point of `D` where `h` has meromorphic order `0` is off the divisor. -/
theorem divisor_eq_zero_of_orderZero {h : ℂ → ℂ} {R : ℝ}
    (hh : MeromorphicOn h Set.univ)
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) R)
    (horder : meromorphicOrderAt h z = 0) :
    (divisor h (Metric.closedBall 0 R)) z = 0 := by
  have hh' : MeromorphicOn h (Metric.closedBall (0 : ℂ) R) :=
    hh.mono_set (Set.subset_univ _)
  rw [MeromorphicOn.divisor_apply hh' hz, horder]
  simp

/-- `f`'s divisor vanishes on the circle. -/
theorem divisor_f_zero_sphere {f g : ℂ → ℂ} {R : ℝ}
    (hf : MeromorphicNFOn f Set.univ)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖)
    {z : ℂ} (hz : ‖z‖ = R) :
    (divisor f (Metric.closedBall 0 R)) z = 0 := by
  have horder := (f_analytic_sphere hf hbound hz).1
  have hcl : z ∈ Metric.closedBall (0 : ℂ) R := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact le_of_eq hz
  exact divisor_eq_zero_of_orderZero hf.meromorphicOn hcl horder

/-- `f + g`'s divisor vanishes on the circle. -/
theorem divisor_fg_zero_sphere {f g : ℂ → ℂ} {R : ℝ}
    (hf : MeromorphicNFOn f Set.univ)
    (hg : AnalyticOn ℂ g Set.univ)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖)
    {z : ℂ} (hz : ‖z‖ = R) :
    (divisor (f + g) (Metric.closedBall 0 R)) z = 0 := by
  have hfg_order : meromorphicOrderAt (f + g) z = 0 :=
    (fg_analytic_sphere hf hg hbound hz).right.right
  have hz_closed : z ∈ Metric.closedBall (0 : ℂ) R := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact le_of_eq hz
  have hfg_merm : MeromorphicOn (f + g) Set.univ := by
    have hf_merm : MeromorphicOn f Set.univ := hf.meromorphicOn
    have hg_merm : MeromorphicOn g Set.univ :=
      fun z hz_univ =>
        have hg_analytic_at : AnalyticAt ℂ g z :=
          (analyticWithinAt_univ.mp (hg z hz_univ))
        hg_analytic_at.meromorphicAt
    exact hf_merm.add hg_merm
  exact divisor_eq_zero_of_orderZero hfg_merm hz_closed hfg_order

/-- The divisors of `f` and `f + g` are supported in the open disk. -/
theorem divisor_support_open {f g : ℂ → ℂ} {R : ℝ}
    (hf : MeromorphicNFOn f Set.univ)
    (hg : AnalyticOn ℂ g Set.univ)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖) :
    (divisor f (Metric.closedBall 0 R)).support ⊆ Metric.ball 0 R ∧
      (divisor (f + g) (Metric.closedBall 0 R)).support ⊆ Metric.ball 0 R := by
  constructor
  · intro z hz
    rw [Function.mem_support] at hz
    have hz_closed : z ∈ Metric.closedBall (0 : ℂ) R := by
      rw [divisor_def] at hz
      split_ifs at hz with h
      · exact h.2
      · exact (hz rfl).elim
    by_cases hz_ball : z ∈ Metric.ball (0 : ℂ) R
    · exact hz_ball
    · exfalso
      have hsphere : ‖z‖ = R := by
        have hle : dist z (0 : ℂ) ≤ R := Metric.mem_closedBall.1 hz_closed
        have hge : ¬dist z (0 : ℂ) < R := by
          rw [Metric.mem_ball] at hz_ball
          exact hz_ball
        have hdist : dist z (0 : ℂ) = ‖z‖ := by simp
        rw [hdist] at hle hge
        exact le_antisymm hle (by linarith)
      have hzero : (divisor f (Metric.closedBall 0 R)) z = 0 :=
        divisor_f_zero_sphere hf hbound hsphere
      rw [hzero] at hz
      exact hz rfl
  · intro z hz
    rw [Function.mem_support] at hz
    have hz_closed : z ∈ Metric.closedBall (0 : ℂ) R := by
      rw [divisor_def] at hz
      split_ifs at hz with h
      · exact h.2
      · exact (hz rfl).elim
    by_cases hz_ball : z ∈ Metric.ball (0 : ℂ) R
    · exact hz_ball
    · exfalso
      have hsphere : ‖z‖ = R := by
        have hle : dist z (0 : ℂ) ≤ R := Metric.mem_closedBall.1 hz_closed
        have hge : ¬dist z (0 : ℂ) < R := by
          rw [Metric.mem_ball] at hz_ball
          exact hz_ball
        have hdist : dist z (0 : ℂ) = ‖z‖ := by simp
        rw [hdist] at hle hge
        exact le_antisymm hle (by linarith)
      have hzero : (divisor (f + g) (Metric.closedBall 0 R)) z = 0 :=
        divisor_fg_zero_sphere hf hg hbound hsphere
      rw [hzero] at hz
      exact hz rfl

end ComplexAnalysis
end LeanEval
