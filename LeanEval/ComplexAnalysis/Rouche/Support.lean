import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Mathlib.Analysis.Meromorphic.Divisor
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

/-! ## The argument principle -/

/-- Logarithmic derivative of a single power factor `(· - u) ^ n`. -/
theorem logDeriv_zpow_shift (u : ℂ) (n : ℤ) {z : ℂ} (hz : z ≠ u) :
    logDeriv (fun w => (w - u) ^ n) z = (n : ℂ) * (z - u)⁻¹ := by
  have hdf : DifferentiableAt ℂ (fun w => w - u) z :=
    (differentiableAt_id (x := z)).sub_const u
  have hlog_sub : logDeriv (fun w => w - u) z = (z - u)⁻¹ := by
    calc
      logDeriv (fun w => w - u) z = deriv (fun w => w - u) z / (z - u) := by rw [logDeriv_apply]
      _ = deriv (fun w : ℂ => w) z / (z - u) := by rw [deriv_sub_const u]
      _ = (1 : ℂ) / (z - u) := by rw [deriv_id'']
      _ = (z - u)⁻¹ := by rw [one_div]
  calc
    logDeriv (fun w => (w - u) ^ n) z = n * logDeriv (fun w => w - u) z := by
      rw [logDeriv_fun_zpow hdf n]
    _ = (n : ℂ) * (z - u)⁻¹ := by rw [hlog_sub]

/-- Logarithmic derivative of a factorized rational function. -/
theorem logDeriv_factorizedRational {d : ℂ → ℤ} (hd : Function.HasFiniteSupport d)
    {z : ℂ} (hz : z ∉ Function.support d) :
    logDeriv (∏ᶠ u, (fun w => w - u) ^ d u) z = ∑ᶠ u, (d u : ℂ) * (z - u)⁻¹ := by
  sorry

/-- Each simple pole `(· - u)⁻¹` with `u` in the open disk is circle-integrable. -/
theorem circleIntegrable_sub_inv {R : ℝ} {u : ℂ} (hu : u ∈ Metric.ball (0 : ℂ) R) :
    CircleIntegrable (fun z => (z - u)⁻¹) 0 R := by
  rw [circleIntegrable_sub_inv_iff]
  have hpos : 0 < R := by
    have hdist : dist u (0 : ℂ) < R := Metric.mem_ball.1 hu
    have hnonneg : 0 ≤ dist u (0 : ℂ) := dist_nonneg
    linarith
  right
  intro h
  have hsphere : dist u (0 : ℂ) = |R| := Metric.mem_sphere.1 h
  have habs : |R| = R := abs_of_pos hpos
  rw [habs] at hsphere
  have hball : dist u (0 : ℂ) < R := Metric.mem_ball.1 hu
  linarith

/-- Cauchy integral of a single simple pole. -/
theorem circleIntegral_sub_inv {R : ℝ} {u : ℂ} (hu : u ∈ Metric.ball (0 : ℂ) R) :
    (∮ z in C(0, R), (z - u)⁻¹) = 2 * (Real.pi : ℂ) * Complex.I := by
  simpa using circleIntegral.integral_sub_inv_of_mem_ball hu

/-- Contour integral of a finite sum of simple poles. -/
theorem circleIntegral_sum_inv {R : ℝ} {d : ℂ → ℤ} (hd : Function.HasFiniteSupport d)
    (hsupp : Function.support d ⊆ Metric.ball (0 : ℂ) R) :
    (∮ z in C(0, R), ∑ᶠ u, (d u : ℂ) * (z - u)⁻¹)
      = (∑ᶠ u, (d u : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I) := by
  let s : Finset ℂ := hd.toFinset
  have hsu : ∀ u ∈ s, u ∈ Metric.ball (0 : ℂ) R := by
    intro u hu
    apply hsupp
    rw [Set.Finite.mem_toFinset] at hu
    exact hu
  have h_int_sub : ∀ u ∈ s, CircleIntegrable (fun (z : ℂ) => (z - u)⁻¹) 0 R := by
    intro u hu
    exact circleIntegrable_sub_inv (hsu u hu)
  have h_int_all : ∀ u ∈ s, CircleIntegrable (fun (z : ℂ) => (d u : ℂ) * (z - u)⁻¹) 0 R := by
    intro u hu
    simpa [smul_eq_mul] using CircleIntegrable.const_fun_smul (a := (d u : ℂ)) (h_int_sub u hu)
  have h_finsum_eq : (fun (z : ℂ) => ∑ᶠ u, (d u : ℂ) * (z - u)⁻¹)
      = (fun (z : ℂ) => ∑ u ∈ s, (d u : ℂ) * (z - u)⁻¹) := by
    ext z
    have h_support : Function.support (fun (u : ℂ) => (d u : ℂ) * ((z : ℂ) - u)⁻¹) ⊆ (s : Set ℂ) := by
      intro u hu
      have hmem : u ∈ Function.support d := by
        rw [Function.mem_support]
        intro hzero
        apply hu
        simp [hzero]
      simpa [s] using (hd.mem_toFinset.mpr hmem)
    rw [finsum_eq_finset_sum_of_support_subset (fun (u : ℂ) => (d u : ℂ) * ((z : ℂ) - u)⁻¹) h_support]
  have h_finsum2 : ∑ᶠ u, (d u : ℂ) = ∑ u ∈ s, (d u : ℂ) := by
    have h_support2 : Function.support (fun (u : ℂ) => (d u : ℂ)) ⊆ (s : Set ℂ) := by
      intro u hu
      have hmem : u ∈ Function.support d := by
        rw [Function.mem_support]
        intro hzero
        apply hu
        simp [hzero]
      simpa [s] using (hd.mem_toFinset.mpr hmem)
    rw [finsum_eq_finset_sum_of_support_subset (fun (u : ℂ) => (d u : ℂ)) h_support2]
  calc
    (∮ z in C(0, R), ∑ᶠ u, (d u : ℂ) * (z - u)⁻¹)
        = (∮ z in C(0, R), ∑ u ∈ s, (d u : ℂ) * (z - u)⁻¹) := by
      rw [h_finsum_eq]
    _ = ∑ u ∈ s, (∮ z in C(0, R), (d u : ℂ) * (z - u)⁻¹) := by
      rw [circleIntegral.integral_fun_sum h_int_all]
    _ = ∑ u ∈ s, (d u : ℂ) * (∮ z in C(0, R), (z - u)⁻¹) := by
      refine Finset.sum_congr rfl fun u hu => ?_
      rw [circleIntegral.integral_const_mul (d u : ℂ) (fun z : ℂ => (z - u)⁻¹) 0 R]
    _ = ∑ u ∈ s, (d u : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      refine Finset.sum_congr rfl fun u hu => ?_
      rw [circleIntegral_sub_inv (hsu u hu)]
    _ = (∑ u ∈ s, (d u : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I) := by
      rw [Finset.sum_mul]
    _ = (∑ᶠ u, (d u : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I) := by
      rw [h_finsum2]

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
  by_cases hAne : A.Nonempty
  · let m := A.min' hAne
    have hm_mem : m ∈ A := Finset.min'_mem _ hAne
    refine ⟨m, hA m hm_mem, λ a ha => Finset.min'_le _ a ha⟩
  · refine ⟨R + 1, by linarith, λ a ha => ?_⟩
    exfalso; exact hAne ⟨a, ha⟩

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
  rcases hne with ⟨w, hw⟩
  have h_univ_preconnected : IsPreconnected (Set.univ : Set ℂ) :=
    (preconnectedSpace_iff_univ.mp inferInstance)
  exact hh.meromorphicOrderAt_ne_top_of_isPreconnected h_univ_preconnected
    (Set.mem_univ w) (Set.mem_univ z) hw

/-- The factorized rational of `h` on the larger disk `B'` restricts to the
factorized rational on the closed disk `D`, provided the divisor on `B'` is
supported in `D`. -/
theorem factorizedRational_restrict {h : ℂ → ℂ} {R R' : ℝ}
    (hh : MeromorphicOn h Set.univ)
    (hsub : Metric.closedBall (0 : ℂ) R ⊆ Metric.ball 0 R')
    (hsupp : (divisor h (Metric.ball 0 R')).support ⊆ Metric.closedBall 0 R) :
    (∏ᶠ u, (fun x => x - u) ^ (divisor h (Metric.ball 0 R')) u)
      = (∏ᶠ u, (fun x => x - u) ^ (divisor h (Metric.closedBall 0 R)) u) := by
  have hh_ball : MeromorphicOn h (Metric.ball 0 R') :=
    hh.mono_set (Set.subset_univ _)
  have hrestrict_eq := MeromorphicOn.divisor_restrict hh_ball hsub
  have hdiv_eq : ∀ (z : ℂ), (divisor h (Metric.ball 0 R')) z = (divisor h (Metric.closedBall 0 R)) z := by
    intro z
    by_cases hz : z ∈ Metric.closedBall (0 : ℂ) R
    · calc
        (divisor h (Metric.ball 0 R')) z = ((divisor h (Metric.ball 0 R')).restrict hsub) z := by
          simp [Function.locallyFinsuppWithin.restrict_apply, hz]
        _ = divisor h (Metric.closedBall 0 R) z := by rw [hrestrict_eq]
    · have hz_not_support : z ∉ (divisor h (Metric.ball 0 R')).support :=
        fun hz_support => hz (hsupp hz_support)
      have hz_closedBall_zero : divisor h (Metric.closedBall 0 R) z = 0 := by
        calc
          divisor h (Metric.closedBall 0 R) z = ((divisor h (Metric.ball 0 R')).restrict hsub) z := by
            rw [hrestrict_eq]
          _ = 0 := by simp [hz]
      have hz_ball_zero : (divisor h (Metric.ball 0 R')) z = 0 := by
        simpa using ((Function.mem_support (f := divisor h (Metric.ball 0 R')) (x := z)).not).mp hz_not_support
      simp [hz_ball_zero, hz_closedBall_zero]
  refine finprod_congr ?_
  intro u
  simp [hdiv_eq u]

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
  rcases annulus_zero_free hh horder with ⟨R', hR', hsupp⟩
  have hh_closedBall' : MeromorphicOn h (Metric.closedBall (0 : ℂ) R') :=
    hh.mono_set (Set.subset_univ _)
  have h_fin_closed : (divisor h (Metric.closedBall (0 : ℂ) R')).support.Finite :=
    (divisor h (Metric.closedBall (0 : ℂ) R')).finiteSupport (isCompact_closedBall (0 : ℂ) R')
  have hdiv_finite : (divisor h (Metric.ball (0 : ℂ) R')).support.Finite := by
    have h_sub : (divisor h (Metric.ball (0 : ℂ) R')).support ⊆
        (divisor h (Metric.closedBall (0 : ℂ) R')).support := by
      intro z hz
      have hz' : (divisor h (Metric.ball (0 : ℂ) R')) z ≠ 0 := hz
      have hz_ball : z ∈ Metric.ball (0 : ℂ) R' := by
        rw [divisor_def] at hz'
        split_ifs at hz' with h
        · exact h.2
        · simp at hz'
      have hz_closedBall_ne_zero : (divisor h (Metric.closedBall (0 : ℂ) R')) z ≠ 0 := by
        have h_restrict_eq : (divisor h (Metric.ball (0 : ℂ) R')) z =
            (divisor h (Metric.closedBall (0 : ℂ) R')) z := by
          calc
            (divisor h (Metric.ball (0 : ℂ) R')) z
                = ((divisor h (Metric.closedBall (0 : ℂ) R')).restrict Metric.ball_subset_closedBall) z := by
              rw [divisor_restrict hh_closedBall' Metric.ball_subset_closedBall]
            _ = (divisor h (Metric.closedBall (0 : ℂ) R')) z := by
              rw [Function.locallyFinsuppWithin.restrict_apply, if_pos hz_ball]
        intro hzero
        apply hz'
        calc
          (divisor h (Metric.ball (0 : ℂ) R')) z = (divisor h (Metric.closedBall (0 : ℂ) R')) z := h_restrict_eq
          _ = 0 := hzero
      exact hz_closedBall_ne_zero
    exact h_fin_closed.subset h_sub
  have h_order_finite : ∀ u : Metric.ball (0 : ℂ) R', meromorphicOrderAt h u ≠ ⊤ := by
    intro u
    exact order_ne_top hh hne u
  rcases MeromorphicOn.extract_zeros_poles (hh.mono_set (Set.subset_univ _))
    h_order_finite hdiv_finite with ⟨g, hg_ana, hg_ne, h_eq⟩
  have h_sub : Metric.closedBall (0 : ℂ) R ⊆ Metric.ball (0 : ℂ) R' := by
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hx
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    exact lt_of_le_of_lt hx hR'
  have hsupp' : (divisor h (Metric.ball (0 : ℂ) R')).support ⊆ Metric.closedBall 0 R :=
    Set.Subset.trans hsupp (Metric.ball_subset_closedBall)
  have hprod_eq : (∏ᶠ u, (fun x => x - u) ^ (divisor h (Metric.ball (0 : ℂ) R')) u) =
      (∏ᶠ u, (fun x => x - u) ^ (divisor h (Metric.closedBall 0 R)) u) :=
    factorizedRational_restrict hh h_sub hsupp'
  have h_eq' : h =ᶠ[Filter.codiscreteWithin (Metric.ball (0 : ℂ) R')]
      (∏ᶠ u, (fun x => x - u) ^ (divisor h (Metric.closedBall 0 R)) u) • g := by
    filter_upwards [h_eq] with x hx
    simpa [hprod_eq] using hx
  have h_filter_le : Filter.codiscreteWithin (Metric.closedBall (0 : ℂ) R) ≤
      Filter.codiscreteWithin (Metric.ball (0 : ℂ) R') := by
    exact Filter.codiscreteWithin.mono h_sub
  have h_eq_closedBall : h =ᶠ[Filter.codiscreteWithin (Metric.closedBall (0 : ℂ) R)]
      (∏ᶠ u, (fun x => x - u) ^ (divisor h (Metric.closedBall 0 R)) u) • g :=
    h_eq'.filter_mono h_filter_le
  have hg_ana_closedBall : AnalyticOnNhd ℂ g (Metric.closedBall (0 : ℂ) R) :=
    hg_ana.mono h_sub
  have hg_ne_closedBall : ∀ z ∈ Metric.closedBall (0 : ℂ) R, g z ≠ 0 := by
    intro z hz
    exact hg_ne ⟨z, h_sub hz⟩
  exact ⟨g, hg_ana_closedBall, hg_ne_closedBall, h_eq_closedBall⟩

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
  have hsupp : (divisor h (Metric.closedBall 0 R)).support ⊆ Metric.ball 0 R := by
    intro z hz
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
      have hzero : (divisor h (Metric.closedBall 0 R)) z = 0 :=
        divisor_eq_zero_of_orderZero hh hz_closed (horder z hsphere)
      rw [hzero] at hz
      exact hz rfl
  rcases factorization_existence hh hne horder with ⟨U, hUana, hU0, hfact⟩
  have hsplit := argument_principle_integral_split hh horder hUana hU0 hfact
  have hUint : (∮ z in C(0, R), logDeriv U z) = 0 :=
    circleIntegral_logDeriv_unit hUana hU0
  have hφint : (∮ z in C(0, R),
      logDeriv (∏ᶠ u, (fun x => x - u) ^ (divisor h (Metric.closedBall 0 R)) u) z)
    = (∑ᶠ u, ((divisor h (Metric.closedBall 0 R)) u : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I) :=
    circleIntegral_logDeriv_factorizedRational hsupp
  calc
    (∮ z in C(0, R), logDeriv h z)
        = (∮ z in C(0, R),
            logDeriv (∏ᶠ u, (fun x => x - u) ^ (divisor h (Metric.closedBall 0 R)) u) z)
          + (∮ z in C(0, R), logDeriv U z) := hsplit
    _ = (∮ z in C(0, R),
        logDeriv (∏ᶠ u, (fun x => x - u) ^ (divisor h (Metric.closedBall 0 R)) u) z) + 0 := by rw [hUint]
    _ = (∑ᶠ u, ((divisor h (Metric.closedBall 0 R)) u : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I) := by
      rw [hφint, add_zero]

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

/-! ## Matching pole divisors and conclusion -/

/-- Nonnegative order of `f` is preserved by adding the analytic `g`. -/
theorem order_nonneg_of_pole {f g : ℂ → ℂ}
    (hf : MeromorphicNFOn f Set.univ)
    (hg : AnalyticOn ℂ g Set.univ) (z : ℂ)
    (h : 0 ≤ meromorphicOrderAt f z) : 0 ≤ meromorphicOrderAt (f + g) z := by
  have hf_mero : MeromorphicAt f z := (hf (Set.mem_univ z)).meromorphicAt
  have hg_analytic : AnalyticAt ℂ g z := hg.analyticAt (isOpen_univ.mem_nhds (Set.mem_univ z))
  have hg_mero : MeromorphicAt g z := hg_analytic.meromorphicAt
  have hg_nonneg : 0 ≤ meromorphicOrderAt g z := hg_analytic.meromorphicOrderAt_nonneg
  have h_min_nonneg : 0 ≤ min (meromorphicOrderAt f z) (meromorphicOrderAt g z) :=
    le_min h hg_nonneg
  have h_add_ineq : min (meromorphicOrderAt f z) (meromorphicOrderAt g z) ≤ meromorphicOrderAt (f + g) z :=
    meromorphicOrderAt_add hf_mero hg_mero
  exact le_trans h_min_nonneg h_add_ineq

/-- At a pole of `f` the order of `f + g` equals that of `f`. -/
theorem order_eq_at_pole {f g : ℂ → ℂ}
    (hf : MeromorphicNFOn f Set.univ)
    (hg : AnalyticOn ℂ g Set.univ) (z : ℂ)
    (h : meromorphicOrderAt f z < 0) :
    meromorphicOrderAt (f + g) z = meromorphicOrderAt f z := by
  have hf_merm : MeromorphicAt f z := (hf (Set.mem_univ z)).meromorphicAt
  have hg_ana : AnalyticAt ℂ g z := hg.analyticAt (isOpen_univ.mem_nhds (Set.mem_univ z))
  have hg_merm : MeromorphicAt g z := hg_ana.meromorphicAt
  have hg_ord_nonneg : 0 ≤ meromorphicOrderAt g z := hg_ana.meromorphicOrderAt_nonneg
  have h_lt : meromorphicOrderAt f z < meromorphicOrderAt g z :=
    lt_of_lt_of_le h hg_ord_nonneg
  have h_eq : meromorphicOrderAt (g + f) z = meromorphicOrderAt f z :=
    meromorphicOrderAt_add_eq_right_of_lt hg_merm h_lt
  simpa [add_comm] using h_eq

/-- `f` and `f + g` have the same pole divisor (negative part). -/
theorem negPart_eq {f g : ℂ → ℂ} {R : ℝ}
    (hf : MeromorphicNFOn f Set.univ)
    (hg : AnalyticOn ℂ g Set.univ)
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) R) :
    ((divisor (f + g) (Metric.closedBall 0 R))⁻) z
      = ((divisor f (Metric.closedBall 0 R))⁻) z := by
  have hz_cl : z ∈ Metric.closedBall (0 : ℂ) R := hz
  have hf_merm : MeromorphicOn f (Metric.closedBall (0 : ℂ) R) :=
    hf.meromorphicOn.mono_set (Set.subset_univ _)
  have hfg_merm : MeromorphicOn (f + g) (Metric.closedBall (0 : ℂ) R) := by
    have hf_merm_univ : MeromorphicOn f Set.univ := hf.meromorphicOn
    have hg_merm_univ : MeromorphicOn g Set.univ :=
      fun w hw_univ => (hg.analyticAt (isOpen_univ.mem_nhds hw_univ)).meromorphicAt
    exact (hf_merm_univ.add hg_merm_univ).mono_set (Set.subset_univ _)
  rw [Function.locallyFinsuppWithin.negPart_apply, Function.locallyFinsuppWithin.negPart_apply]
  rw [MeromorphicOn.divisor_apply hf_merm hz_cl, MeromorphicOn.divisor_apply hfg_merm hz_cl]
  by_cases h : 0 ≤ meromorphicOrderAt f z
  · have hfg_nonneg : 0 ≤ meromorphicOrderAt (f + g) z := order_nonneg_of_pole hf hg z h
    have hf_untop_nonneg : 0 ≤ (meromorphicOrderAt f z).untop₀ :=
      (WithTop.untop₀_nonneg (α := ℤ)).mpr h
    have hfg_untop_nonneg : 0 ≤ (meromorphicOrderAt (f + g) z).untop₀ :=
      (WithTop.untop₀_nonneg (α := ℤ)).mpr hfg_nonneg
    simp [hf_untop_nonneg, hfg_untop_nonneg]
  · have h_neg : meromorphicOrderAt f z < 0 := lt_of_not_ge h
    have heq : meromorphicOrderAt (f + g) z = meromorphicOrderAt f z :=
      order_eq_at_pole hf hg z h_neg
    simp [heq]

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
  let d := divisor h (Metric.closedBall 0 R)
  have hfinite : Function.HasFiniteSupport d := by
    have hfinite' : Set.Finite d.support :=
      Function.locallyFinsuppWithin.finiteSupport d (isCompact_closedBall 0 R)
    exact hfinite'
  have hfinite_negPart : Function.HasFiniteSupport ((d⁻ : ℂ → ℤ)) := by
    have : Function.support ((d⁻ : ℂ → ℤ)) ⊆ Function.support (d : ℂ → ℤ) := by
      intro x hx
      rw [Function.mem_support, Pi.negPart_apply] at hx
      rw [Function.mem_support]
      intro hzero
      apply hx
      simp [hzero]
    exact hfinite.subset this
  have hpointwise : ∀ z, ((d⁺ : ℂ → ℤ) z) = ((d : ℂ → ℤ) z) + ((d⁻ : ℂ → ℤ) z) := by
    intro z
    calc
      ((d⁺ : ℂ → ℤ) z) = (d z)⁺ := rfl
      _ = (d z) + (d z)⁻ := by
        have := posPart_sub_negPart (a := d z)
        linarith
      _ = ((d : ℂ → ℤ) z) + ((d⁻ : ℂ → ℤ) z) := rfl
  calc
    (∑ᶠ z, ((d⁺ : ℂ → ℤ) z)) = (∑ᶠ z, (((d : ℂ → ℤ) z) + ((d⁻ : ℂ → ℤ) z))) := by
      refine finsum_congr ?_
      intro z
      exact hpointwise z
    _ = (∑ᶠ z, ((d : ℂ → ℤ) z)) + (∑ᶠ z, ((d⁻ : ℂ → ℤ) z)) := by
      simpa using finsum_add_distrib hfinite hfinite_negPart

end ComplexAnalysis
end LeanEval
