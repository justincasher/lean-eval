import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import LeanEval.ComplexAnalysis.Rouche.Boundary

/-!
# Logarithmic-derivative and circle-integral building blocks

Proved supporting lemmas of the blueprint `rouche-theorem-via-zero-counting` used in
the argument-principle development: the logarithmic derivative of a factorized
rational, contour integrals of simple poles, the factorization existence statement
and the surrounding analytic facts.
-/

namespace LeanEval
namespace ComplexAnalysis

open MeromorphicOn

/-! ## Logarithmic derivative of factorized rationals -/

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
  -- The finite product over all `u` reduces to a product over the finite support.
  have h_mulSupport_subset : Function.mulSupport (fun u : ℂ => (fun w : ℂ => w - u) ^ d u) ⊆
      (hd.toFinset : Set ℂ) := by
    intro u hu
    have h_nonzero : d u ≠ 0 := by
      intro hzero
      apply hu
      simp [hzero]
    exact hd.mem_toFinset.mpr (by rwa [Function.mem_support])
  have h_prod_eq : (∏ᶠ u, (fun w : ℂ => w - u) ^ d u) = ∏ u ∈ hd.toFinset, (fun w : ℂ => w - u) ^ d u :=
    finprod_eq_prod_of_mulSupport_subset _ h_mulSupport_subset
  -- For each `u` in the finite support, `z ≠ u` (otherwise `z` would be in the support of `d`).
  have hz_ne_u : ∀ u ∈ hd.toFinset, z ≠ u := by
    intro u hu
    intro h_eq
    apply hz
    have h_support : u ∈ Function.support d := hd.mem_toFinset.mp hu
    rw [h_eq]
    exact h_support
  -- Every factor is nonzero at `z`.
  have hf_nonzero : ∀ u ∈ hd.toFinset, ((fun w : ℂ => w - u) ^ d u) z ≠ 0 := by
    intro u hu
    have h_val_ne_zero : (z - u) ≠ 0 := sub_ne_zero.mpr (hz_ne_u u hu)
    simpa [Pi.pow_apply] using zpow_ne_zero (d u) h_val_ne_zero
  -- Every factor is differentiable at `z`.
  have h_diff : ∀ u ∈ hd.toFinset, DifferentiableAt ℂ ((fun w : ℂ => w - u) ^ d u) z := by
    intro u hu
    have hz_ne_u' : z ≠ u := hz_ne_u u hu
    have h_sub_diff : DifferentiableAt ℂ (fun w : ℂ => w - u) z :=
      (differentiableAt_id (x := z)).sub_const u
    have h_val_ne_zero : (fun w : ℂ => w - u) z ≠ 0 := by
      simpa [sub_ne_zero] using hz_ne_u'
    exact h_sub_diff.zpow (m := d u) (Or.inl h_val_ne_zero)
  -- Apply the logarithmic derivative rule for a finite product.
  have h_log_prod : logDeriv (∏ u ∈ hd.toFinset, (fun w : ℂ => w - u) ^ d u) z
      = ∑ u ∈ hd.toFinset, logDeriv ((fun w : ℂ => w - u) ^ d u) z := by
    have htemp := logDeriv_prod hf_nonzero h_diff
    have h_eq_fun : (∏ u ∈ hd.toFinset, (fun w : ℂ => w - u) ^ d u) =
        (fun x : ℂ => ∏ u ∈ hd.toFinset, ((fun w : ℂ => w - u) ^ d u) x) := by
      ext x; simp
    rw [h_eq_fun]
    exact htemp
  -- Each summand simplifies by `logDeriv_zpow_shift`.
  have h_log_sum : ∑ u ∈ hd.toFinset, logDeriv ((fun w : ℂ => w - u) ^ d u) z
      = ∑ u ∈ hd.toFinset, (d u : ℂ) * (z - u)⁻¹ := by
    refine Finset.sum_congr rfl fun u hu => ?_
    simpa [Pi.pow_apply] using logDeriv_zpow_shift u (d u) (hz_ne_u u hu)
  -- The infinite sum on the right equals the finite sum over the support.
  have h_finsum_eq : ∑ᶠ u, (d u : ℂ) * (z - u)⁻¹ = ∑ u ∈ hd.toFinset, (d u : ℂ) * (z - u)⁻¹ :=
    finsum_eq_sum_of_support_subset (fun u : ℂ => (d u : ℂ) * (z - u)⁻¹) (s := hd.toFinset) (by
      intro u hu
      have h_nonzero : (d u : ℂ) * (z - u)⁻¹ ≠ 0 := hu
      have h_d_nonzero : d u ≠ 0 := by
        intro hzero
        apply h_nonzero
        simp [hzero]
      have h_support : u ∈ Function.support d := by
        rw [Function.mem_support]
        exact h_d_nonzero
      rw [Finset.mem_coe, hd.mem_toFinset]
      exact h_support)
  -- Combine everything.
  calc
    logDeriv (∏ᶠ u, (fun w : ℂ => w - u) ^ d u) z
        = logDeriv (∏ u ∈ hd.toFinset, (fun w : ℂ => w - u) ^ d u) z := by rw [h_prod_eq]
    _ = ∑ u ∈ hd.toFinset, logDeriv ((fun w : ℂ => w - u) ^ d u) z := h_log_prod
    _ = ∑ u ∈ hd.toFinset, (d u : ℂ) * (z - u)⁻¹ := h_log_sum
    _ = ∑ᶠ u, (d u : ℂ) * (z - u)⁻¹ := by rw [h_finsum_eq]

/-! ## Contour integrals of simple poles -/

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

/-! ## Analytic units and the factorization existence statement -/

/-- The logarithmic derivative of a unit (analytic and nowhere zero on the closed
disk) is analytic on the closed disk. -/
theorem logDeriv_analytic_unit {R : ℝ} {U : ℂ → ℂ}
    (hUana : AnalyticOnNhd ℂ U (Metric.closedBall 0 R))
    (hU0 : ∀ z ∈ Metric.closedBall (0 : ℂ) R, U z ≠ 0) :
    AnalyticOnNhd ℂ (logDeriv U) (Metric.closedBall 0 R) := by
  intro z hz
  have hUz : AnalyticAt ℂ U z := hUana z hz
  have hderivUz : AnalyticAt ℂ (deriv U) z := hUana.deriv z hz
  have hUz_ne : U z ≠ 0 := hU0 z hz
  have h_log_analytic : AnalyticAt ℂ (deriv U / U) z :=
    hderivUz.div hUz hUz_ne
  simpa [logDeriv_apply] using h_log_analytic

/-- For `R > 0` the closed disk is preperfect. -/
theorem closedBall_preperfect {R : ℝ} (hR : 0 < R) :
    Preperfect (Metric.closedBall (0 : ℂ) R) := by
  have hR_ne_zero : R ≠ 0 := by linarith
  have hball : Preperfect (Metric.ball (0 : ℂ) R) :=
    Metric.isOpen_ball.preperfect
  have hperf : Perfect (closure (Metric.ball (0 : ℂ) R)) :=
    hball.perfect_closure
  have hcl : closure (Metric.ball (0 : ℂ) R) = Metric.closedBall (0 : ℂ) R :=
    closure_ball (0 : ℂ) hR_ne_zero
  rw [hcl] at hperf
  exact hperf.acc

/-- Both sides of the factorization `h = φ · U` are meromorphic at each point of the
closed disk. -/
theorem factorization_meromorphicAt {h : ℂ → ℂ} {R : ℝ}
    (hh : MeromorphicOn h Set.univ)
    {U : ℂ → ℂ} (hUana : AnalyticOnNhd ℂ U (Metric.closedBall 0 R))
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) R) :
    MeromorphicAt h z ∧
      MeromorphicAt
        ((∏ᶠ u, (fun x => x - u) ^ (divisor h (Metric.closedBall 0 R)) u) • U) z := by
  have hz_univ : z ∈ Set.univ := Set.mem_univ z
  have hmerm_h : MeromorphicAt h z := hh z hz_univ
  have hU_analytic : AnalyticAt ℂ U z := hUana z hz
  have hmerm_U : MeromorphicAt U z := hU_analytic.meromorphicAt
  have hmerm_factor : MeromorphicAt (∏ᶠ u, (fun x => x - u) ^ (divisor h (Metric.closedBall 0 R)) u) z := by
    refine MeromorphicAt.finprod ?_
    intro u
    have h_id_merm : MeromorphicAt (fun x : ℂ => x) z :=
      (analyticAt_id (z := z)).meromorphicAt
    have h_const_merm : MeromorphicAt (fun _ : ℂ => u) z :=
      (analyticAt_const (v := u) (x := z)).meromorphicAt
    have h_affine_merm : MeromorphicAt (fun x : ℂ => x - u) z :=
      h_id_merm.sub h_const_merm
    exact h_affine_merm.zpow ((divisor h (Metric.closedBall 0 R)) u)
  have hmerm_smul : MeromorphicAt
    ((∏ᶠ u, (fun x => x - u) ^ (divisor h (Metric.closedBall 0 R)) u) • U) z :=
    hmerm_factor.smul hmerm_U
  exact ⟨hmerm_h, hmerm_smul⟩

/-- `logDeriv φ` is circle-integrable, where `φ` is the factorized rational of
`divisor h D` supported in the open disk. -/
theorem circleIntegrable_logDeriv_factorizedRational {h : ℂ → ℂ} {R : ℝ}
    (hsupp : (divisor h (Metric.closedBall 0 R)).support ⊆ Metric.ball 0 R) :
    CircleIntegrable
      (logDeriv (∏ᶠ u, (fun x => x - u) ^ (divisor h (Metric.closedBall 0 R)) u)) 0 R := by
  let d := divisor h (Metric.closedBall 0 R)
  have hfinite : Function.HasFiniteSupport d :=
    Function.locallyFinsuppWithin.finiteSupport d (isCompact_closedBall 0 R)
  by_cases hRnonneg : 0 ≤ R
  · have habs : |R| = R := abs_of_nonneg hRnonneg
    -- The family (d u) * (· - u)⁻¹ has finite support, so finsum_apply applies
    have hF_finsupport : Function.HasFiniteSupport (fun (u : ℂ) (z : ℂ) => (d u : ℂ) * (z - u)⁻¹) := by
      refine hfinite.subset ?_
      intro u hu
      rw [Function.mem_support] at hu ⊢
      intro hzero
      apply hu
      ext z
      simp [hzero]
    -- Each term is circle-integrable
    have h_int_each : ∀ u : ℂ, CircleIntegrable (fun z : ℂ => (d u : ℂ) * (z - u)⁻¹) 0 R := by
      intro u
      by_cases hu : u ∈ d.support
      · have hu_ball : u ∈ Metric.ball (0 : ℂ) R := hsupp hu
        have h_int_sub : CircleIntegrable (fun z => (z - u)⁻¹) 0 R := circleIntegrable_sub_inv hu_ball
        simpa [smul_eq_mul] using CircleIntegrable.const_fun_smul (a := (d u : ℂ)) h_int_sub
      · have hd_zero : (d u : ℂ) = 0 := by
          simpa [Function.mem_support] using hu
        simp [hd_zero, circleIntegrable_const]
    -- The finite sum is circle-integrable
    set F := ∑ᶠ u, (fun z : ℂ => (d u : ℂ) * (z - u)⁻¹) with hF
    have hF_int : CircleIntegrable F 0 R := CircleIntegrable.finsum h_int_each
    -- On the sphere, logDeriv φ and F agree pointwise
    have hsphere_eq : Set.EqOn (logDeriv (∏ᶠ u, (fun x => x - u) ^ d u)) F
        (Metric.sphere (0 : ℂ) |R|) := by
      intro z hz
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hz
      rw [habs] at hz
      have hz_not_support : z ∉ Function.support d := by
        intro hz_support
        have hz_ball : z ∈ Metric.ball (0 : ℂ) R := hsupp hz_support
        rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hz_ball
        linarith
      calc
        logDeriv (∏ᶠ u, (fun x => x - u) ^ d u) z = ∑ᶠ u, (d u : ℂ) * (z - u)⁻¹ :=
          logDeriv_factorizedRational hfinite hz_not_support
        _ = F z := by
          simp [F, finsum_apply hF_finsupport z]
    -- Convert pointwise equality to an `EventuallyEq` for the codiscrete filter
    have h_codisc : logDeriv (∏ᶠ u, (fun x => x - u) ^ d u) =ᶠ[
        Filter.codiscreteWithin (Metric.sphere (0 : ℂ) |R|)] F := by
      filter_upwards [Filter.self_mem_codiscreteWithin (Metric.sphere (0 : ℂ) |R|)] with z hz
      exact hsphere_eq hz
    -- Transfer circle-integrability across equality on the sphere
    exact ((circleIntegrable_congr_codiscreteWithin h_codisc).mpr hF_int)
  · -- When R < 0, the ball is empty, so d is identically zero
    have hd_zero : d = 0 := by
      ext u
      by_contra! hne
      have hmem_support : u ∈ Function.support d := by
        rw [Function.mem_support]
        exact hne
      have hu_ball : u ∈ Metric.ball (0 : ℂ) R := hsupp hmem_support
      have hball_empty : Metric.ball (0 : ℂ) R = ∅ :=
        (Metric.ball_eq_empty).mpr (by linarith)
      rw [hball_empty] at hu_ball
      exact hu_ball
    have h_prod : (∏ᶠ u, (fun x => x - u) ^ d u) = 1 := by
      simp [hd_zero]
    have h_log : logDeriv (1 : ℂ → ℂ) = (0 : ℂ → ℂ) := by
      ext z; simp [logDeriv_apply]
    rw [h_prod, h_log]
    exact circleIntegrable_const (a := (0 : ℂ)) (c := 0) (R := R)

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
  -- The closed disk of radius R+1 is compact, so the divisor's support there is finite.
  set K := Metric.closedBall (0 : ℂ) (R + 1) with hK
  have hK_compact : IsCompact K := isCompact_closedBall (0 : ℂ) (R + 1)
  have hhK : MeromorphicOn h K := hh.mono_set (Set.subset_univ _)
  have hfin_support : Set.Finite (divisor h K).support :=
    (divisor h K).finiteSupport hK_compact

  -- Points on the circle ‖z‖ = R have divisor zero on the closed disk of radius R+1.
  have h_circle_zero : ∀ z : ℂ, ‖z‖ = R → (divisor h K) z = 0 := by
    intro z hz
    have hz_closedBall_R : z ∈ Metric.closedBall (0 : ℂ) R := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact le_of_eq hz
    have hz_divisor_R_zero : (divisor h (Metric.closedBall (0 : ℂ) R)) z = 0 :=
      divisor_eq_zero_of_orderZero hh hz_closedBall_R (horder z hz)
    have hsub : Metric.closedBall (0 : ℂ) R ⊆ K := by
      intro x hx
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hx
      rw [hK, Metric.mem_closedBall, dist_eq_norm, sub_zero]
      nlinarith
    have hrestrict_eq := MeromorphicOn.divisor_restrict hhK hsub
    calc
      (divisor h K) z = ((divisor h K).restrict hsub) z := by
        simp [Function.locallyFinsuppWithin.restrict_apply, hz_closedBall_R]
      _ = divisor h (Metric.closedBall (0 : ℂ) R) z := by rw [hrestrict_eq]
      _ = 0 := hz_divisor_R_zero

  -- Consider the support points outside the open disk of radius R.
  let S : Set ℂ := (divisor h K).support \ Metric.ball (0 : ℂ) R
  have hS_fin : Set.Finite S := hfin_support.subset (by
    intro x hx; exact hx.1)

  -- Every point in S has norm > R (since those with norm = R have divisor zero).
  have hS_norm_gt_R : ∀ z ∈ S, R < ‖z‖ := by
    intro z hz
    rcases hz with ⟨hz_supp, hz_not_ball⟩
    have hz_norm_ge_R : R ≤ ‖z‖ := by
      by_contra! hlt
      apply hz_not_ball
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]
      exact hlt
    have hz_norm_ne_R : ‖z‖ ≠ R := by
      intro heq
      have hzero : (divisor h K) z = 0 := h_circle_zero z heq
      exact hz_supp hzero
    exact lt_of_le_of_ne hz_norm_ge_R hz_norm_ne_R.symm

  -- Build a Finset ℝ of the norms of points in S.
  let A : Finset ℝ := (hS_fin.toFinset).image (fun z : ℂ => ‖z‖)
  have hA_gt_R : ∀ a ∈ A, R < a := by
    intro a ha
    rw [Finset.mem_image] at ha
    rcases ha with ⟨z, hz, rfl⟩
    have hz_S : z ∈ S := by
      simpa using hz
    exact hS_norm_gt_R z hz_S

  rcases exists_lt_of_finite hA_gt_R with ⟨R1, hR1_gt_R, hR1_le⟩

  -- Choose R' = min R1 (R+1), ensuring R' > R and Metric.ball 0 R' ⊆ K.
  set R' := min R1 (R + 1) with hR'
  have hR'_gt_R : R < R' := by
    have hR1_gt_R : R < R1 := hR1_gt_R
    have hRp1_gt_R : R < R + 1 := by nlinarith
    exact lt_min_iff.mpr ⟨hR1_gt_R, hRp1_gt_R⟩

  have hR'_le_Rp1 : R' ≤ R + 1 := min_le_right _ _
  have hball_sub_K : Metric.ball (0 : ℂ) R' ⊆ K := by
    intro x hx
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hx
    rw [hK, Metric.mem_closedBall, dist_eq_norm, sub_zero]
    nlinarith

  -- The divisor on the ball of radius R' and on K agree for points in the ball.
  have h_restrict_eq₂ := MeromorphicOn.divisor_restrict hhK hball_sub_K

  -- Now we prove the support inclusion.
  refine ⟨R', hR'_gt_R, ?_⟩
  intro z hz
  rw [Function.mem_support] at hz
  by_cases hz_ball_R : z ∈ Metric.ball (0 : ℂ) R
  · exact hz_ball_R
  · exfalso
    have hz_ball_R'_from_divisor : z ∈ Metric.ball (0 : ℂ) R' := by
      rw [divisor_def] at hz
      split_ifs at hz with h
      · exact h.2
      · exact (hz rfl).elim
    have hz_K : z ∈ K := hball_sub_K hz_ball_R'_from_divisor
    -- Since the divisors agree, (divisor h K) z ≠ 0.
    have hz_divisor_K_ne_zero : (divisor h K) z ≠ 0 := by
      intro hzero
      apply hz
      calc
        (divisor h (Metric.ball (0 : ℂ) R')) z = ((divisor h K).restrict hball_sub_K) z := by rw [h_restrict_eq₂]
        _ = (divisor h K) z := by
          simp [Function.locallyFinsuppWithin.restrict_apply, hz_ball_R'_from_divisor]
        _ = 0 := hzero
    have hz_S : z ∈ S := ⟨hz_divisor_K_ne_zero, hz_ball_R⟩
    -- Then ‖z‖ is one of the moduli in A, so R1 ≤ ‖z‖.
    have h_norm_in_A : ‖z‖ ∈ A := by
      apply Finset.mem_image.mpr
      refine ⟨z, ?_, rfl⟩
      simpa using hz_S
    have hR1_le_norm : R1 ≤ ‖z‖ := hR1_le ‖z‖ h_norm_in_A
    -- But z is in the ball of radius R' = min R1 (R+1), so ‖z‖ < R' ≤ R1, contradiction.
    have hz_norm_lt_R' : ‖z‖ < R' := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hz_ball_R'_from_divisor
      exact hz_ball_R'_from_divisor
    have hR'_le_R1 : R' ≤ R1 := min_le_left _ _
    have : ‖z‖ < R1 := lt_of_lt_of_le hz_norm_lt_R' hR'_le_R1
    linarith

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

/-- Contour integral of `logDeriv φ` where `φ` is the factorized rational of
`divisor h D`, supported in the open disk. -/
theorem circleIntegral_logDeriv_factorizedRational {h : ℂ → ℂ} {R : ℝ}
    (hsupp : (divisor h (Metric.closedBall 0 R)).support ⊆ Metric.ball 0 R) :
    (∮ z in C(0, R),
        logDeriv (∏ᶠ u, (fun x => x - u) ^ (divisor h (Metric.closedBall 0 R)) u) z)
      = (∑ᶠ u, ((divisor h (Metric.closedBall 0 R)) u : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I) := by
  let d := divisor h (Metric.closedBall 0 R)
  have hfinite : Function.HasFiniteSupport d :=
    Function.locallyFinsuppWithin.finiteSupport d (isCompact_closedBall 0 R)
  by_cases hRnonneg : 0 ≤ R
  · have hsphere_eq : ∀ z ∈ Metric.sphere (0 : ℂ) R,
      logDeriv (∏ᶠ u, (fun x => x - u) ^ d u) z = ∑ᶠ u, (d u : ℂ) * (z - u)⁻¹ := by
      intro z hz
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hz
      have hz_not_support : z ∉ Function.support d := by
        intro hz_support
        have hz_ball : z ∈ Metric.ball (0 : ℂ) R := hsupp hz_support
        rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hz_ball
        linarith
      exact logDeriv_factorizedRational hfinite hz_not_support
    calc
      (∮ z in C(0, R), logDeriv (∏ᶠ u, (fun x => x - u) ^ d u) z)
          = (∮ z in C(0, R), ∑ᶠ u, (d u : ℂ) * (z - u)⁻¹) := by
        rw [circleIntegral.integral_congr hRnonneg hsphere_eq]
      _ = (∑ᶠ u, (d u : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I) :=
        circleIntegral_sum_inv hfinite hsupp
  · -- When R < 0, the ball is empty, so d is identically zero and both sides are zero
    have hd_zero : divisor h (Metric.closedBall 0 R) = 0 := by
      ext u
      by_contra! hne
      have hmem_support : u ∈ Function.support (divisor h (Metric.closedBall 0 R)) := by
        rw [Function.mem_support]
        exact hne
      have hu_ball : u ∈ Metric.ball (0 : ℂ) R := hsupp hmem_support
      have hball_empty : Metric.ball (0 : ℂ) R = ∅ :=
        (Metric.ball_eq_empty).mpr (by linarith)
      rw [hball_empty] at hu_ball
      exact hu_ball
    rw [hd_zero]
    simp [Pi.zero_apply, zpow_zero, logDeriv_apply, deriv_const]
    simp [circleIntegral, smul_zero, intervalIntegral.integral_zero]

end ComplexAnalysis
end LeanEval
