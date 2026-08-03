import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import LeanEval.ComplexAnalysis.Rouche.Boundary
import LeanEval.ComplexAnalysis.Rouche.LogDerivBasics

/-!
# The argument principle (Rouché via zero counting)

The contour-integral form of the argument principle: splitting the integral of
`logDeriv h` along the factorization `h = φ · U`, the vanishing of the unit
contribution, and the assembled zero-counting statement.
-/

namespace LeanEval
namespace ComplexAnalysis

open MeromorphicOn

/-! ## Vanishing of the unit contribution -/

/-- `logDeriv U` is circle-integrable for `U` analytic and nowhere zero on the
closed disk. -/
theorem circleIntegrable_logDeriv_unit {R : ℝ} {U : ℂ → ℂ} (hR : 0 < R)
    (hUana : AnalyticOnNhd ℂ U (Metric.closedBall 0 R))
    (hU0 : ∀ z ∈ Metric.closedBall (0 : ℂ) R, U z ≠ 0) :
    CircleIntegrable (logDeriv U) 0 R := by
  have h_logAna : AnalyticOnNhd ℂ (logDeriv U) (Metric.closedBall 0 R) :=
    logDeriv_analytic_unit hUana hU0
  have h_cont : ContinuousOn (logDeriv U) (Metric.closedBall 0 R) :=
    h_logAna.continuousOn
  have h_sphere_sub_closedBall : Metric.sphere (0 : ℂ) R ⊆ Metric.closedBall (0 : ℂ) R := by
    intro z hz
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hz
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact le_of_eq hz
  have h_cont_sphere : ContinuousOn (logDeriv U) (Metric.sphere (0 : ℂ) R) :=
    h_cont.mono h_sphere_sub_closedBall
  exact h_cont_sphere.circleIntegrable (by linarith)

/-- Contour integral of the logarithmic derivative of a unit (analytic and nowhere
zero on the closed disk) vanishes. -/
theorem circleIntegral_logDeriv_unit {R : ℝ} {U : ℂ → ℂ} (hR : 0 < R)
    (hUana : AnalyticOnNhd ℂ U (Metric.closedBall 0 R))
    (hU0 : ∀ z ∈ Metric.closedBall (0 : ℂ) R, U z ≠ 0) :
    (∮ z in C(0, R), logDeriv U z) = 0 := by
  have h_logAna : AnalyticOnNhd ℂ (logDeriv U) (Metric.closedBall 0 R) :=
    logDeriv_analytic_unit hUana hU0
  have h_diff : DifferentiableOn ℂ (logDeriv U) (Metric.ball 0 R) :=
    h_logAna.differentiableOn.mono Metric.ball_subset_closedBall
  have h_cont_cl : ContinuousOn (logDeriv U) (Metric.closedBall 0 R) :=
    h_logAna.continuousOn
  have h_closure : closure (Metric.ball (0 : ℂ) R) = Metric.closedBall (0 : ℂ) R := by
    have hR_ne : R ≠ 0 := by linarith
    exact closure_ball (0 : ℂ) hR_ne
  have h_cont_closure : ContinuousOn (logDeriv U) (closure (Metric.ball (0 : ℂ) R)) := by
    rw [h_closure]
    exact h_cont_cl
  have h_diffOnCl : DiffContOnCl ℂ (logDeriv U) (Metric.ball (0 : ℂ) R) :=
    { differentiableOn := h_diff
      continuousOn := h_cont_closure }
  exact h_diffOnCl.circleIntegral_eq_zero (by linarith)

/-! ## Factorization of the logarithmic derivative on the circle -/

/-- The factorization `h = φ · U` holds on a punctured neighbourhood of each point
of the circle. -/
theorem factorization_eventuallyEq {h : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hh : MeromorphicOn h Set.univ)
    (_horder : ∀ z : ℂ, ‖z‖ = R → meromorphicOrderAt h z = 0)
    {U : ℂ → ℂ} (hUana : AnalyticOnNhd ℂ U (Metric.closedBall 0 R))
    (_hU0 : ∀ z ∈ Metric.closedBall (0 : ℂ) R, U z ≠ 0)
    (hfact : h =ᶠ[Filter.codiscreteWithin (Metric.closedBall 0 R)]
      (∏ᶠ u, (fun x => x - u) ^ (divisor h (Metric.closedBall 0 R)) u) • U)
    {z : ℂ} (hz : ‖z‖ = R) :
    h =ᶠ[nhdsWithin z {z}ᶜ]
      (∏ᶠ u, (fun x => x - u) ^ (divisor h (Metric.closedBall 0 R)) u) • U := by
  have hz_closed : z ∈ Metric.closedBall (0 : ℂ) R := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact le_of_eq hz
  rcases factorization_meromorphicAt hh hUana hz_closed with ⟨hmerm_h, hmerm_φU⟩
  have h_preperfect : Preperfect (Metric.closedBall (0 : ℂ) R) :=
    closedBall_preperfect hR
  have h_bridge := hmerm_h.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
    hmerm_φU hz_closed h_preperfect hfact
  simpa [nhdsWithin] using h_bridge

/-- Factorization of the logarithmic derivative on the circle.

The blueprint's standing assumption that `h` is analytic on the circle (its
parenthetical "so `h` is analytic and nonzero on the circle") is made explicit as
`hana`: for a general `MeromorphicOn` function, `meromorphicOrderAt h z = 0` only
forces `h` to agree with an analytic function on the *punctured* neighbourhood of
`z`, so without analyticity at `z` the pointwise `logDeriv` identity can fail. -/
theorem factorization_logDeriv {h : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hh : MeromorphicOn h Set.univ)
    (horder : ∀ z : ℂ, ‖z‖ = R → meromorphicOrderAt h z = 0)
    (hana : ∀ z : ℂ, ‖z‖ = R → AnalyticAt ℂ h z)
    {U : ℂ → ℂ} (hUana : AnalyticOnNhd ℂ U (Metric.closedBall 0 R))
    (hU0 : ∀ z ∈ Metric.closedBall (0 : ℂ) R, U z ≠ 0)
    (hfact : h =ᶠ[Filter.codiscreteWithin (Metric.closedBall 0 R)]
      (∏ᶠ u, (fun x => x - u) ^ (divisor h (Metric.closedBall 0 R)) u) • U)
    {z : ℂ} (hz : ‖z‖ = R) :
    logDeriv h z
      = logDeriv (∏ᶠ u, (fun x => x - u) ^ (divisor h (Metric.closedBall 0 R)) u) z
        + logDeriv U z := by
  set d := divisor h (Metric.closedBall 0 R) with hd
  set φ := ∏ᶠ u, (fun x => x - u) ^ d u with hφ
  -- `z` lies in the closed disk.
  have hz_closed : z ∈ Metric.closedBall (0 : ℂ) R := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact le_of_eq hz
  -- `z` is off the divisor support.
  have hdz : d z = 0 := by
    rw [hd]; exact divisor_eq_zero_of_orderZero hh hz_closed (horder z hz)
  have hz_not_supp : z ∉ Function.support d := by
    rw [Function.mem_support, not_not]; exact hdz
  -- Reduce `φ` to a finite product over the (finite) divisor support.
  have hfinite : Function.HasFiniteSupport d :=
    Function.locallyFinsuppWithin.finiteSupport d (isCompact_closedBall 0 R)
  have hmulsupp : Function.mulSupport (fun u : ℂ => (fun x : ℂ => x - u) ^ d u)
      ⊆ (hfinite.toFinset : Set ℂ) := by
    intro u hu
    have hdu : d u ≠ 0 := by intro h0; apply hu; simp [h0]
    exact hfinite.mem_toFinset.mpr (by rwa [Function.mem_support])
  have hφ_prod : φ = ∏ u ∈ hfinite.toFinset, (fun x : ℂ => x - u) ^ d u := by
    rw [hφ]; exact finprod_eq_prod_of_mulSupport_subset _ hmulsupp
  -- For each support point `u` we have `z ≠ u`.
  have hz_ne_u : ∀ u ∈ hfinite.toFinset, z ≠ u := by
    intro u hu heq
    apply hz_not_supp
    rw [Function.mem_support]
    have hdu : d u ≠ 0 := by
      have := hfinite.mem_toFinset.mp hu
      rwa [Function.mem_support] at this
    rwa [heq]
  -- Each factor is differentiable and nonzero at `z`.
  have hfac_diff : ∀ u ∈ hfinite.toFinset,
      DifferentiableAt ℂ ((fun x : ℂ => x - u) ^ d u) z := by
    intro u hu
    have hval_ne : (fun x : ℂ => x - u) z ≠ 0 := by
      simpa [sub_ne_zero] using hz_ne_u u hu
    exact ((differentiableAt_id (x := z)).sub_const u).zpow (m := d u) (Or.inl hval_ne)
  have hfac_ne : ∀ u ∈ hfinite.toFinset, ((fun x : ℂ => x - u) ^ d u) z ≠ 0 := by
    intro u hu
    have hzu : (z - u) ≠ 0 := sub_ne_zero.mpr (hz_ne_u u hu)
    simpa [Pi.pow_apply] using zpow_ne_zero (d u) hzu
  -- Hence `φ` is differentiable and nonzero at `z`.
  have hφ_diff : DifferentiableAt ℂ φ z := by
    rw [hφ_prod]; exact DifferentiableAt.finsetProd hfac_diff
  have hφz_ne : φ z ≠ 0 := by
    rw [hφ_prod, Finset.prod_apply]
    exact Finset.prod_ne_zero_iff.mpr hfac_ne
  -- `U` is differentiable and nonzero at `z`.
  have hU_diff : DifferentiableAt ℂ U z := (hUana z hz_closed).differentiableAt
  have hUz_ne : U z ≠ 0 := hU0 z hz_closed
  -- `φ • U` is the pointwise product.
  have hsmul_eq : (φ • U) = fun w => φ w * U w := by
    funext w
    show φ w • U w = φ w * U w
    rw [smul_eq_mul]
  -- Both `h` and `φ • U` are continuous at `z`.
  have hcont_h : ContinuousAt h z := (hana z hz).continuousAt
  have hcont_φU : ContinuousAt (φ • U) z := by
    rw [hsmul_eq]
    exact hφ_diff.continuousAt.mul hU_diff.continuousAt
  -- The factorization holds on a punctured neighbourhood, upgraded to a full one.
  have h_pNbhd : h =ᶠ[nhdsWithin z {z}ᶜ] φ • U := by
    have hee := factorization_eventuallyEq hR hh horder hUana hU0 hfact hz
    rw [← hd, ← hφ] at hee
    exact hee
  have h_nhds : h =ᶠ[nhds z] φ • U :=
    (hcont_h.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hcont_φU).mp h_pNbhd
  have hval : h z = (φ • U) z := h_nhds.eq_of_nhds
  -- Conclude: `logDeriv` is determined by the germ at `z`, then split the product.
  have hlog_eq : logDeriv h z = logDeriv (φ • U) z := by
    rw [logDeriv_apply, logDeriv_apply, h_nhds.deriv_eq, hval]
  rw [hlog_eq, hsmul_eq, logDeriv_mul z hφz_ne hUz_ne hφ_diff hU_diff]

/-! ## Splitting and assembling the argument-principle integral -/

/-- Splitting the contour integral of `logDeriv h` along the factorization
`h = φ · U`. -/
theorem argument_principle_integral_split {h : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hh : MeromorphicOn h Set.univ)
    (horder : ∀ z : ℂ, ‖z‖ = R → meromorphicOrderAt h z = 0)
    (hana : ∀ z : ℂ, ‖z‖ = R → AnalyticAt ℂ h z)
    {U : ℂ → ℂ} (hUana : AnalyticOnNhd ℂ U (Metric.closedBall 0 R))
    (hU0 : ∀ z ∈ Metric.closedBall (0 : ℂ) R, U z ≠ 0)
    (hfact : h =ᶠ[Filter.codiscreteWithin (Metric.closedBall 0 R)]
      (∏ᶠ u, (fun x => x - u) ^ (divisor h (Metric.closedBall 0 R)) u) • U) :
    (∮ z in C(0, R), logDeriv h z)
      = (∮ z in C(0, R),
          logDeriv (∏ᶠ u, (fun x => x - u) ^ (divisor h (Metric.closedBall 0 R)) u) z)
        + (∮ z in C(0, R), logDeriv U z) := by
  let φ := ∏ᶠ u, (fun x => x - u) ^ (divisor h (Metric.closedBall 0 R)) u
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
  have h_int_φ : CircleIntegrable (logDeriv φ) 0 R :=
    circleIntegrable_logDeriv_factorizedRational hsupp
  have h_int_U : CircleIntegrable (logDeriv U) 0 R :=
    circleIntegrable_logDeriv_unit hR hUana hU0
  have h_eqon : Set.EqOn (logDeriv h) (logDeriv φ + logDeriv U) (Metric.sphere 0 R) := by
    intro z hz
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hz
    have h_eq := factorization_logDeriv hR hh horder hana hUana hU0 hfact hz
    simpa [φ] using h_eq
  have h_int_congr := circleIntegral.integral_congr hR.le h_eqon
  have h_int_add := circleIntegral.integral_add h_int_φ h_int_U
  calc
    (∮ z in C(0, R), logDeriv h z)
        = (∮ z in C(0, R), (logDeriv φ + logDeriv U) z) := h_int_congr
    _ = (∮ z in C(0, R), logDeriv φ z) + (∮ z in C(0, R), logDeriv U z) := h_int_add
    _ = (∮ z in C(0, R),
          logDeriv (∏ᶠ u, (fun x => x - u) ^ (divisor h (Metric.closedBall 0 R)) u) z)
        + (∮ z in C(0, R), logDeriv U z) := rfl

/-- Integral evaluation of the logarithmic derivative. -/
theorem argument_principle_integral {h : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hh : MeromorphicOn h Set.univ)
    (hne : ∃ z, meromorphicOrderAt h z ≠ ⊤)
    (horder : ∀ z : ℂ, ‖z‖ = R → meromorphicOrderAt h z = 0)
    (hana : ∀ z : ℂ, ‖z‖ = R → AnalyticAt ℂ h z) :
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
  have hsplit := argument_principle_integral_split hR hh horder hana hUana hU0 hfact
  have hUint : (∮ z in C(0, R), logDeriv U z) = 0 :=
    circleIntegral_logDeriv_unit hR hUana hU0
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
theorem argument_principle {h : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hh : MeromorphicOn h Set.univ)
    (hne : ∃ z, meromorphicOrderAt h z ≠ ⊤)
    (horder : ∀ z : ℂ, ‖z‖ = R → meromorphicOrderAt h z = 0)
    (hana : ∀ z : ℂ, ‖z‖ = R → AnalyticAt ℂ h z) :
    ((∑ᶠ z, (divisor h (Metric.closedBall 0 R)) z : ℤ) : ℂ)
      = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * (∮ z in C(0, R), logDeriv h z) := by
  have hintegral := argument_principle_integral hR hh hne horder hana
  have hfinite : Function.HasFiniteSupport (divisor h (Metric.closedBall 0 R)) :=
    Function.locallyFinsuppWithin.finiteSupport (divisor h (Metric.closedBall 0 R))
      (isCompact_closedBall 0 R)
  have hC : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    have hπ0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
    have hI0 : Complex.I ≠ 0 := Complex.I_ne_zero
    have h20 : (2 : ℂ) ≠ 0 := by norm_num
    exact mul_ne_zero (mul_ne_zero h20 hπ0) hI0
  calc
    ((∑ᶠ z, (divisor h (Metric.closedBall 0 R)) z : ℤ) : ℂ)
        = ∑ᶠ u, ((divisor h (Metric.closedBall 0 R)) u : ℂ) := by
      let d : ℂ → ℤ := divisor h (Metric.closedBall 0 R)
      have hfinite_d : Function.HasFiniteSupport d := hfinite
      simpa using (Int.castAddHom ℂ).map_finsum (f := d) hfinite_d
    _ = (2 * (Real.pi : ℂ) * Complex.I)⁻¹
        * ((∑ᶠ u, ((divisor h (Metric.closedBall 0 R)) u : ℂ))
          * (2 * (Real.pi : ℂ) * Complex.I)) := by
      field_simp [hC]
    _ = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * (∮ z in C(0, R), logDeriv h z) := by rw [hintegral]

end ComplexAnalysis
end LeanEval
