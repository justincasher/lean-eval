import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import LeanEval.ComplexAnalysis.Rouche.Boundary

/-!
# Matching pole divisors and conclusion (Rouché via zero counting)

`f` and `f + g` share the same pole divisor (negative part), the argument principle
applies to both, and the positive-part mass decomposes as signed mass plus
negative-part mass. These assemble into the final zero-count identity in
`LeanEval/ComplexAnalysis/Rouche.lean`.
-/

namespace LeanEval
namespace ComplexAnalysis

open MeromorphicOn

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
theorem orderZero_bundle {f g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
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
