import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import LeanEval.ComplexAnalysis.Rouche.Support
import EvalTools.Markers

namespace LeanEval
namespace ComplexAnalysis

open MeromorphicOn

/-!
Rouché's theorem (zero-count formulation, extended to the meromorphic case via divisors),
stated as equality of multiplicity-counted zero counts on the closed disk of radius `R`
centered at `0`.

The previous formulation used `ValueDistribution.logCounting f 0 R`, the **log-weighted**
Nevanlinna counting function — which is *not* the conclusion of Rouché. Under `‖g‖ < ‖f‖`
on the boundary, `f` and `f + g` have the same number of zeros (counted with multiplicity)
inside the disk, but the log-weighted count depends on where each zero sits. Concretely,
`f(z) = z` and `g(z) = -1/2` satisfy `|g| = 1/2 < 2 = |z| = |f|` on `|z| = 2`, yet
`logCounting f 0 2 = log 2` while `logCounting (f + g) 0 2 = log(2 / (1/2)) = log 4`.

We instead state the conclusion as the equality of the multiplicity sums of the zero
divisors of `f` and `f + g` taken on the closed disk of radius `R`.

We also require `f` to be in *normal form* (`MeromorphicNFOn`) rather than merely
`MeromorphicOn`. A bare `MeromorphicOn` hypothesis admits functions whose pointwise values
disagree with their meromorphic order at exceptional points (any `=ᶠ[codiscreteWithin]`
modification is still meromorphic), and that pointwise disagreement is enough to make the
divisor identity fail. See the Zulip discussion at
https://leanprover.zulipchat.com/#narrow/channel/583341-Model-comparisons-for-Lean/topic/LeanEval/near/593331158
for a concrete counterexample to the previous `MeromorphicOn`-only formulation.
-/

@[eval_problem]
theorem rouche_zero_count_eq
    {f g : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R)
    (hf : MeromorphicNFOn f Set.univ)
    (hg : AnalyticOn ℂ g Set.univ)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖) :
    (∑ᶠ z, ((divisor (f + g) (Metric.closedBall 0 R))⁺) z) =
      (∑ᶠ z, ((divisor f (Metric.closedBall 0 R))⁺) z) := by
  set D := Metric.closedBall (0 : ℂ) R with hD
  have hpos_decomp_f : (∑ᶠ z, ((divisor f D)⁺) z) =
      (∑ᶠ z, (divisor f D) z) + (∑ᶠ z, ((divisor f D)⁻) z) :=
    posPart_mass_decomp (h := f) (R := R)
  have hpos_decomp_fg : (∑ᶠ z, ((divisor (f + g) D)⁺) z) =
      (∑ᶠ z, (divisor (f + g) D) z) + (∑ᶠ z, ((divisor (f + g) D)⁻) z) :=
    posPart_mass_decomp (h := f + g) (R := R)
  -- The negative parts are equal
  have h_neg_eq_pointwise : ∀ z, ((divisor (f + g) D)⁻) z = ((divisor f D)⁻) z := by
    intro z
    by_cases hz : z ∈ D
    · exact negPart_eq hf hg hz
    · have hdiv_f : divisor f D z = 0 := by
        rw [MeromorphicOn.divisor_def]
        simp [hz]
      have hdiv_fg : divisor (f + g) D z = 0 := by
        rw [MeromorphicOn.divisor_def]
        simp [hz]
      simp [hdiv_f, hdiv_fg]
  have h_neg_sum_eq : (∑ᶠ z, ((divisor (f + g) D)⁻) z) = (∑ᶠ z, ((divisor f D)⁻) z) := by
    refine finsum_congr ?_
    intro z
    exact h_neg_eq_pointwise z
  -- The signed masses are equal via the argument principle
  have hfg_merm : MeromorphicOn (f + g) Set.univ :=
    hf.meromorphicOn.add (fun z hz => (hg.analyticAt (isOpen_univ.mem_nhds hz)).meromorphicAt)
  have hf_ne_top : ∃ z, meromorphicOrderAt f z ≠ ⊤ := by
    have hz_sphere : ∃ z : ℂ, ‖z‖ = R := by
      refine ⟨(R : ℂ), ?_⟩
      calc
        ‖(R : ℂ)‖ = |R| := by simp
        _ = R := abs_of_pos hR
    rcases hz_sphere with ⟨z, hz⟩
    have horder : meromorphicOrderAt f z = 0 := (f_analytic_sphere hf hbound hz).1
    exact ⟨z, by simp [horder]⟩
  have hfg_ne_top : ∃ z, meromorphicOrderAt (f + g) z ≠ ⊤ := by
    have hz_sphere : ∃ z : ℂ, ‖z‖ = R := by
      refine ⟨(R : ℂ), ?_⟩
      calc
        ‖(R : ℂ)‖ = |R| := by simp
        _ = R := abs_of_pos hR
    rcases hz_sphere with ⟨z, hz⟩
    have horder : meromorphicOrderAt (f + g) z = 0 :=
      (fg_analytic_sphere hf hg hbound hz).2.2
    exact ⟨z, by simp [horder]⟩
  have hf_order_sphere : ∀ z : ℂ, ‖z‖ = R → meromorphicOrderAt f z = 0 := by
    intro z hz
    exact (f_analytic_sphere hf hbound hz).1
  have hfg_order_sphere : ∀ z : ℂ, ‖z‖ = R → meromorphicOrderAt (f + g) z = 0 := by
    intro z hz
    exact (fg_analytic_sphere hf hg hbound hz).2.2
  have hf_ana_sphere : ∀ z : ℂ, ‖z‖ = R → AnalyticAt ℂ f z := by
    intro z hz
    exact (f_analytic_sphere hf hbound hz).2.1
  have hfg_ana_sphere : ∀ z : ℂ, ‖z‖ = R → AnalyticAt ℂ (f + g) z := by
    intro z hz
    exact (fg_analytic_sphere hf hg hbound hz).1
  have h_ap_f := argument_principle hR hf.meromorphicOn hf_ne_top hf_order_sphere hf_ana_sphere
  have h_ap_fg := argument_principle hR hfg_merm hfg_ne_top hfg_order_sphere hfg_ana_sphere
  have h_int_eq : (∮ z in C(0, R), logDeriv (f + g) z) = (∮ z in C(0, R), logDeriv f z) :=
    logDeriv_diff hR hf hg hbound
  have h_signed_eq_ℂ : ((∑ᶠ z, (divisor (f + g) D) z : ℤ) : ℂ) =
      ((∑ᶠ z, (divisor f D) z : ℤ) : ℂ) := by
    calc
      ((∑ᶠ z, (divisor (f + g) D) z : ℤ) : ℂ) =
          (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * (∮ z in C(0, R), logDeriv (f + g) z) := h_ap_fg
      _ = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * (∮ z in C(0, R), logDeriv f z) := by rw [h_int_eq]
      _ = ((∑ᶠ z, (divisor f D) z : ℤ) : ℂ) := by rw [h_ap_f]
  have h_signed_eq : (∑ᶠ z, (divisor (f + g) D) z) = (∑ᶠ z, (divisor f D) z) := by
    exact_mod_cast h_signed_eq_ℂ
  -- Combine using the decompositions
  calc
    (∑ᶠ z, ((divisor (f + g) D)⁺) z)
        = (∑ᶠ z, (divisor (f + g) D) z) + (∑ᶠ z, ((divisor (f + g) D)⁻) z) := hpos_decomp_fg
    _ = (∑ᶠ z, (divisor f D) z) + (∑ᶠ z, ((divisor (f + g) D)⁻) z) := by rw [h_signed_eq]
    _ = (∑ᶠ z, (divisor f D) z) + (∑ᶠ z, ((divisor f D)⁻) z) := by rw [h_neg_sum_eq]
    _ = (∑ᶠ z, ((divisor f D)⁺) z) := by rw [hpos_decomp_f]

end ComplexAnalysis
end LeanEval
