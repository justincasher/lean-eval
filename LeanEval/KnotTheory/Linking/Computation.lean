import LeanEval.KnotTheory.Linking.Invariance
import LeanEval.KnotTheory.Linking.Examples

namespace LeanEval
namespace KnotTheory

/-!
# Computing the two linking numbers

The closed-form linking integrands of the unlink and the Hopf link, the
vanishing of `lk(unlink)`, the (elliptic-integral) Hopf evaluation, and the
conclusion that the two links are not ambient-isotopic.
-/

open scoped RealInnerProductSpace

/-- **The unlink linking integrand** in closed form:
`I_{L₁}(s,t) = -2 sin(s - t) / (6 - 2 cos(s - t))^{3/2}`. -/
theorem unlink_integrand (s t : ℝ) :
    linkingIntegrand unlink.K.curve unlink.L.curve s t
      = -2 * Real.sin (s - t) / Real.sqrt (6 - 2 * Real.cos (s - t)) ^ 3 := by
  sorry

/-- **Antiderivative of the unlink integrand.** For fixed `t`,
`s ↦ (6 - 2cos(s - t))^{-1/2}` has derivative equal to the unlink integrand. -/
theorem unlink_inner_antideriv (t s : ℝ) :
    HasDerivAt (fun s => (6 - 2 * Real.cos (s - t)) ^ (-(1 / 2) : ℝ))
      (-2 * Real.sin (s - t) / Real.sqrt (6 - 2 * Real.cos (s - t)) ^ 3) s := by
  sorry

/-- **Inner integral of the unlink integrand vanishes** for every `t`. -/
theorem unlink_inner_integral_zero (t : ℝ) :
    ∫ s in (0 : ℝ)..(2 * Real.pi), linkingIntegrand unlink.K.curve unlink.L.curve s t = 0 := by
  sorry

/-- **The unlink has linking number zero.** -/
theorem linking_unlink_zero : unlink.linkingNumber = 0 := by
  sorry

/-- **The Hopf linking integrand** in closed form:
`I_{L₂}(s,t) = (cos t - (1 + cos t) cos s) / D(s,t)^{3/2}`, where
`D(s,t) = 3 + 2 cos t - 2 (1 + cos t) cos s = ‖u‖²`. -/
theorem hopf_integrand (s t : ℝ) :
    linkingIntegrand hopfLink.K.curve hopfLink.L.curve s t
      = (Real.cos t - (1 + Real.cos t) * Real.cos s)
        / Real.sqrt (3 + 2 * Real.cos t - 2 * (1 + Real.cos t) * Real.cos s) ^ 3 := by
  sorry

/-- **The Hopf denominator is bounded below.**
`D(s,t) = 3 + 2 cos t - 2 (1 + cos t) cos s ≥ 1`; in particular `D(s,t) > 0`. -/
theorem hopf_denom_pos (s t : ℝ) :
    (1 : ℝ) ≤ 3 + 2 * Real.cos t - 2 * (1 + Real.cos t) * Real.cos s := by
  have hcos_s : Real.cos s ≤ 1 := Real.cos_le_one _
  have hcos_t : -1 ≤ Real.cos t := Real.neg_one_le_cos _
  nlinarith

/-- **Reduced form of the Hopf integrand.** Since the numerator is `½(D - 3)`,
`I_{L₂}(s,t) = ½ D(s,t)^{-1/2} - 3/2 D(s,t)^{-3/2}`. -/
theorem hopf_integrand_reduced (s t : ℝ) :
    linkingIntegrand hopfLink.K.curve hopfLink.L.curve s t
      = (1 / 2) *
          (3 + 2 * Real.cos t - 2 * (1 + Real.cos t) * Real.cos s) ^ (-(1 / 2) : ℝ)
        - (3 / 2) *
          (3 + 2 * Real.cos t - 2 * (1 + Real.cos t) * Real.cos s) ^ (-(3 / 2) : ℝ) := by
  sorry

/-- **Explicit half-angle reduction of the Hopf inner integrand.** Under
`x = tan(s/2)`, with `c = 5 + 4cos t`, the reduced integrand times `2/(1+x²)`
equals `Ψ_t(x) = ((c-3)x² - 2)(1+x²)^{-1/2}(1+cx²)^{-3/2}`. -/
theorem hopf_halfAngle_reduction (t x : ℝ) :
    ((1 / 2) * ((1 + (5 + 4 * Real.cos t) * x ^ 2) / (1 + x ^ 2)) ^ (-(1 / 2) : ℝ)
        - (3 / 2) * ((1 + (5 + 4 * Real.cos t) * x ^ 2) / (1 + x ^ 2)) ^ (-(3 / 2) : ℝ))
        * (2 / (1 + x ^ 2))
      = ((5 + 4 * Real.cos t - 3) * x ^ 2 - 2) * (1 + x ^ 2) ^ (-(1 / 2) : ℝ)
          * (1 + (5 + 4 * Real.cos t) * x ^ 2) ^ (-(3 / 2) : ℝ) := by
  sorry

/-- **Continuity and periodicity of the Hopf inner integral.** -/
theorem hopf_inner_integral_regularity :
    Continuous (fun t => ∫ s in (0 : ℝ)..(2 * Real.pi),
        (1 / 2) * (3 + 2 * Real.cos t - 2 * (1 + Real.cos t) * Real.cos s) ^ (-(1 / 2) : ℝ)
        - (3 / 2) * (3 + 2 * Real.cos t - 2 * (1 + Real.cos t) * Real.cos s) ^ (-(3 / 2) : ℝ))
      ∧ Function.Periodic (fun t => ∫ s in (0 : ℝ)..(2 * Real.pi),
        (1 / 2) * (3 + 2 * Real.cos t - 2 * (1 + Real.cos t) * Real.cos s) ^ (-(1 / 2) : ℝ)
        - (3 / 2) * (3 + 2 * Real.cos t - 2 * (1 + Real.cos t) * Real.cos s) ^ (-(3 / 2) : ℝ))
        (2 * Real.pi) := by
  sorry

/-- **The Hopf inner integral splits by linearity** into the two real-power
integrals (each a complete elliptic integral; only the linearity split is
formalized here). -/
theorem hopf_inner_integral (t : ℝ) :
    (∫ s in (0 : ℝ)..(2 * Real.pi),
        (1 / 2) * (3 + 2 * Real.cos t - 2 * (1 + Real.cos t) * Real.cos s) ^ (-(1 / 2) : ℝ)
        - (3 / 2) * (3 + 2 * Real.cos t - 2 * (1 + Real.cos t) * Real.cos s) ^ (-(3 / 2) : ℝ))
      = (1 / 2) * (∫ s in (0 : ℝ)..(2 * Real.pi),
            (3 + 2 * Real.cos t - 2 * (1 + Real.cos t) * Real.cos s) ^ (-(1 / 2) : ℝ))
        - (3 / 2) * (∫ s in (0 : ℝ)..(2 * Real.pi),
            (3 + 2 * Real.cos t - 2 * (1 + Real.cos t) * Real.cos s) ^ (-(3 / 2) : ℝ)) := by
  sorry

/-- **The Hopf outer integral equals `4π`.**

*Obstruction.* The inner integral is a nonzero combination of complete elliptic
integrals of `t`, hence has no elementary antiderivative; the true value `4π` is
a mapping-degree / solid-angle fact. Mathlib currently has neither a theory of
complete elliptic integrals nor smooth degree theory, so this statement, although
true, cannot be proved within Mathlib. -/
theorem hopf_outer_integral :
    (∫ t in (0 : ℝ)..(2 * Real.pi), ∫ s in (0 : ℝ)..(2 * Real.pi),
        (1 / 2) * (3 + 2 * Real.cos t - 2 * (1 + Real.cos t) * Real.cos s) ^ (-(1 / 2) : ℝ)
        - (3 / 2) * (3 + 2 * Real.cos t - 2 * (1 + Real.cos t) * Real.cos s) ^ (-(3 / 2) : ℝ))
      = 4 * Real.pi := by
  sorry

/-- **The Hopf Gauss integral equals 4π.** The double integral evaluates to
`4π`, so `lk(L₂) = 1`, via `hopf_integrand_reduced` and the FTC. -/
theorem hopf_linking_value : hopfLink.linkingNumber = 1 := by
  sorry

/-- **The Hopf link has nonzero linking number.** -/
theorem linking_hopf_nonzero : hopfLink.linkingNumber ≠ 0 := by
  rw [hopf_linking_value]
  norm_num

end KnotTheory
end LeanEval
