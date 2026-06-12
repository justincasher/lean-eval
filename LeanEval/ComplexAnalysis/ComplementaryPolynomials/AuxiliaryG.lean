import Mathlib
import EvalTools.Markers
import LeanEval.ComplexAnalysis.ComplementaryPolynomials.ConjugateReciprocal

/-!
The auxiliary polynomial `G = Xⁿ - P · P^{†n}` realising `1 - |P|²` on the circle. Helper file
for `LeanEval.ComplexAnalysis.ComplementaryPolynomials`.
-/

namespace LeanEval
namespace ComplexAnalysis

open Polynomial

/-- The auxiliary polynomial `G = Xⁿ - P · P^{†n}` with `n = deg P`. -/
noncomputable def auxG (P : ℂ[X]) : ℂ[X] :=
  X ^ P.natDegree - P * conjRecip P.natDegree P

/-- `deg G ≤ 2n`. -/
theorem auxG_natDegree_le (P : ℂ[X]) :
    (auxG P).natDegree ≤ 2 * P.natDegree := by
  sorry

/-- Value of `G` on the circle: `G(z) = zⁿ (1 - |P(z)|²)`. -/
theorem auxG_eval_circle (P : ℂ[X]) {z : ℂ} (hz : ‖z‖ = 1) :
    (auxG P).eval z = z ^ P.natDegree * ((1 - ‖P.eval z‖ ^ 2 : ℝ) : ℂ) := by
  sorry

/-- The predicate "`z ↦ z⁻ⁿ · H(z)` is a nonnegative real on the unit circle". -/
def NonnegRealOnCircle (n : ℕ) (H : ℂ[X]) : Prop :=
  ∀ z : ℂ, ‖z‖ = 1 → ∃ r : ℝ, 0 ≤ r ∧ (z ^ n)⁻¹ * H.eval z = (r : ℂ)

/-- If `P` is bounded by `1` on the circle, then `z⁻ⁿ G(z)` is a nonnegative real there. -/
theorem auxG_nonneg_circle (P : ℂ[X]) (hP : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1) :
    NonnegRealOnCircle P.natDegree (auxG P) := by
  sorry

/-- `G` is self-inversive: `G^{†2n} = G`. -/
theorem auxG_self_inversive (P : ℂ[X]) :
    conjRecip (2 * P.natDegree) (auxG P) = auxG P := by
  sorry

end ComplexAnalysis
end LeanEval
