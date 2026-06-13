import Mathlib
import LeanEval.Analysis.ODE.SturmSeparation.Defs
import LeanEval.Analysis.ODE.SturmSeparation.WronskianHasDerivAt
import LeanEval.Analysis.ODE.SturmSeparation.ExistsPrimitive

namespace LeanEval
namespace Analysis
namespace ODE

variable {p q y₁ y₂ : ℝ → ℝ} {a b : ℝ} {J : Set ℝ}
  (hab : a < b)
  (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
  (hJ_sub : Set.Icc a b ⊆ J)
  (hp : ContinuousOn p J) (hq : ContinuousOn q J)
  (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
  (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
  (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
  (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
  (hW : ∃ x₀ ∈ J, y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ ≠ 0)
  (hza : y₁ a = 0) (hzb : y₁ b = 0)
  (hne : ∀ x ∈ Set.Ioo a b, y₁ x ≠ 0)

include hy₁ hy₁' hy₂ hy₂' in
/-- **The product `W·eᴾ` has zero derivative.** For any primitive `P` of `p` on `J`, the
function `x ↦ W(x) eᴾ⁽ˣ⁾` has derivative `0` at every point of `J`. -/
theorem wronskian_mul_exp_hasDerivAt_zero {P : ℝ → ℝ}
    (hP : ∀ x ∈ J, HasDerivAt P (p x) x) {x : ℝ} (hx : x ∈ J) :
    HasDerivAt (fun t => wronskian y₁ y₂ t * Real.exp (P t)) 0 x := by
  sorry

end ODE
end Analysis
end LeanEval
