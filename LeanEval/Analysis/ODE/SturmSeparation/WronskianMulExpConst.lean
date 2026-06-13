import Mathlib
import LeanEval.Analysis.ODE.SturmSeparation.WronskianMulExpZero
import LeanEval.Analysis.ODE.SturmSeparation.UIccSubset

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

include hJ_open hJ_conn hy₁ hy₁' hy₂ hy₂' in
/-- **`W·eᴾ` is constant on `J`.** For any primitive `P` of `p` and any `x₀, x ∈ J`,
`W(x) eᴾ⁽ˣ⁾ = W(x₀) eᴾ⁽ˣ⁰⁾`. -/
theorem wronskian_mul_exp_const {P : ℝ → ℝ}
    (hP : ∀ x ∈ J, HasDerivAt P (p x) x) {x₀ : ℝ} (hx₀ : x₀ ∈ J) {x : ℝ} (hx : x ∈ J) :
    wronskian y₁ y₂ x * Real.exp (P x) = wronskian y₁ y₂ x₀ * Real.exp (P x₀) := by
  sorry

end ODE
end Analysis
end LeanEval
