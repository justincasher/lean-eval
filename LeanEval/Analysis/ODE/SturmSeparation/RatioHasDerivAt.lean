import Mathlib
import LeanEval.Analysis.ODE.SturmSeparation.Defs

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

include hJ_sub hy₁ hy₂ hne in
/-- **Derivative of the ratio.** On `(a,b)`, `g = y₂/y₁` has derivative `W(x) / y₁(x)²`. -/
theorem ratio_hasDerivAt {x : ℝ} (hx : x ∈ Set.Ioo a b) :
    HasDerivAt (ratio y₁ y₂) (wronskian y₁ y₂ x / (y₁ x) ^ 2) x := by
  have hxJ : x ∈ J := hJ_sub (Set.Ioo_subset_Icc_self hx)
  have hy₁x : HasDerivAt y₁ (deriv y₁ x) x := hy₁ x hxJ
  have hy₂x : HasDerivAt y₂ (deriv y₂ x) x := hy₂ x hxJ
  have hy₁_ne : y₁ x ≠ 0 := hne x hx
  have h_div : HasDerivAt (y₂ / y₁) ((deriv y₂ x * y₁ x - y₂ x * deriv y₁ x) / (y₁ x) ^ 2) x :=
    HasDerivAt.div hy₂x hy₁x hy₁_ne
  unfold ratio wronskian
  change HasDerivAt (y₂ / y₁)
    ((y₁ x * deriv y₂ x - y₂ x * deriv y₁ x) / y₁ x ^ 2) x
  convert h_div using 1
  ring

end ODE
end Analysis
end LeanEval
