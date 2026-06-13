import Mathlib
import LeanEval.Analysis.ODE.SturmSeparation.UIccSubset

namespace LeanEval
namespace Analysis
namespace ODE

open scoped MeasureTheory

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

include hJ_open hJ_conn hp in
/-- **Integrability and measurability of `p` along `J`.** For `x₀, x ∈ J`, `p` is interval
integrable from `x₀` to `x` and strongly measurable at the neighborhood filter of `x`. -/
theorem p_intervalIntegrable_stronglyMeasurable {x₀ : ℝ} (hx₀ : x₀ ∈ J)
    {x : ℝ} (hx : x ∈ J) :
    IntervalIntegrable p MeasureTheory.volume x₀ x ∧
      StronglyMeasurableAtFilter p (nhds x) := by
  sorry

end ODE
end Analysis
end LeanEval
