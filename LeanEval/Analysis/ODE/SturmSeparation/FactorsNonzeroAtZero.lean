import Mathlib
import LeanEval.Analysis.ODE.SturmSeparation.WronskianAtZero
import LeanEval.Analysis.ODE.SturmSeparation.WronskianMulPos

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

include hJ_open hJ_conn hp hy₁ hy₁' hy₂ hy₂' hW in
/-- **Both factors are nonzero at a zero of `y₁`.** If `t ∈ J` and `y₁ t = 0`, then
`y₂ t ≠ 0` and `y₁'(t) ≠ 0`. -/
theorem factors_nonzero_at_zero {t : ℝ} (ht : t ∈ J) (hy : y₁ t = 0) :
    y₂ t ≠ 0 ∧ deriv y₁ t ≠ 0 := by
  -- By wronskian_at_zero, W(t) = -(y₂ t * deriv y₁ t) when y₁ t = 0
  have hW_eq : wronskian y₁ y₂ t = -(y₂ t * deriv y₁ t) := wronskian_at_zero hy
  -- By wronskian_mul_pos, W(t)² > 0, hence W(t) ≠ 0
  have hW_pos : 0 < wronskian y₁ y₂ t * wronskian y₁ y₂ t :=
    wronskian_mul_pos hJ_open hJ_conn hp hy₁ hy₁' hy₂ hy₂' hW ht ht
  have hW_ne : wronskian y₁ y₂ t ≠ 0 := by
    intro hzero
    rw [hzero] at hW_pos
    linarith
  -- Therefore -(y₂ t * deriv y₁ t) ≠ 0, so y₂ t * deriv y₁ t ≠ 0
  have hprod_ne : y₂ t * deriv y₁ t ≠ 0 := by
    intro hzero
    apply hW_ne
    rw [hW_eq]
    simp [hzero]
  -- mul_ne_zero_iff gives both factors nonzero
  exact mul_ne_zero_iff.mp hprod_ne

end ODE
end Analysis
end LeanEval
