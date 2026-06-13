import Mathlib
import LeanEval.Analysis.ODE.SturmSeparation.WronskianMulPos
import LeanEval.Analysis.ODE.SturmSeparation.Y1DerivOpposite
import LeanEval.Analysis.ODE.SturmSeparation.WronskianAtZero

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

include hab hJ_open hJ_conn hJ_sub hp hy₁ hy₁' hy₂ hy₂' hW hza hzb hne in
/-- **`y₂` takes opposite signs at the endpoints.** `y₂ a · y₂ b < 0`. -/
theorem y2_endpoints_opposite :
    y₂ a * y₂ b < 0 := by
  have haJ : a ∈ J := hJ_sub (Set.mem_Icc.mpr ⟨le_rfl, le_of_lt hab⟩)
  have hbJ : b ∈ J := hJ_sub (Set.mem_Icc.mpr ⟨le_of_lt hab, le_rfl⟩)
  have hWpos : 0 < wronskian y₁ y₂ a * wronskian y₁ y₂ b :=
    wronskian_mul_pos hJ_open hJ_conn hp hy₁ hy₁' hy₂ hy₂' hW haJ hbJ
  have hWa : wronskian y₁ y₂ a = -(y₂ a * deriv y₁ a) := wronskian_at_zero hza
  have hWb : wronskian y₁ y₂ b = -(y₂ b * deriv y₁ b) := wronskian_at_zero hzb
  rw [hWa, hWb] at hWpos
  have hderiv_neg : deriv y₁ a * deriv y₁ b < 0 :=
    y1_deriv_opposite hab hJ_open hJ_conn hJ_sub hp hy₁ hy₁' hy₂ hy₂' hW hza hzb hne
  nlinarith

end ODE
end Analysis
end LeanEval
