import Mathlib
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
/-- **The Wronskian keeps the sign of a reference point.** For `m ∈ J`, if `W(m) > 0` then
`W(x) > 0` for all `x ∈ J`, and if `W(m) < 0` then `W(x) < 0` for all `x ∈ J`. -/
theorem wronskian_sign_of_ref {m : ℝ} (hm : m ∈ J) {x : ℝ} (hx : x ∈ J) :
    (0 < wronskian y₁ y₂ m → 0 < wronskian y₁ y₂ x) ∧
      (wronskian y₁ y₂ m < 0 → wronskian y₁ y₂ x < 0) := by
  have hprod_pos : 0 < wronskian y₁ y₂ m * wronskian y₁ y₂ x :=
    wronskian_mul_pos (hJ_open := hJ_open) (hJ_conn := hJ_conn) (hp := hp) (hy₁ := hy₁) (hy₁' := hy₁') (hy₂ := hy₂) (hy₂' := hy₂') (hW := hW) hm hx
  constructor
  · intro hWm_pos
    have hWx_pos : 0 < wronskian y₁ y₂ x := by
      nlinarith
    exact hWx_pos
  · intro hWm_neg
    have hWx_neg : wronskian y₁ y₂ x < 0 := by
      nlinarith
    exact hWx_neg

end ODE
end Analysis
end LeanEval
