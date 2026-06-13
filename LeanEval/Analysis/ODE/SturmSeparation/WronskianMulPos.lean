import Mathlib
import LeanEval.Analysis.ODE.SturmSeparation.WronskianEqConstMulExp
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

include hJ_open hJ_conn hp hy₁ hy₁' hy₂ hy₂' hW in
/-- **The Wronskian has constant sign.** For all `s, t ∈ J`, `0 < W(s) W(t)`; in
particular `W` is nonzero on `J`. -/
theorem wronskian_mul_pos {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J) :
    0 < wronskian y₁ y₂ s * wronskian y₁ y₂ t := by
  have hP : ∃ P : ℝ → ℝ, ∀ x ∈ J, HasDerivAt P (p x) x :=
    exists_primitive hJ_open hJ_conn hp hW
  rcases hP with ⟨P, hP⟩
  have hW_eq : ∃ C : ℝ, C ≠ 0 ∧ ∀ x ∈ J, wronskian y₁ y₂ x = C * Real.exp (-(P x)) :=
    wronskian_eq_const_mul_exp hJ_open hJ_conn hy₁ hy₁' hy₂ hy₂' hW hP
  rcases hW_eq with ⟨C, hC_ne, hW_eq⟩
  have hprod : wronskian y₁ y₂ s * wronskian y₁ y₂ t = C ^ 2 * (Real.exp (-(P s)) * Real.exp (-(P t))) := by
    rw [hW_eq s hs, hW_eq t ht]
    ring
  rw [hprod]
  have hC_sq_pos : 0 < C ^ 2 := sq_pos_of_ne_zero hC_ne
  have h_exp_pos_s : 0 < Real.exp (-(P s)) := Real.exp_pos _
  have h_exp_pos_t : 0 < Real.exp (-(P t)) := Real.exp_pos _
  exact mul_pos hC_sq_pos (mul_pos h_exp_pos_s h_exp_pos_t)

end ODE
end Analysis
end LeanEval
