import Mathlib
import LeanEval.Analysis.ODE.SturmSeparation.WronskianMulExpConst
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

include hJ_open hJ_conn hy₁ hy₁' hy₂ hy₂' hW in
/-- **Closed form of the Wronskian.** There is a constant `C ≠ 0` with
`W(x) = C e^{−P(x)}` for every `x ∈ J`. -/
theorem wronskian_eq_const_mul_exp {P : ℝ → ℝ}
    (hP : ∀ x ∈ J, HasDerivAt P (p x) x) :
    ∃ C : ℝ, C ≠ 0 ∧ ∀ x ∈ J, wronskian y₁ y₂ x = C * Real.exp (-(P x)) := by
  rcases hW with ⟨x₀, hx₀, hWx₀⟩
  have hWx₀' : wronskian y₁ y₂ x₀ ≠ 0 := hWx₀
  have hpos : Real.exp (P x₀) > 0 := Real.exp_pos (P x₀)
  have hC_ne_zero : wronskian y₁ y₂ x₀ * Real.exp (P x₀) ≠ 0 :=
    mul_ne_zero hWx₀' hpos.ne'
  refine ⟨wronskian y₁ y₂ x₀ * Real.exp (P x₀), hC_ne_zero, λ x hx => ?_⟩
  have h_eq : wronskian y₁ y₂ x * Real.exp (P x) = wronskian y₁ y₂ x₀ * Real.exp (P x₀) :=
    wronskian_mul_exp_const hJ_open hJ_conn hy₁ hy₁' hy₂ hy₂' hP hx₀ hx
  have h_nonzero : Real.exp (P x) ≠ 0 := (Real.exp_pos (P x)).ne'
  calc
    wronskian y₁ y₂ x
        = (wronskian y₁ y₂ x * Real.exp (P x)) * (Real.exp (P x))⁻¹ := by
      field_simp [h_nonzero]
    _ = (wronskian y₁ y₂ x₀ * Real.exp (P x₀)) * (Real.exp (P x))⁻¹ := by rw [h_eq]
    _ = (wronskian y₁ y₂ x₀ * Real.exp (P x₀)) * Real.exp (-(P x)) := by rw [Real.exp_neg]

end ODE
end Analysis
end LeanEval
