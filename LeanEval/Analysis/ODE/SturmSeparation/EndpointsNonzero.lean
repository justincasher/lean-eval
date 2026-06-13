import Mathlib
import LeanEval.Analysis.ODE.SturmSeparation.FactorsNonzeroAtZero

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

include hab hJ_open hJ_conn hJ_sub hp hy₁ hy₁' hy₂ hy₂' hW hza hzb in
/-- **Endpoint values are nonzero.** `y₂ a ≠ 0`, `y₂ b ≠ 0`, `y₁'(a) ≠ 0`, `y₁'(b) ≠ 0`. -/
theorem endpoints_nonzero :
    y₂ a ≠ 0 ∧ y₂ b ≠ 0 ∧ deriv y₁ a ≠ 0 ∧ deriv y₁ b ≠ 0 := by
  have haJ : a ∈ J := hJ_sub (Set.mem_Icc.mpr ⟨le_rfl, le_of_lt hab⟩)
  have hbJ : b ∈ J := hJ_sub (Set.mem_Icc.mpr ⟨le_of_lt hab, le_rfl⟩)
  rcases factors_nonzero_at_zero hJ_open hJ_conn hp hy₁ hy₁' hy₂ hy₂' hW haJ hza with ⟨ha2, ha1'⟩
  rcases factors_nonzero_at_zero hJ_open hJ_conn hp hy₁ hy₁' hy₂ hy₂' hW hbJ hzb with ⟨hb2, hb1'⟩
  exact ⟨ha2, hb2, ha1', hb1'⟩

end ODE
end Analysis
end LeanEval
