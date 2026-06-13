import Mathlib
import LeanEval.Analysis.ODE.SturmSeparation.EndpointsNonzero
import LeanEval.Analysis.ODE.SturmSeparation.DerivEndpointsSigned
import LeanEval.Analysis.ODE.SturmSeparation.Y1SignConstant

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
/-- **Endpoint derivatives of `y₁` have opposite signs.** `y₁'(a) · y₁'(b) < 0`. -/
theorem y1_deriv_opposite :
    deriv y₁ a * deriv y₁ b < 0 := by
  have haJ : a ∈ J := hJ_sub (Set.mem_Icc.mpr ⟨le_rfl, le_of_lt hab⟩)
  have hbJ : b ∈ J := hJ_sub (Set.mem_Icc.mpr ⟨le_of_lt hab, le_rfl⟩)
  have h_deriv_a : HasDerivAt y₁ (deriv y₁ a) a := hy₁ a haJ
  have h_deriv_b : HasDerivAt y₁ (deriv y₁ b) b := hy₁ b hbJ
  have h_endpoints := endpoints_nonzero hab hJ_open hJ_conn hJ_sub hp hy₁ hy₁' hy₂ hy₂' hW hza hzb
  rcases h_endpoints with ⟨_, _, hLa, hLb⟩
  have hsign := y1_sign_constant hab hJ_sub hy₁ hne
  exact deriv_endpoints_of_signed_interior hab h_deriv_a h_deriv_b hza hzb hLa hLb hsign

end ODE
end Analysis
end LeanEval
