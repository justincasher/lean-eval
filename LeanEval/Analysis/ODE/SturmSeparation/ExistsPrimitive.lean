import Mathlib
import LeanEval.Analysis.ODE.SturmSeparation.PIntegMeas

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

include hJ_open hJ_conn hp hW in
/-- **Existence of a primitive of `p`.** There is `P : ℝ → ℝ` with `P'(x) = p(x)` for
every `x ∈ J`. -/
theorem exists_primitive :
    ∃ P : ℝ → ℝ, ∀ x ∈ J, HasDerivAt P (p x) x := by
  rcases hW with ⟨x₀, hx₀, _⟩
  set P := fun (x : ℝ) => ∫ t in (x₀ : ℝ)..x, p t with hP
  refine ⟨P, λ x hx => ?_⟩
  have hp_int_meas := p_intervalIntegrable_stronglyMeasurable hJ_open hJ_conn hp hx₀ hx
  rcases hp_int_meas with ⟨h_int, h_meas⟩
  have h_cont : ContinuousAt p x :=
    hp.continuousAt (hJ_open.mem_nhds hx)
  exact intervalIntegral.integral_hasDerivAt_right h_int h_meas h_cont

end ODE
end Analysis
end LeanEval
