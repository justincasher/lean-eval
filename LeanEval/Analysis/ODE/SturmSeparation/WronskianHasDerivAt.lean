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

include hy₁ hy₁' hy₂ hy₂' in
/-- **Abel/Liouville identity.** The Wronskian satisfies `W'(x) = −p(x) W(x)`. -/
theorem wronskian_hasDerivAt {x : ℝ} (hx : x ∈ J) :
    HasDerivAt (wronskian y₁ y₂) (-(p x * wronskian y₁ y₂ x)) x := by
  have hy₁x : HasDerivAt y₁ (deriv y₁ x) x := hy₁ x hx
  have hy₁'x : HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x := hy₁' x hx
  have hy₂x : HasDerivAt y₂ (deriv y₂ x) x := hy₂ x hx
  have hy₂'x : HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x := hy₂' x hx
  have hA : HasDerivAt (fun t => y₁ t * deriv y₂ t)
      ((deriv y₁ x) * (deriv y₂ x) + y₁ x * (-(p x * deriv y₂ x + q x * y₂ x))) x :=
    HasDerivAt.mul hy₁x hy₂'x
  have hB : HasDerivAt (fun t => y₂ t * deriv y₁ t)
      ((deriv y₂ x) * (deriv y₁ x) + y₂ x * (-(p x * deriv y₁ x + q x * y₁ x))) x :=
    HasDerivAt.mul hy₂x hy₁'x
  have hW : HasDerivAt (wronskian y₁ y₂)
      (((deriv y₁ x) * (deriv y₂ x) + y₁ x * (-(p x * deriv y₂ x + q x * y₂ x))) -
       ((deriv y₂ x) * (deriv y₁ x) + y₂ x * (-(p x * deriv y₁ x + q x * y₁ x)))) x := by
    simpa [wronskian] using HasDerivAt.sub hA hB
  have hW' : ((deriv y₁ x) * (deriv y₂ x) + y₁ x * (-(p x * deriv y₂ x + q x * y₂ x))) -
      ((deriv y₂ x) * (deriv y₁ x) + y₂ x * (-(p x * deriv y₁ x + q x * y₁ x))) =
      -(p x * wronskian y₁ y₂ x) := by
    dsimp [wronskian]
    ring
  rw [hW'] at hW
  exact hW

end ODE
end Analysis
end LeanEval
