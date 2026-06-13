import Mathlib

namespace LeanEval
namespace Analysis
namespace ODE

/-- **Wronskian** of `y₁, y₂`: `W(x) = y₁ x · y₂'(x) − y₂ x · y₁'(x)`. -/
noncomputable def wronskian (y₁ y₂ : ℝ → ℝ) (x : ℝ) : ℝ :=
  y₁ x * deriv y₂ x - y₂ x * deriv y₁ x

/-- **Ratio of solutions** `g(x) = y₂ x / y₁ x`, used on the interval where `y₁ ≠ 0`. -/
noncomputable def ratio (y₁ y₂ : ℝ → ℝ) (x : ℝ) : ℝ := y₂ x / y₁ x

end ODE
end Analysis
end LeanEval
