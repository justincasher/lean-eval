import Mathlib

namespace LeanEval
namespace Analysis
namespace ODE

/-- **One-sided derivative sign at the right endpoint.** If `f b = 0`, `f ≥ 0` on `(a,b)`,
and `f` has derivative `L` at `b`, then `L ≤ 0`. -/
theorem deriv_left_nonpos {f : ℝ → ℝ} {L a b : ℝ} (hab : a < b)
    (hf : HasDerivAt f L b) (hfb : f b = 0) (hpos : ∀ x ∈ Set.Ioo a b, 0 ≤ f x) :
    L ≤ 0 := by
  sorry

end ODE
end Analysis
end LeanEval
