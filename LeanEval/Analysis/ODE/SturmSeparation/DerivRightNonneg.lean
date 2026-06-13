import Mathlib

namespace LeanEval
namespace Analysis
namespace ODE

/-- **One-sided derivative sign at the left endpoint.** If `f a = 0`, `f ≥ 0` on `(a,b)`,
and `f` has derivative `L` at `a`, then `0 ≤ L`. -/
theorem deriv_right_nonneg {f : ℝ → ℝ} {L a b : ℝ} (hab : a < b)
    (hf : HasDerivAt f L a) (hfa : f a = 0) (hpos : ∀ x ∈ Set.Ioo a b, 0 ≤ f x) :
    0 ≤ L := by
  sorry

end ODE
end Analysis
end LeanEval
