import Mathlib
import LeanEval.Analysis.ODE.SturmSeparation.PosOfNoInteriorZero

namespace LeanEval
namespace Analysis
namespace ODE

/-- **A nowhere-vanishing continuous function has constant sign.** If `f` is continuous on
`[a,b]` (with `a < b`) and nonzero on `(a,b)`, then either `f > 0` throughout `(a,b)` or
`f < 0` throughout `(a,b)`. -/
theorem const_sign_of_nonzero {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) (hne : ∀ x ∈ Set.Ioo a b, f x ≠ 0) :
    (∀ x ∈ Set.Ioo a b, 0 < f x) ∨ (∀ x ∈ Set.Ioo a b, f x < 0) := by
  sorry

end ODE
end Analysis
end LeanEval
