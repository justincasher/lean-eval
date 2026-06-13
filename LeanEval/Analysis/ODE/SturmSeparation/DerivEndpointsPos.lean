import Mathlib
import LeanEval.Analysis.ODE.SturmSeparation.DerivRightNonneg
import LeanEval.Analysis.ODE.SturmSeparation.DerivLeftNonpos

namespace LeanEval
namespace Analysis
namespace ODE

/-- **Endpoint derivatives of a positive interior bump.** If `f a = f b = 0`, `f > 0` on
`(a,b)`, `f` has nonzero derivatives `Lₐ, L_b` at the endpoints, then `0 < Lₐ` and
`L_b < 0`. -/
theorem deriv_endpoints_of_pos_interior {f : ℝ → ℝ} {La Lb a b : ℝ} (hab : a < b)
    (hfa' : HasDerivAt f La a) (hfb' : HasDerivAt f Lb b)
    (hfa : f a = 0) (hfb : f b = 0) (hpos : ∀ x ∈ Set.Ioo a b, 0 < f x)
    (hLa : La ≠ 0) (hLb : Lb ≠ 0) :
    0 < La ∧ Lb < 0 := by
  sorry

end ODE
end Analysis
end LeanEval
