import Mathlib
import LeanEval.Analysis.ODE.SturmSeparation.DerivEndpointsPos

namespace LeanEval
namespace Analysis
namespace ODE

/-- **Endpoint derivatives of a constant-sign interior bump.** If `f a = f b = 0`, `f` has
nonzero derivatives `Lₐ, L_b` at the endpoints, and `f` has constant sign on `(a,b)`, then
`Lₐ · L_b < 0`. -/
theorem deriv_endpoints_of_signed_interior {f : ℝ → ℝ} {La Lb a b : ℝ} (hab : a < b)
    (hfa' : HasDerivAt f La a) (hfb' : HasDerivAt f Lb b)
    (hfa : f a = 0) (hfb : f b = 0) (hLa : La ≠ 0) (hLb : Lb ≠ 0)
    (hsign : (∀ x ∈ Set.Ioo a b, 0 < f x) ∨ (∀ x ∈ Set.Ioo a b, f x < 0)) :
    La * Lb < 0 := by
  sorry

end ODE
end Analysis
end LeanEval
