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
  rcases hsign with (hpos | hneg)
  · rcases deriv_endpoints_of_pos_interior hab hfa' hfb' hfa hfb hpos hLa hLb with ⟨hLa_pos, hLb_neg⟩
    exact mul_neg_of_pos_of_neg hLa_pos hLb_neg
  · have hga : (-f) a = 0 := by simp [hfa]
    have hgb : (-f) b = 0 := by simp [hfb]
    have hpos_g : ∀ x ∈ Set.Ioo a b, 0 < (-f) x := by
      intro x hx
      have h := hneg x hx
      simpa [Pi.neg_apply] using neg_pos.mpr h
    have hga' : HasDerivAt (-f) (-La) a := hfa'.neg
    have hgb' : HasDerivAt (-f) (-Lb) b := hfb'.neg
    have hnegLa : -La ≠ 0 := neg_ne_zero.mpr hLa
    have hnegLb : -Lb ≠ 0 := neg_ne_zero.mpr hLb
    rcases deriv_endpoints_of_pos_interior hab hga' hgb' hga hgb hpos_g hnegLa hnegLb with ⟨h_negLa_pos, h_negLb_neg⟩
    have hLa_neg : La < 0 := by linarith
    have hLb_pos : 0 < Lb := by linarith
    exact mul_neg_of_neg_of_pos hLa_neg hLb_pos

end ODE
end Analysis
end LeanEval
