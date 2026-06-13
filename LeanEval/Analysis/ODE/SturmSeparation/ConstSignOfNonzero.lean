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
  -- pick a midpoint m in (a,b)
  rcases exists_between hab with ⟨m, hm_a, hm_b⟩
  have hm : m ∈ Set.Ioo a b := Set.mem_Ioo.mpr ⟨hm_a, hm_b⟩
  have hfm_ne : f m ≠ 0 := hne m hm
  by_cases hpos : 0 < f m
  · left
    intro x hx
    exact pos_of_pos_of_no_interior_zero hf hne hm hx hpos
  · have hneg : f m < 0 := by
      by_contra! H
      -- H: f m ≥ 0; with ¬(0 < f m) we get f m = 0, contradicting hfm_ne
      have : f m = 0 := by linarith
      exact hfm_ne this
    right
    intro x hx
    have h_neg_cont : ContinuousOn (-f) (Set.Icc a b) := hf.neg
    have h_neg_ne : ∀ x ∈ Set.Ioo a b, (-f) x ≠ 0 := by
      intro x hx'
      exact mt neg_eq_zero.mp (hne x hx')
    have h_neg_m_pos : 0 < (-f) m := by
      have : 0 < -(f m) := by linarith
      simpa using this
    have h_neg_x_pos : 0 < (-f) x :=
      pos_of_pos_of_no_interior_zero h_neg_cont h_neg_ne hm hx h_neg_m_pos
    -- (-f) x = -(f x), so 0 < -(f x) gives f x < 0
    have hfx_neg : f x < 0 := by
      have : 0 < -(f x) := by simpa using h_neg_x_pos
      linarith
    exact hfx_neg

end ODE
end Analysis
end LeanEval
