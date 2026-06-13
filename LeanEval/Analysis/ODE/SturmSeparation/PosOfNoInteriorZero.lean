import Mathlib

namespace LeanEval
namespace Analysis
namespace ODE

/-- **A nowhere-vanishing continuous function cannot change sign.** If `f` is continuous on
`[a,b]`, nonzero on `(a,b)`, and positive at some `u ∈ (a,b)`, then it is positive at every
`v ∈ (a,b)`. -/
theorem pos_of_pos_of_no_interior_zero {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hne : ∀ x ∈ Set.Ioo a b, f x ≠ 0)
    {u v : ℝ} (hu : u ∈ Set.Ioo a b) (hv : v ∈ Set.Ioo a b) (hfu : 0 < f u) :
    0 < f v := by
  sorry

end ODE
end Analysis
end LeanEval
