import Mathlib

namespace LeanEval
namespace Analysis
namespace ODE

/-- **Closed interval between two points of `J` stays in `J`.** For an open preconnected
`J ⊆ ℝ` and `x₀, x ∈ J`, the unordered closed interval `[x₀, x]` is contained in `J`. -/
theorem uIcc_subset_of_isOpen_isPreconnected {J : Set ℝ} (hJ_open : IsOpen J)
    (hJ_conn : IsPreconnected J) {x₀ x : ℝ} (hx₀ : x₀ ∈ J) (hx : x ∈ J) :
    Set.uIcc x₀ x ⊆ J := by
  sorry

end ODE
end Analysis
end LeanEval
