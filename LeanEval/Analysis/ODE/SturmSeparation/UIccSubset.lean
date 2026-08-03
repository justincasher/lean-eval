import Mathlib

namespace LeanEval
namespace Analysis
namespace ODE

/-- **Closed interval between two points of `J` stays in `J`.** For an open preconnected
`J ⊆ ℝ` and `x₀, x ∈ J`, the unordered closed interval `[x₀, x]` is contained in `J`. -/
theorem uIcc_subset_of_isOpen_isPreconnected {J : Set ℝ} (_hJ_open : IsOpen J)
    (hJ_conn : IsPreconnected J) {x₀ x : ℝ} (hx₀ : x₀ ∈ J) (hx : x ∈ J) :
    Set.uIcc x₀ x ⊆ J := by
  have hJ_convex : Convex ℝ J := (Real.convex_iff_isPreconnected.mpr hJ_conn)
  have hJ_ordConnected : Set.OrdConnected J := hJ_convex.ordConnected
  exact hJ_ordConnected.uIcc_subset hx₀ hx

end ODE
end Analysis
end LeanEval
