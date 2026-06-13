import Mathlib

open Filter Topology

namespace LeanEval
namespace Analysis
namespace ODE

/-- **One-sided derivative sign at the left endpoint.** If `f a = 0`, `f ≥ 0` on `(a,b)`,
and `f` has derivative `L` at `a`, then `0 ≤ L`. -/
theorem deriv_right_nonneg {f : ℝ → ℝ} {L a b : ℝ} (hab : a < b)
    (hf : HasDerivAt f L a) (hfa : f a = 0) (hpos : ∀ x ∈ Set.Ioo a b, 0 ≤ f x) :
    0 ≤ L := by
  have ha_not_mem : a ∉ Set.Ioo a b := by
    rw [Set.mem_Ioo]
    exact fun h => lt_irrefl a h.1
  have h_tendsto : Tendsto (slope f a) (𝓝[Set.Ioo a b] a) (𝓝 L) := by
    have hfw : HasDerivWithinAt f L (Set.Ioo a b) a := hf.hasDerivWithinAt
    exact (hasDerivWithinAt_iff_tendsto_slope' ha_not_mem).mp hfw
  haveI : NeBot (𝓝[Set.Ioo a b] a) := left_nhdsWithin_Ioo_neBot hab
  have h_eventually_nonneg : ∀ᶠ x in 𝓝[Set.Ioo a b] a, 0 ≤ slope f a x := by
    filter_upwards [self_mem_nhdsWithin (s := Set.Ioo a b)] with x hx
    rw [slope_def_field f a x, hfa, sub_zero]
    exact div_nonneg (hpos x hx) (sub_nonneg.mpr hx.1.le)
  exact ge_of_tendsto h_tendsto h_eventually_nonneg

end ODE
end Analysis
end LeanEval
