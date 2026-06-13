import Mathlib

open Filter
open Topology

namespace LeanEval
namespace Analysis
namespace ODE

/-- **One-sided derivative sign at the right endpoint.** If `f b = 0`, `f ≥ 0` on `(a,b)`,
and `f` has derivative `L` at `b`, then `L ≤ 0`. -/
theorem deriv_left_nonpos {f : ℝ → ℝ} {L a b : ℝ} (hab : a < b)
    (hf : HasDerivAt f L b) (hfb : f b = 0) (hpos : ∀ x ∈ Set.Ioo a b, 0 ≤ f x) :
    L ≤ 0 := by
  -- `b` is not in `Ioo a b`
  have hb_not_mem : b ∉ Set.Ioo a b := by
    intro h
    exact lt_irrefl b h.2
  -- from `HasDerivAt` to `HasDerivWithinAt` on `Ioo a b`
  have hfw : HasDerivWithinAt f L (Set.Ioo a b) b := hf.hasDerivWithinAt
  -- `HasDerivWithinAt` iff the slope tends to the derivative
  have h_tendsto : Tendsto (slope f b) (𝓝[Set.Ioo a b] b) (𝓝 L) :=
    ((hasDerivWithinAt_iff_tendsto_slope' hb_not_mem).mp hfw)
  -- for `x ∈ Ioo a b`, the slope is nonpositive
  have h_slope_nonpos : ∀ x ∈ Set.Ioo a b, slope f b x ≤ 0 := by
    intro x hx
    have hx_lt_b : x < b := hx.2
    have hx_minus_b_neg : x - b < 0 := sub_lt_zero.mpr hx_lt_b
    have h_fx_nonneg : 0 ≤ f x := hpos x hx
    -- rewrite slope using `slope_def_field`
    rw [slope_def_field f b x, hfb, sub_zero]
    -- now goal: (f x) / (x - b) ≤ 0
    exact (div_nonpos_of_nonneg_of_nonpos h_fx_nonneg (by linarith))
  -- the set `Ioo a b` is in the filter `𝓝[Ioo a b] b`
  have h_mem : Set.Ioo a b ∈ 𝓝[Set.Ioo a b] b := self_mem_nhdsWithin
  have h_event : ∀ᶠ x in 𝓝[Set.Ioo a b] b, slope f b x ≤ 0 := by
    filter_upwards [h_mem] with x hx
    exact h_slope_nonpos x hx
  -- `𝓝[Ioo a b] b` is nontrivial
  haveI : NeBot (𝓝[Set.Ioo a b] b) := right_nhdsWithin_Ioo_neBot hab
  exact le_of_tendsto h_tendsto h_event

end ODE
end Analysis
end LeanEval
