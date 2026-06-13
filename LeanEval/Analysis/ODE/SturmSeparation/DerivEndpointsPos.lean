import Mathlib
import LeanEval.Analysis.ODE.SturmSeparation.DerivRightNonneg
import LeanEval.Analysis.ODE.SturmSeparation.DerivLeftNonpos

open Set
open Filter

open scoped Topology

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
  have hpos_nonneg : ∀ x ∈ Set.Ioo a b, 0 ≤ f x := by
    intro x hx
    exact le_of_lt (hpos x hx)
  -- From HasDerivAt at a, the right-hand slope limit is La
  have h_right_tendsto : Tendsto (slope f a) (𝓝[>] a) (𝓝 La) :=
    (hasDerivAt_iff_tendsto_slope_left_right.mp hfa').2
  -- For x in Ioo a b with x > a, slope f a x = f x / (x - a) > 0
  have h_slope_nonneg : ∀ᶠ x in 𝓝[>] a, 0 ≤ slope f a x := by
    -- Ioo a b is in 𝓝[>] a when a < b
    have hmem : Set.Ioo a b ∈ 𝓝[>] a := by
      rw [nhdsWithin, Filter.mem_inf_iff]
      refine ⟨Set.Ioo (a - 1) b, Ioo_mem_nhds (by linarith) (by linarith),
              Set.Ioi a, ?_, ?_⟩
      · exact Filter.mem_principal_self (Set.Ioi a)
      · calc
          Set.Ioo a b = {x | a < x ∧ x < b} := rfl
          _ = {x | a - 1 < x ∧ x < b} ∩ {x | a < x} := by
            ext x; constructor
            · rintro ⟨hax, hxb⟩; exact ⟨⟨by linarith, hxb⟩, hax⟩
            · rintro ⟨⟨h_left, hxb⟩, hax⟩; exact ⟨hax, hxb⟩
          _ = Set.Ioo (a - 1) b ∩ Set.Ioi a := rfl
    filter_upwards [hmem] with x hx
    have hxpos : 0 < f x := hpos x hx
    have hx_gt_a : a < x := Set.mem_Ioo.mp hx |>.left
    have h_slope_pos : 0 < slope f a x := by
      calc
        slope f a x = (f x - f a) / (x - a) := by
          dsimp [slope]
          ring
        _ = f x / (x - a) := by simp [hfa]
        _ > 0 := div_pos hxpos (sub_pos.mpr hx_gt_a)
    exact le_of_lt h_slope_pos
  have h_La_nonneg : 0 ≤ La :=
    ge_of_tendsto h_right_tendsto h_slope_nonneg
  -- Similarly for the left endpoint b
  have h_left_tendsto : Tendsto (slope f b) (𝓝[<] b) (𝓝 Lb) :=
    (hasDerivAt_iff_tendsto_slope_left_right.mp hfb').1
  have h_slope_nonpos : ∀ᶠ x in 𝓝[<] b, slope f b x ≤ 0 := by
    have hmem : Set.Ioo a b ∈ 𝓝[<] b := by
      rw [nhdsWithin, Filter.mem_inf_iff]
      refine ⟨Set.Ioo a (b + 1), Ioo_mem_nhds (by linarith) (by linarith),
              Set.Iio b, ?_, ?_⟩
      · exact Filter.mem_principal_self (Set.Iio b)
      · calc
          Set.Ioo a b = {x | a < x ∧ x < b} := rfl
          _ = {x | a < x ∧ x < b + 1} ∩ {x | x < b} := by
            ext x; constructor
            · rintro ⟨hax, hxb⟩; exact ⟨⟨hax, by linarith⟩, hxb⟩
            · rintro ⟨⟨hax, hx_lt_b_plus_one⟩, hxb⟩; exact ⟨hax, hxb⟩
          _ = Set.Ioo a (b + 1) ∩ Set.Iio b := rfl
    filter_upwards [hmem] with x hx
    have hxpos : 0 < f x := hpos x hx
    have hx_lt_b : x < b := Set.mem_Ioo.mp hx |>.right
    have h_slope_neg : slope f b x < 0 := by
      calc
        slope f b x = (f x - f b) / (x - b) := by
          dsimp [slope]
          ring
        _ = f x / (x - b) := by simp [hfb]
        _ < 0 := div_neg_of_pos_of_neg hxpos (sub_neg.mpr hx_lt_b)
    exact le_of_lt h_slope_neg
  have h_Lb_nonpos : Lb ≤ 0 :=
    le_of_tendsto h_left_tendsto h_slope_nonpos
  -- Now combine with nonzero conditions
  have h_pos_La : 0 < La := by
    by_contra! h
    -- h: La ≤ 0. We know 0 ≤ La, so La = 0, contradicting hLa
    have : La = 0 := le_antisymm h h_La_nonneg
    exact hLa this
  have h_neg_Lb : Lb < 0 := by
    by_contra! h
    -- h: 0 ≤ Lb. We know Lb ≤ 0, so Lb = 0, contradicting hLb
    have : Lb = 0 := le_antisymm h_Lb_nonpos h
    exact hLb this
  exact ⟨h_pos_La, h_neg_Lb⟩

end ODE
end Analysis
end LeanEval
