import Mathlib

namespace LeanEval
namespace Analysis
namespace ODE

/-- **Wronskian** of `y₁, y₂`: `W(x) = y₁ x · y₂'(x) − y₂ x · y₁'(x)`. -/
noncomputable def wronskian (y₁ y₂ : ℝ → ℝ) (x : ℝ) : ℝ :=
  y₁ x * deriv y₂ x - y₂ x * deriv y₁ x

/-- **Ratio of solutions** `g(x) = y₂ x / y₁ x`, used on the interval where `y₁ ≠ 0`. -/
noncomputable def ratio (y₁ y₂ : ℝ → ℝ) (x : ℝ) : ℝ := y₂ x / y₁ x

end ODE
end Analysis
end LeanEval
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
  by_contra! H
  -- H : f v ≤ 0
  have hfv_neg : f v < 0 := by
    refine lt_of_le_of_ne H (hne v hv)
  have h0_mem_uIcc : (0 : ℝ) ∈ Set.uIcc (f u) (f v) := by
    rw [Set.mem_uIcc]
    -- f v < 0 < f u, so f v ≤ 0 ∧ 0 ≤ f u
    exact Or.inr ⟨hfv_neg.le, hfu.le⟩
  have h_cont : ContinuousOn f (Set.uIcc u v) := by
    -- uIcc u v ⊆ Ioo a b ⊆ Icc a b
    have h1 : Set.uIcc u v ⊆ Set.Ioo a b :=
      Set.OrdConnected.uIcc_subset (Set.ordConnected_Ioo (a := a) (b := b)) hu hv
    have h2 : Set.Ioo a b ⊆ Set.Icc a b := Set.Ioo_subset_Icc_self
    exact hf.mono (h1.trans h2)
  have h_ivt : Set.uIcc (f u) (f v) ⊆ f '' Set.uIcc u v :=
    intermediate_value_uIcc h_cont
  have h0_image : (0 : ℝ) ∈ f '' Set.uIcc u v :=
    h_ivt h0_mem_uIcc
  rcases h0_image with ⟨w, hw, hfw⟩
  -- w ∈ uIcc u v, f w = 0
  have hw_Ioo : w ∈ Set.Ioo a b :=
    Set.OrdConnected.uIcc_subset (Set.ordConnected_Ioo (a := a) (b := b)) hu hv hw
  have h_contra := hne w hw_Ioo
  -- h_contra : f w ≠ 0, but hfw : f w = 0
  exact h_contra hfw

end ODE
end Analysis
end LeanEval
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
namespace LeanEval
namespace Analysis
namespace ODE

variable {p q y₁ y₂ : ℝ → ℝ} {a b : ℝ} {J : Set ℝ}
  (hab : a < b)
  (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
  (hJ_sub : Set.Icc a b ⊆ J)
  (hp : ContinuousOn p J) (hq : ContinuousOn q J)
  (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
  (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
  (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
  (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
  (hW : ∃ x₀ ∈ J, y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ ≠ 0)
  (hza : y₁ a = 0) (hzb : y₁ b = 0)
  (hne : ∀ x ∈ Set.Ioo a b, y₁ x ≠ 0)

include hy₁ hy₁' hy₂ hy₂' in
/-- **Abel/Liouville identity.** The Wronskian satisfies `W'(x) = −p(x) W(x)`. -/
theorem wronskian_hasDerivAt {x : ℝ} (hx : x ∈ J) :
    HasDerivAt (wronskian y₁ y₂) (-(p x * wronskian y₁ y₂ x)) x := by
  have hy₁x : HasDerivAt y₁ (deriv y₁ x) x := hy₁ x hx
  have hy₁'x : HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x := hy₁' x hx
  have hy₂x : HasDerivAt y₂ (deriv y₂ x) x := hy₂ x hx
  have hy₂'x : HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x := hy₂' x hx
  have hA : HasDerivAt (fun t => y₁ t * deriv y₂ t)
      ((deriv y₁ x) * (deriv y₂ x) + y₁ x * (-(p x * deriv y₂ x + q x * y₂ x))) x :=
    HasDerivAt.mul hy₁x hy₂'x
  have hB : HasDerivAt (fun t => y₂ t * deriv y₁ t)
      ((deriv y₂ x) * (deriv y₁ x) + y₂ x * (-(p x * deriv y₁ x + q x * y₁ x))) x :=
    HasDerivAt.mul hy₂x hy₁'x
  have hW : HasDerivAt (wronskian y₁ y₂)
      (((deriv y₁ x) * (deriv y₂ x) + y₁ x * (-(p x * deriv y₂ x + q x * y₂ x))) -
       ((deriv y₂ x) * (deriv y₁ x) + y₂ x * (-(p x * deriv y₁ x + q x * y₁ x)))) x := by
    change HasDerivAt
      ((fun t => y₁ t * deriv y₂ t) - fun t => y₂ t * deriv y₁ t) _ x
    exact HasDerivAt.sub hA hB
  have hW' : ((deriv y₁ x) * (deriv y₂ x) + y₁ x * (-(p x * deriv y₂ x + q x * y₂ x))) -
      ((deriv y₂ x) * (deriv y₁ x) + y₂ x * (-(p x * deriv y₁ x + q x * y₁ x))) =
      -(p x * wronskian y₁ y₂ x) := by
    dsimp [wronskian]
    ring
  rw [hW'] at hW
  exact hW

end ODE
end Analysis
end LeanEval
namespace LeanEval
namespace Analysis
namespace ODE

open scoped MeasureTheory

variable {p q y₁ y₂ : ℝ → ℝ} {a b : ℝ} {J : Set ℝ}
  (hab : a < b)
  (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
  (hJ_sub : Set.Icc a b ⊆ J)
  (hp : ContinuousOn p J) (hq : ContinuousOn q J)
  (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
  (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
  (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
  (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
  (hW : ∃ x₀ ∈ J, y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ ≠ 0)
  (hza : y₁ a = 0) (hzb : y₁ b = 0)
  (hne : ∀ x ∈ Set.Ioo a b, y₁ x ≠ 0)

include hJ_open hJ_conn hp in
/-- **Integrability and measurability of `p` along `J`.** For `x₀, x ∈ J`, `p` is interval
integrable from `x₀` to `x` and strongly measurable at the neighborhood filter of `x`. -/
theorem p_intervalIntegrable_stronglyMeasurable {x₀ : ℝ} (hx₀ : x₀ ∈ J)
    {x : ℝ} (hx : x ∈ J) :
    IntervalIntegrable p MeasureTheory.volume x₀ x ∧
      StronglyMeasurableAtFilter p (nhds x) := by
  have h_uIcc_sub : Set.uIcc x₀ x ⊆ J :=
    uIcc_subset_of_isOpen_isPreconnected hJ_open hJ_conn hx₀ hx
  have hp_uIcc : ContinuousOn p (Set.uIcc x₀ x) := hp.mono h_uIcc_sub
  have h_int : IntervalIntegrable p MeasureTheory.volume x₀ x :=
    hp_uIcc.intervalIntegrable
  have h_meas : StronglyMeasurableAtFilter p (nhds x) :=
    ContinuousOn.stronglyMeasurableAtFilter hJ_open hp x hx
  exact ⟨h_int, h_meas⟩

end ODE
end Analysis
end LeanEval
namespace LeanEval
namespace Analysis
namespace ODE

variable {p q y₁ y₂ : ℝ → ℝ} {a b : ℝ} {J : Set ℝ}
  (hab : a < b)
  (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
  (hJ_sub : Set.Icc a b ⊆ J)
  (hp : ContinuousOn p J) (hq : ContinuousOn q J)
  (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
  (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
  (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
  (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
  (hW : ∃ x₀ ∈ J, y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ ≠ 0)
  (hza : y₁ a = 0) (hzb : y₁ b = 0)
  (hne : ∀ x ∈ Set.Ioo a b, y₁ x ≠ 0)

include hJ_open hJ_conn hp hW in
/-- **Existence of a primitive of `p`.** There is `P : ℝ → ℝ` with `P'(x) = p(x)` for
every `x ∈ J`. -/
theorem exists_primitive :
    ∃ P : ℝ → ℝ, ∀ x ∈ J, HasDerivAt P (p x) x := by
  rcases hW with ⟨x₀, hx₀, _⟩
  set P := fun (x : ℝ) => ∫ t in (x₀ : ℝ)..x, p t with hP
  refine ⟨P, λ x hx => ?_⟩
  have hp_int_meas := p_intervalIntegrable_stronglyMeasurable hJ_open hJ_conn hp hx₀ hx
  rcases hp_int_meas with ⟨h_int, h_meas⟩
  have h_cont : ContinuousAt p x :=
    hp.continuousAt (hJ_open.mem_nhds hx)
  exact intervalIntegral.integral_hasDerivAt_right h_int h_meas h_cont

end ODE
end Analysis
end LeanEval
namespace LeanEval
namespace Analysis
namespace ODE

variable {p q y₁ y₂ : ℝ → ℝ} {a b : ℝ} {J : Set ℝ}
  (hab : a < b)
  (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
  (hJ_sub : Set.Icc a b ⊆ J)
  (hp : ContinuousOn p J) (hq : ContinuousOn q J)
  (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
  (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
  (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
  (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
  (hW : ∃ x₀ ∈ J, y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ ≠ 0)
  (hza : y₁ a = 0) (hzb : y₁ b = 0)
  (hne : ∀ x ∈ Set.Ioo a b, y₁ x ≠ 0)

include hy₁ hy₁' hy₂ hy₂' in
/-- **The product `W·eᴾ` has zero derivative.** For any primitive `P` of `p` on `J`, the
function `x ↦ W(x) eᴾ⁽ˣ⁾` has derivative `0` at every point of `J`. -/
theorem wronskian_mul_exp_hasDerivAt_zero {P : ℝ → ℝ}
    (hP : ∀ x ∈ J, HasDerivAt P (p x) x) {x : ℝ} (hx : x ∈ J) :
    HasDerivAt (fun t => wronskian y₁ y₂ t * Real.exp (P t)) 0 x := by
  have hWx : HasDerivAt (wronskian y₁ y₂) (-(p x * wronskian y₁ y₂ x)) x :=
    wronskian_hasDerivAt hy₁ hy₁' hy₂ hy₂' hx
  have hPx : HasDerivAt P (p x) x := hP x hx
  have hExpPx : HasDerivAt (fun t => Real.exp (P t)) (Real.exp (P x) * p x) x :=
    hPx.exp
  have hMul : HasDerivAt (fun t => wronskian y₁ y₂ t * Real.exp (P t))
      ((-(p x * wronskian y₁ y₂ x)) * Real.exp (P x) + wronskian y₁ y₂ x * (Real.exp (P x) * p x)) x :=
    HasDerivAt.mul hWx hExpPx
  have hZero : (-(p x * wronskian y₁ y₂ x)) * Real.exp (P x) + wronskian y₁ y₂ x * (Real.exp (P x) * p x) = 0 := by
    ring
  rw [hZero] at hMul
  exact hMul

end ODE
end Analysis
end LeanEval
namespace LeanEval
namespace Analysis
namespace ODE

variable {p q y₁ y₂ : ℝ → ℝ} {a b : ℝ} {J : Set ℝ}
  (hab : a < b)
  (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
  (hJ_sub : Set.Icc a b ⊆ J)
  (hp : ContinuousOn p J) (hq : ContinuousOn q J)
  (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
  (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
  (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
  (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
  (hW : ∃ x₀ ∈ J, y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ ≠ 0)
  (hza : y₁ a = 0) (hzb : y₁ b = 0)
  (hne : ∀ x ∈ Set.Ioo a b, y₁ x ≠ 0)

include hJ_open hJ_conn hy₁ hy₁' hy₂ hy₂' in
/-- **`W·eᴾ` is constant on `J`.** For any primitive `P` of `p` and any `x₀, x ∈ J`,
`W(x) eᴾ⁽ˣ⁾ = W(x₀) eᴾ⁽ˣ⁰⁾`. -/
theorem wronskian_mul_exp_const {P : ℝ → ℝ}
    (hP : ∀ x ∈ J, HasDerivAt P (p x) x) {x₀ : ℝ} (hx₀ : x₀ ∈ J) {x : ℝ} (hx : x ∈ J) :
    wronskian y₁ y₂ x * Real.exp (P x) = wronskian y₁ y₂ x₀ * Real.exp (P x₀) := by
  let h := fun t : ℝ => wronskian y₁ y₂ t * Real.exp (P t)
  have hderiv : ∀ z ∈ J, HasDerivAt h 0 z :=
    fun z hz => wronskian_mul_exp_hasDerivAt_zero hy₁ hy₁' hy₂ hy₂' hP hz
  have uIcc_sub : Set.uIcc x₀ x ⊆ J :=
    uIcc_subset_of_isOpen_isPreconnected hJ_open hJ_conn hx₀ hx
  have hx₀_uIcc : x₀ ∈ Set.uIcc x₀ x := Set.left_mem_uIcc
  have hx_uIcc : x ∈ Set.uIcc x₀ x := Set.right_mem_uIcc
  by_cases hx_eq : x₀ = x
  · subst hx_eq; rfl
  · have ha_lt_b : min x₀ x < max x₀ x := by
      by_cases hx₀_le_x : x₀ ≤ x
      · have hx₀_lt_x : x₀ < x := lt_of_le_of_ne hx₀_le_x hx_eq
        calc
          min x₀ x = x₀ := min_eq_left hx₀_le_x
          _ < x := hx₀_lt_x
          _ = max x₀ x := (max_eq_right hx₀_le_x).symm
      · have hx_lt_x₀ : x < x₀ := by
          exact lt_of_not_ge hx₀_le_x
        calc
          min x₀ x = x := min_eq_right (by exact hx_lt_x₀.le)
          _ < x₀ := hx_lt_x₀
          _ = max x₀ x := (max_eq_left (by exact hx_lt_x₀.le)).symm
    let a := min x₀ x
    let b := max x₀ x
    have ha_lt_b' : a < b := ha_lt_b
    have hIcc_eq : Set.Icc a b = Set.uIcc x₀ x := by
      calc
        Set.Icc a b = Set.Icc (min x₀ x) (max x₀ x) := rfl
        _ = Set.uIcc x₀ x := rfl
    have hIcc_sub : Set.Icc a b ⊆ J := by
      rw [hIcc_eq]
      exact uIcc_sub
    have h_diff : DifferentiableOn ℝ h (Set.Icc a b) := by
      intro z hz
      have hz_in_J : z ∈ J := hIcc_sub hz
      have hz_deriv : HasDerivAt h 0 z := hderiv z hz_in_J
      have hz_derivWithin : HasDerivWithinAt h 0 (Set.Icc a b) z :=
        hz_deriv.hasDerivWithinAt
      exact hz_derivWithin.differentiableWithinAt
    have h_derivWithin : ∀ z ∈ Set.Ico a b, derivWithin h (Set.Icc a b) z = 0 := by
      intro z hz
      rcases Set.mem_Ico.1 hz with ⟨hz_a, hz_b⟩
      have hz_Icc : z ∈ Set.Icc a b := Set.mem_Icc.mpr ⟨hz_a, hz_b.le⟩
      have hz_in_J : z ∈ J := hIcc_sub hz_Icc
      have hz_deriv : HasDerivAt h 0 z := hderiv z hz_in_J
      have hz_derivWithin : HasDerivWithinAt h 0 (Set.Icc a b) z :=
        hz_deriv.hasDerivWithinAt
      have h_unique : UniqueDiffWithinAt ℝ (Set.Icc a b) z :=
        (uniqueDiffOn_Icc ha_lt_b') z hz_Icc
      exact hz_derivWithin.derivWithin h_unique
    have h_const : ∀ z ∈ Set.Icc a b, h z = h a :=
      constant_of_derivWithin_zero h_diff h_derivWithin
    have hx₀_Icc : x₀ ∈ Set.Icc a b := by
      rw [hIcc_eq]
      exact hx₀_uIcc
    have hx_Icc : x ∈ Set.Icc a b := by
      rw [hIcc_eq]
      exact hx_uIcc
    calc
      h x = h a := h_const x hx_Icc
      _ = h x₀ := (h_const x₀ hx₀_Icc).symm

end ODE
end Analysis
end LeanEval
namespace LeanEval
namespace Analysis
namespace ODE

variable {p q y₁ y₂ : ℝ → ℝ} {a b : ℝ} {J : Set ℝ}
  (hab : a < b)
  (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
  (hJ_sub : Set.Icc a b ⊆ J)
  (hp : ContinuousOn p J) (hq : ContinuousOn q J)
  (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
  (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
  (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
  (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
  (hW : ∃ x₀ ∈ J, y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ ≠ 0)
  (hza : y₁ a = 0) (hzb : y₁ b = 0)
  (hne : ∀ x ∈ Set.Ioo a b, y₁ x ≠ 0)

include hJ_open hJ_conn hy₁ hy₁' hy₂ hy₂' hW in
/-- **Closed form of the Wronskian.** There is a constant `C ≠ 0` with
`W(x) = C e^{−P(x)}` for every `x ∈ J`. -/
theorem wronskian_eq_const_mul_exp {P : ℝ → ℝ}
    (hP : ∀ x ∈ J, HasDerivAt P (p x) x) :
    ∃ C : ℝ, C ≠ 0 ∧ ∀ x ∈ J, wronskian y₁ y₂ x = C * Real.exp (-(P x)) := by
  rcases hW with ⟨x₀, hx₀, hWx₀⟩
  have hWx₀' : wronskian y₁ y₂ x₀ ≠ 0 := hWx₀
  have hpos : Real.exp (P x₀) > 0 := Real.exp_pos (P x₀)
  have hC_ne_zero : wronskian y₁ y₂ x₀ * Real.exp (P x₀) ≠ 0 :=
    mul_ne_zero hWx₀' hpos.ne'
  refine ⟨wronskian y₁ y₂ x₀ * Real.exp (P x₀), hC_ne_zero, λ x hx => ?_⟩
  have h_eq : wronskian y₁ y₂ x * Real.exp (P x) = wronskian y₁ y₂ x₀ * Real.exp (P x₀) :=
    wronskian_mul_exp_const hJ_open hJ_conn hy₁ hy₁' hy₂ hy₂' hP hx₀ hx
  have h_nonzero : Real.exp (P x) ≠ 0 := (Real.exp_pos (P x)).ne'
  calc
    wronskian y₁ y₂ x
        = (wronskian y₁ y₂ x * Real.exp (P x)) * (Real.exp (P x))⁻¹ := by
      field_simp [h_nonzero]
    _ = (wronskian y₁ y₂ x₀ * Real.exp (P x₀)) * (Real.exp (P x))⁻¹ := by rw [h_eq]
    _ = (wronskian y₁ y₂ x₀ * Real.exp (P x₀)) * Real.exp (-(P x)) := by rw [Real.exp_neg]

end ODE
end Analysis
end LeanEval
namespace LeanEval
namespace Analysis
namespace ODE

variable {p q y₁ y₂ : ℝ → ℝ} {a b : ℝ} {J : Set ℝ}
  (hab : a < b)
  (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
  (hJ_sub : Set.Icc a b ⊆ J)
  (hp : ContinuousOn p J) (hq : ContinuousOn q J)
  (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
  (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
  (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
  (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
  (hW : ∃ x₀ ∈ J, y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ ≠ 0)
  (hza : y₁ a = 0) (hzb : y₁ b = 0)
  (hne : ∀ x ∈ Set.Ioo a b, y₁ x ≠ 0)

include hJ_open hJ_conn hp hy₁ hy₁' hy₂ hy₂' hW in
/-- **The Wronskian has constant sign.** For all `s, t ∈ J`, `0 < W(s) W(t)`; in
particular `W` is nonzero on `J`. -/
theorem wronskian_mul_pos {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J) :
    0 < wronskian y₁ y₂ s * wronskian y₁ y₂ t := by
  have hP : ∃ P : ℝ → ℝ, ∀ x ∈ J, HasDerivAt P (p x) x :=
    exists_primitive hJ_open hJ_conn hp hW
  rcases hP with ⟨P, hP⟩
  have hW_eq : ∃ C : ℝ, C ≠ 0 ∧ ∀ x ∈ J, wronskian y₁ y₂ x = C * Real.exp (-(P x)) :=
    wronskian_eq_const_mul_exp hJ_open hJ_conn hy₁ hy₁' hy₂ hy₂' hW hP
  rcases hW_eq with ⟨C, hC_ne, hW_eq⟩
  have hprod : wronskian y₁ y₂ s * wronskian y₁ y₂ t = C ^ 2 * (Real.exp (-(P s)) * Real.exp (-(P t))) := by
    rw [hW_eq s hs, hW_eq t ht]
    ring
  rw [hprod]
  have hC_sq_pos : 0 < C ^ 2 := sq_pos_of_ne_zero hC_ne
  have h_exp_pos_s : 0 < Real.exp (-(P s)) := Real.exp_pos _
  have h_exp_pos_t : 0 < Real.exp (-(P t)) := Real.exp_pos _
  exact mul_pos hC_sq_pos (mul_pos h_exp_pos_s h_exp_pos_t)

end ODE
end Analysis
end LeanEval
namespace LeanEval
namespace Analysis
namespace ODE

variable {p q y₁ y₂ : ℝ → ℝ} {a b : ℝ} {J : Set ℝ}
  (hab : a < b)
  (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
  (hJ_sub : Set.Icc a b ⊆ J)
  (hp : ContinuousOn p J) (hq : ContinuousOn q J)
  (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
  (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
  (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
  (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
  (hW : ∃ x₀ ∈ J, y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ ≠ 0)
  (hza : y₁ a = 0) (hzb : y₁ b = 0)
  (hne : ∀ x ∈ Set.Ioo a b, y₁ x ≠ 0)

/-- **Wronskian at a zero of `y₁`.** If `y₁ t = 0` then `W(t) = −y₂(t) y₁'(t)`. -/
theorem wronskian_at_zero {t : ℝ} (ht : y₁ t = 0) :
    wronskian y₁ y₂ t = -(y₂ t * deriv y₁ t) := by
  simp [wronskian, ht]

end ODE
end Analysis
end LeanEval
namespace LeanEval
namespace Analysis
namespace ODE

variable {p q y₁ y₂ : ℝ → ℝ} {a b : ℝ} {J : Set ℝ}
  (hab : a < b)
  (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
  (hJ_sub : Set.Icc a b ⊆ J)
  (hp : ContinuousOn p J) (hq : ContinuousOn q J)
  (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
  (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
  (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
  (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
  (hW : ∃ x₀ ∈ J, y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ ≠ 0)
  (hza : y₁ a = 0) (hzb : y₁ b = 0)
  (hne : ∀ x ∈ Set.Ioo a b, y₁ x ≠ 0)

include hJ_open hJ_conn hp hy₁ hy₁' hy₂ hy₂' hW in
/-- **Both factors are nonzero at a zero of `y₁`.** If `t ∈ J` and `y₁ t = 0`, then
`y₂ t ≠ 0` and `y₁'(t) ≠ 0`. -/
theorem factors_nonzero_at_zero {t : ℝ} (ht : t ∈ J) (hy : y₁ t = 0) :
    y₂ t ≠ 0 ∧ deriv y₁ t ≠ 0 := by
  -- By wronskian_at_zero, W(t) = -(y₂ t * deriv y₁ t) when y₁ t = 0
  have hW_eq : wronskian y₁ y₂ t = -(y₂ t * deriv y₁ t) := wronskian_at_zero hy
  -- By wronskian_mul_pos, W(t)² > 0, hence W(t) ≠ 0
  have hW_pos : 0 < wronskian y₁ y₂ t * wronskian y₁ y₂ t :=
    wronskian_mul_pos hJ_open hJ_conn hp hy₁ hy₁' hy₂ hy₂' hW ht ht
  have hW_ne : wronskian y₁ y₂ t ≠ 0 := by
    intro hzero
    rw [hzero] at hW_pos
    linarith
  -- Therefore -(y₂ t * deriv y₁ t) ≠ 0, so y₂ t * deriv y₁ t ≠ 0
  have hprod_ne : y₂ t * deriv y₁ t ≠ 0 := by
    intro hzero
    apply hW_ne
    rw [hW_eq]
    simp [hzero]
  -- mul_ne_zero_iff gives both factors nonzero
  exact mul_ne_zero_iff.mp hprod_ne

end ODE
end Analysis
end LeanEval
namespace LeanEval
namespace Analysis
namespace ODE

variable {p q y₁ y₂ : ℝ → ℝ} {a b : ℝ} {J : Set ℝ}
  (hab : a < b)
  (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
  (hJ_sub : Set.Icc a b ⊆ J)
  (hp : ContinuousOn p J) (hq : ContinuousOn q J)
  (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
  (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
  (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
  (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
  (hW : ∃ x₀ ∈ J, y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ ≠ 0)
  (hza : y₁ a = 0) (hzb : y₁ b = 0)
  (hne : ∀ x ∈ Set.Ioo a b, y₁ x ≠ 0)

include hab hJ_open hJ_conn hJ_sub hp hy₁ hy₁' hy₂ hy₂' hW hza hzb in
/-- **Endpoint values are nonzero.** `y₂ a ≠ 0`, `y₂ b ≠ 0`, `y₁'(a) ≠ 0`, `y₁'(b) ≠ 0`. -/
theorem endpoints_nonzero :
    y₂ a ≠ 0 ∧ y₂ b ≠ 0 ∧ deriv y₁ a ≠ 0 ∧ deriv y₁ b ≠ 0 := by
  have haJ : a ∈ J := hJ_sub (Set.mem_Icc.mpr ⟨le_rfl, le_of_lt hab⟩)
  have hbJ : b ∈ J := hJ_sub (Set.mem_Icc.mpr ⟨le_of_lt hab, le_rfl⟩)
  rcases factors_nonzero_at_zero hJ_open hJ_conn hp hy₁ hy₁' hy₂ hy₂' hW haJ hza with ⟨ha2, ha1'⟩
  rcases factors_nonzero_at_zero hJ_open hJ_conn hp hy₁ hy₁' hy₂ hy₂' hW hbJ hzb with ⟨hb2, hb1'⟩
  exact ⟨ha2, hb2, ha1', hb1'⟩

end ODE
end Analysis
end LeanEval
namespace LeanEval
namespace Analysis
namespace ODE

variable {p q y₁ y₂ : ℝ → ℝ} {a b : ℝ} {J : Set ℝ}
  (hab : a < b)
  (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
  (hJ_sub : Set.Icc a b ⊆ J)
  (hp : ContinuousOn p J) (hq : ContinuousOn q J)
  (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
  (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
  (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
  (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
  (hW : ∃ x₀ ∈ J, y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ ≠ 0)
  (hza : y₁ a = 0) (hzb : y₁ b = 0)
  (hne : ∀ x ∈ Set.Ioo a b, y₁ x ≠ 0)

include hJ_sub hy₁ hy₂ hne in
/-- **Derivative of the ratio.** On `(a,b)`, `g = y₂/y₁` has derivative `W(x) / y₁(x)²`. -/
theorem ratio_hasDerivAt {x : ℝ} (hx : x ∈ Set.Ioo a b) :
    HasDerivAt (ratio y₁ y₂) (wronskian y₁ y₂ x / (y₁ x) ^ 2) x := by
  have hxJ : x ∈ J := hJ_sub (Set.Ioo_subset_Icc_self hx)
  have hy₁x : HasDerivAt y₁ (deriv y₁ x) x := hy₁ x hxJ
  have hy₂x : HasDerivAt y₂ (deriv y₂ x) x := hy₂ x hxJ
  have hy₁_ne : y₁ x ≠ 0 := hne x hx
  have h_div : HasDerivAt (y₂ / y₁) ((deriv y₂ x * y₁ x - y₂ x * deriv y₁ x) / (y₁ x) ^ 2) x :=
    HasDerivAt.div hy₂x hy₁x hy₁_ne
  unfold ratio wronskian
  change HasDerivAt (y₂ / y₁)
    ((y₁ x * deriv y₂ x - y₂ x * deriv y₁ x) / y₁ x ^ 2) x
  convert h_div using 1
  ring

end ODE
end Analysis
end LeanEval
namespace LeanEval
namespace Analysis
namespace ODE

variable {p q y₁ y₂ : ℝ → ℝ} {a b : ℝ} {J : Set ℝ}
  (hab : a < b)
  (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
  (hJ_sub : Set.Icc a b ⊆ J)
  (hp : ContinuousOn p J) (hq : ContinuousOn q J)
  (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
  (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
  (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
  (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
  (hW : ∃ x₀ ∈ J, y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ ≠ 0)
  (hza : y₁ a = 0) (hzb : y₁ b = 0)
  (hne : ∀ x ∈ Set.Ioo a b, y₁ x ≠ 0)

include hJ_sub hy₁ hy₂ hne in
/-- **The ratio is continuous on `(a,b)`.** -/
theorem ratio_continuousOn :
    ContinuousOn (ratio y₁ y₂) (Set.Ioo a b) := by
  have hdiff : DifferentiableOn ℝ (ratio y₁ y₂) (Set.Ioo a b) := by
    intro x hx
    have hderiv := ratio_hasDerivAt hJ_sub hy₁ hy₂ hne hx
    have hdiffAt : DifferentiableAt ℝ (ratio y₁ y₂) x :=
      hderiv.differentiableAt
    exact hdiffAt.differentiableWithinAt
  exact hdiff.continuousOn

end ODE
end Analysis
end LeanEval
namespace LeanEval
namespace Analysis
namespace ODE

variable {p q y₁ y₂ : ℝ → ℝ} {a b : ℝ} {J : Set ℝ}
  (hab : a < b)
  (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
  (hJ_sub : Set.Icc a b ⊆ J)
  (hp : ContinuousOn p J) (hq : ContinuousOn q J)
  (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
  (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
  (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
  (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
  (hW : ∃ x₀ ∈ J, y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ ≠ 0)
  (hza : y₁ a = 0) (hzb : y₁ b = 0)
  (hne : ∀ x ∈ Set.Ioo a b, y₁ x ≠ 0)

include hJ_open hJ_conn hp hy₁ hy₁' hy₂ hy₂' hW in
/-- **The Wronskian keeps the sign of a reference point.** For `m ∈ J`, if `W(m) > 0` then
`W(x) > 0` for all `x ∈ J`, and if `W(m) < 0` then `W(x) < 0` for all `x ∈ J`. -/
theorem wronskian_sign_of_ref {m : ℝ} (hm : m ∈ J) {x : ℝ} (hx : x ∈ J) :
    (0 < wronskian y₁ y₂ m → 0 < wronskian y₁ y₂ x) ∧
      (wronskian y₁ y₂ m < 0 → wronskian y₁ y₂ x < 0) := by
  have hprod_pos : 0 < wronskian y₁ y₂ m * wronskian y₁ y₂ x :=
    wronskian_mul_pos (hJ_open := hJ_open) (hJ_conn := hJ_conn) (hp := hp) (hy₁ := hy₁) (hy₁' := hy₁') (hy₂ := hy₂) (hy₂' := hy₂') (hW := hW) hm hx
  constructor
  · intro hWm_pos
    have hWx_pos : 0 < wronskian y₁ y₂ x := by
      nlinarith
    exact hWx_pos
  · intro hWm_neg
    have hWx_neg : wronskian y₁ y₂ x < 0 := by
      nlinarith
    exact hWx_neg

end ODE
end Analysis
end LeanEval
namespace LeanEval
namespace Analysis
namespace ODE

variable {p q y₁ y₂ : ℝ → ℝ} {a b : ℝ} {J : Set ℝ}
  (hab : a < b)
  (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
  (hJ_sub : Set.Icc a b ⊆ J)
  (hp : ContinuousOn p J) (hq : ContinuousOn q J)
  (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
  (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
  (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
  (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
  (hW : ∃ x₀ ∈ J, y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ ≠ 0)
  (hza : y₁ a = 0) (hzb : y₁ b = 0)
  (hne : ∀ x ∈ Set.Ioo a b, y₁ x ≠ 0)

include hJ_open hJ_conn hJ_sub hp hy₁ hy₁' hy₂ hy₂' hW hne in
/-- **The ratio is strictly increasing when `W > 0`.** -/
theorem ratio_strictMonoOn {m : ℝ} (hm : m ∈ Set.Ioo a b)
    (hWm : 0 < wronskian y₁ y₂ m) :
    StrictMonoOn (ratio y₁ y₂) (Set.Ioo a b) := by
  have hpos : ∀ x ∈ Set.Ioo a b, 0 < wronskian y₁ y₂ x := by
    intro x hx
    have hmJ : m ∈ J := hJ_sub (Set.Ioo_subset_Icc_self hm)
    have hxJ : x ∈ J := hJ_sub (Set.Ioo_subset_Icc_self hx)
    exact ((wronskian_sign_of_ref hJ_open hJ_conn hp hy₁ hy₁' hy₂ hy₂' hW hmJ hxJ).1 hWm)
  have h_deriv_pos : ∀ x ∈ Set.Ioo a b, 0 < wronskian y₁ y₂ x / (y₁ x) ^ 2 := by
    intro x hx
    have hWx_pos : 0 < wronskian y₁ y₂ x := hpos x hx
    have h_y1_sq_pos : 0 < (y₁ x) ^ 2 := sq_pos_iff.mpr (hne x hx)
    exact div_pos hWx_pos h_y1_sq_pos
  have h_interior_eq : interior (Set.Ioo a b) = Set.Ioo a b := interior_Ioo
  have h_deriv_within : ∀ x ∈ interior (Set.Ioo a b),
      HasDerivWithinAt (ratio y₁ y₂) (wronskian y₁ y₂ x / (y₁ x) ^ 2) (interior (Set.Ioo a b)) x := by
    intro x hx
    rw [h_interior_eq] at hx
    have h_hasDerivAt := ratio_hasDerivAt hJ_sub hy₁ hy₂ hne hx
    rw [h_interior_eq]
    exact h_hasDerivAt.hasDerivWithinAt
  have h_deriv_pos_interior : ∀ x ∈ interior (Set.Ioo a b), 0 < wronskian y₁ y₂ x / (y₁ x) ^ 2 := by
    intro x hx
    rw [h_interior_eq] at hx
    exact h_deriv_pos x hx
  have h_continuous_on : ContinuousOn (ratio y₁ y₂) (Set.Ioo a b) := ratio_continuousOn hJ_sub hy₁ hy₂ hne
  exact strictMonoOn_of_hasDerivWithinAt_pos (convex_Ioo a b) h_continuous_on h_deriv_within h_deriv_pos_interior

end ODE
end Analysis
end LeanEval
namespace LeanEval
namespace Analysis
namespace ODE

variable {p q y₁ y₂ : ℝ → ℝ} {a b : ℝ} {J : Set ℝ}
  (hab : a < b)
  (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
  (hJ_sub : Set.Icc a b ⊆ J)
  (hp : ContinuousOn p J) (hq : ContinuousOn q J)
  (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
  (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
  (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
  (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
  (hW : ∃ x₀ ∈ J, y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ ≠ 0)
  (hza : y₁ a = 0) (hzb : y₁ b = 0)
  (hne : ∀ x ∈ Set.Ioo a b, y₁ x ≠ 0)

include hJ_open hJ_conn hJ_sub hp hy₁ hy₁' hy₂ hy₂' hW hne in
/-- **The ratio is strictly decreasing when `W < 0`.** -/
theorem ratio_strictAntiOn {m : ℝ} (hm : m ∈ Set.Ioo a b)
    (hWm : wronskian y₁ y₂ m < 0) :
    StrictAntiOn (ratio y₁ y₂) (Set.Ioo a b) := by
  have h_convex : Convex ℝ (Set.Ioo a b) := convex_Ioo a b
  have h_cont : ContinuousOn (ratio y₁ y₂) (Set.Ioo a b) := by
    exact ratio_continuousOn (hJ_sub := hJ_sub) (hy₁ := hy₁) (hy₂ := hy₂) (hne := hne)
  have h_int_eq : interior (Set.Ioo a b) = Set.Ioo a b := interior_Ioo
  have h_deriv : ∀ x ∈ interior (Set.Ioo a b), HasDerivWithinAt (ratio y₁ y₂)
      (wronskian y₁ y₂ x / (y₁ x) ^ 2) (interior (Set.Ioo a b)) x := by
    intro x hx
    rw [h_int_eq] at hx
    have h_hasDerivAt : HasDerivAt (ratio y₁ y₂) (wronskian y₁ y₂ x / (y₁ x) ^ 2) x :=
      ratio_hasDerivAt (hJ_sub := hJ_sub) (hy₁ := hy₁) (hy₂ := hy₂) (hne := hne) hx
    have hw : HasDerivWithinAt (ratio y₁ y₂) (wronskian y₁ y₂ x / (y₁ x) ^ 2)
        (interior (Set.Ioo a b)) x :=
      h_hasDerivAt.hasDerivWithinAt
    simpa [h_int_eq] using hw
  have h_deriv_neg : ∀ x ∈ interior (Set.Ioo a b), wronskian y₁ y₂ x / (y₁ x) ^ 2 < 0 := by
    intro x hx
    rw [h_int_eq] at hx
    have hmJ : m ∈ J := hJ_sub (Set.Ioo_subset_Icc_self hm)
    have hxJ : x ∈ J := hJ_sub (Set.Ioo_subset_Icc_self hx)
    have hWx : wronskian y₁ y₂ x < 0 :=
      (wronskian_sign_of_ref (hJ_open := hJ_open) (hJ_conn := hJ_conn) (hp := hp)
        (hy₁ := hy₁) (hy₁' := hy₁') (hy₂ := hy₂) (hy₂' := hy₂') (hW := hW) hmJ hxJ).2 hWm
    have hy₁_sq_pos : 0 < (y₁ x) ^ 2 := sq_pos_iff.mpr (hne x hx)
    exact div_neg_of_neg_of_pos hWx hy₁_sq_pos
  exact strictAntiOn_of_hasDerivWithinAt_neg h_convex h_cont h_deriv h_deriv_neg

end ODE
end Analysis
end LeanEval
namespace LeanEval
namespace Analysis
namespace ODE

variable {p q y₁ y₂ : ℝ → ℝ} {a b : ℝ} {J : Set ℝ}
  (hab : a < b)
  (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
  (hJ_sub : Set.Icc a b ⊆ J)
  (hp : ContinuousOn p J) (hq : ContinuousOn q J)
  (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
  (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
  (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
  (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
  (hW : ∃ x₀ ∈ J, y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ ≠ 0)
  (hza : y₁ a = 0) (hzb : y₁ b = 0)
  (hne : ∀ x ∈ Set.Ioo a b, y₁ x ≠ 0)

include hab hJ_open hJ_conn hJ_sub hp hy₁ hy₁' hy₂ hy₂' hW hne in
/-- **The ratio is injective on `(a,b)`.** -/
theorem ratio_injOn :
    Set.InjOn (ratio y₁ y₂) (Set.Ioo a b) := by
  set m := (a + b) / 2 with hm_def
  have hm_lt : a < m := by
    dsimp [m]
    nlinarith
  have hm_gt : m < b := by
    dsimp [m]
    nlinarith
  have hm_ioo : m ∈ Set.Ioo a b := Set.mem_Ioo.mpr ⟨hm_lt, hm_gt⟩
  have hm_icc : m ∈ Set.Icc a b := Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  have hm_J : m ∈ J := hJ_sub hm_icc
  have hW_prod_pos : 0 < wronskian y₁ y₂ m * wronskian y₁ y₂ m :=
    wronskian_mul_pos (hJ_open := hJ_open) (hJ_conn := hJ_conn) (hp := hp)
      (hy₁ := hy₁) (hy₁' := hy₁') (hy₂ := hy₂) (hy₂' := hy₂') (hW := hW)
      (hs := hm_J) (ht := hm_J)
  have hW_ne : wronskian y₁ y₂ m ≠ 0 := by
    intro hzero
    have : wronskian y₁ y₂ m * wronskian y₁ y₂ m = 0 := by
      simp [hzero]
    linarith
  rcases lt_or_gt_of_ne hW_ne with (hW_neg | hW_pos)
  · -- case hW_neg : wronskian y₁ y₂ m < 0
    have h_anti : StrictAntiOn (ratio y₁ y₂) (Set.Ioo a b) :=
      ratio_strictAntiOn (hJ_open := hJ_open) (hJ_conn := hJ_conn) (hJ_sub := hJ_sub)
        (hp := hp) (hy₁ := hy₁) (hy₁' := hy₁') (hy₂ := hy₂) (hy₂' := hy₂') (hW := hW)
        (hne := hne) hm_ioo hW_neg
    exact h_anti.injOn
  · -- case hW_pos : 0 < wronskian y₁ y₂ m
    have h_mono : StrictMonoOn (ratio y₁ y₂) (Set.Ioo a b) :=
      ratio_strictMonoOn (hJ_open := hJ_open) (hJ_conn := hJ_conn) (hJ_sub := hJ_sub)
        (hp := hp) (hy₁ := hy₁) (hy₁' := hy₁') (hy₂ := hy₂) (hy₂' := hy₂') (hW := hW)
        (hne := hne) hm_ioo hW_pos
    exact h_mono.injOn

end ODE
end Analysis
end LeanEval
namespace LeanEval
namespace Analysis
namespace ODE

variable {p q y₁ y₂ : ℝ → ℝ} {a b : ℝ} {J : Set ℝ}
  (hab : a < b)
  (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
  (hJ_sub : Set.Icc a b ⊆ J)
  (hp : ContinuousOn p J) (hq : ContinuousOn q J)
  (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
  (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
  (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
  (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
  (hW : ∃ x₀ ∈ J, y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ ≠ 0)
  (hza : y₁ a = 0) (hzb : y₁ b = 0)
  (hne : ∀ x ∈ Set.Ioo a b, y₁ x ≠ 0)

include hab hJ_sub hy₁ hne in
/-- **`y₁` has constant sign on `(a,b)`.** -/
theorem y1_sign_constant :
    (∀ x ∈ Set.Ioo a b, 0 < y₁ x) ∨ (∀ x ∈ Set.Ioo a b, y₁ x < 0) := by
  have h_cont : ContinuousOn y₁ (Set.Icc a b) := by
    intro x hx
    have hxJ : x ∈ J := hJ_sub hx
    have hdy : HasDerivAt y₁ (deriv y₁ x) x := hy₁ x hxJ
    exact hdy.continuousAt.continuousWithinAt
  exact const_sign_of_nonzero hab h_cont hne

end ODE
end Analysis
end LeanEval
namespace LeanEval
namespace Analysis
namespace ODE

variable {p q y₁ y₂ : ℝ → ℝ} {a b : ℝ} {J : Set ℝ}
  (hab : a < b)
  (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
  (hJ_sub : Set.Icc a b ⊆ J)
  (hp : ContinuousOn p J) (hq : ContinuousOn q J)
  (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
  (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
  (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
  (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
  (hW : ∃ x₀ ∈ J, y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ ≠ 0)
  (hza : y₁ a = 0) (hzb : y₁ b = 0)
  (hne : ∀ x ∈ Set.Ioo a b, y₁ x ≠ 0)

include hab hJ_open hJ_conn hJ_sub hp hy₁ hy₁' hy₂ hy₂' hW hza hzb hne in
/-- **Endpoint derivatives of `y₁` have opposite signs.** `y₁'(a) · y₁'(b) < 0`. -/
theorem y1_deriv_opposite :
    deriv y₁ a * deriv y₁ b < 0 := by
  have haJ : a ∈ J := hJ_sub (Set.mem_Icc.mpr ⟨le_rfl, le_of_lt hab⟩)
  have hbJ : b ∈ J := hJ_sub (Set.mem_Icc.mpr ⟨le_of_lt hab, le_rfl⟩)
  have h_deriv_a : HasDerivAt y₁ (deriv y₁ a) a := hy₁ a haJ
  have h_deriv_b : HasDerivAt y₁ (deriv y₁ b) b := hy₁ b hbJ
  have h_endpoints := endpoints_nonzero hab hJ_open hJ_conn hJ_sub hp hy₁ hy₁' hy₂ hy₂' hW hza hzb
  rcases h_endpoints with ⟨_, _, hLa, hLb⟩
  have hsign := y1_sign_constant hab hJ_sub hy₁ hne
  exact deriv_endpoints_of_signed_interior hab h_deriv_a h_deriv_b hza hzb hLa hLb hsign

end ODE
end Analysis
end LeanEval
namespace LeanEval
namespace Analysis
namespace ODE

variable {p q y₁ y₂ : ℝ → ℝ} {a b : ℝ} {J : Set ℝ}
  (hab : a < b)
  (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
  (hJ_sub : Set.Icc a b ⊆ J)
  (hp : ContinuousOn p J) (hq : ContinuousOn q J)
  (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
  (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
  (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
  (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
  (hW : ∃ x₀ ∈ J, y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ ≠ 0)
  (hza : y₁ a = 0) (hzb : y₁ b = 0)
  (hne : ∀ x ∈ Set.Ioo a b, y₁ x ≠ 0)

include hab hJ_open hJ_conn hJ_sub hp hy₁ hy₁' hy₂ hy₂' hW hza hzb hne in
/-- **`y₂` takes opposite signs at the endpoints.** `y₂ a · y₂ b < 0`. -/
theorem y2_endpoints_opposite :
    y₂ a * y₂ b < 0 := by
  have haJ : a ∈ J := hJ_sub (Set.mem_Icc.mpr ⟨le_rfl, le_of_lt hab⟩)
  have hbJ : b ∈ J := hJ_sub (Set.mem_Icc.mpr ⟨le_of_lt hab, le_rfl⟩)
  have hWpos : 0 < wronskian y₁ y₂ a * wronskian y₁ y₂ b :=
    wronskian_mul_pos hJ_open hJ_conn hp hy₁ hy₁' hy₂ hy₂' hW haJ hbJ
  have hWa : wronskian y₁ y₂ a = -(y₂ a * deriv y₁ a) := wronskian_at_zero hza
  have hWb : wronskian y₁ y₂ b = -(y₂ b * deriv y₁ b) := wronskian_at_zero hzb
  rw [hWa, hWb] at hWpos
  have hderiv_neg : deriv y₁ a * deriv y₁ b < 0 :=
    y1_deriv_opposite hab hJ_open hJ_conn hJ_sub hp hy₁ hy₁' hy₂ hy₂' hW hza hzb hne
  nlinarith

end ODE
end Analysis
end LeanEval
namespace LeanEval
namespace Analysis
namespace ODE

variable {p q y₁ y₂ : ℝ → ℝ} {a b : ℝ} {J : Set ℝ}
  (hab : a < b)
  (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
  (hJ_sub : Set.Icc a b ⊆ J)
  (hp : ContinuousOn p J) (hq : ContinuousOn q J)
  (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
  (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
  (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
  (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
  (hW : ∃ x₀ ∈ J, y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ ≠ 0)
  (hza : y₁ a = 0) (hzb : y₁ b = 0)
  (hne : ∀ x ∈ Set.Ioo a b, y₁ x ≠ 0)

include hab hJ_open hJ_conn hJ_sub hp hy₁ hy₁' hy₂ hy₂' hW hza hzb hne in
/-- **Existence of a zero of `y₂`.** There is `c ∈ (a,b)` with `y₂ c = 0`. -/
theorem y2_zero_exists :
    ∃ c ∈ Set.Ioo a b, y₂ c = 0 := by
  have h_opp : y₂ a * y₂ b < 0 :=
    y2_endpoints_opposite hab hJ_open hJ_conn hJ_sub hp hy₁ hy₁' hy₂ hy₂' hW hza hzb hne
  have hy₂_cont : ContinuousOn y₂ (Set.Icc a b) := by
    intro x hx
    exact (hy₂ x (hJ_sub hx)).continuousAt.continuousWithinAt
  have hab_le : a ≤ b := le_of_lt hab
  by_cases hy2a_neg : y₂ a < 0
  · -- case y₂ a < 0 < y₂ b
    have hy2b_pos : 0 < y₂ b := by
      nlinarith
    have h0_mem : (0 : ℝ) ∈ Set.Ioo (y₂ a) (y₂ b) :=
      Set.mem_Ioo.mpr ⟨hy2a_neg, hy2b_pos⟩
    have h_sub : Set.Ioo (y₂ a) (y₂ b) ⊆ y₂ '' Set.Ioo a b :=
      intermediate_value_Ioo hab_le hy₂_cont
    obtain ⟨c, hc, hc_eq⟩ := h_sub h0_mem
    exact ⟨c, hc, hc_eq⟩
  · -- case y₂ b < 0 < y₂ a
    have hy2a_pos : 0 < y₂ a := by
      have hy2a_ne_zero : y₂ a ≠ 0 := by
        intro hzero
        have : y₂ a * y₂ b = 0 := by simp [hzero]
        nlinarith
      have hge : 0 ≤ y₂ a := not_lt.mp hy2a_neg
      exact lt_of_le_of_ne hge hy2a_ne_zero.symm
    have hy2b_neg : y₂ b < 0 := by
      nlinarith
    have h0_mem : (0 : ℝ) ∈ Set.Ioo (y₂ b) (y₂ a) :=
      Set.mem_Ioo.mpr ⟨hy2b_neg, hy2a_pos⟩
    have h_sub : Set.Ioo (y₂ b) (y₂ a) ⊆ y₂ '' Set.Ioo a b :=
      intermediate_value_Ioo' hab_le hy₂_cont
    obtain ⟨c, hc, hc_eq⟩ := h_sub h0_mem
    exact ⟨c, hc, hc_eq⟩

end ODE
end Analysis
end LeanEval
