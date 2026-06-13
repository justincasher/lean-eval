import Mathlib
import LeanEval.Analysis.ODE.SturmSeparation.WronskianMulExpZero
import LeanEval.Analysis.ODE.SturmSeparation.UIccSubset

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
