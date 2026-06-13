import Mathlib
import LeanEval.Analysis.ODE.SturmSeparation.Y2EndpointsOpposite

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
