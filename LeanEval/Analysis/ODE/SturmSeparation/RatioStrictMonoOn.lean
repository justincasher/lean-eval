import Mathlib
import LeanEval.Analysis.ODE.SturmSeparation.RatioHasDerivAt
import LeanEval.Analysis.ODE.SturmSeparation.RatioContinuousOn
import LeanEval.Analysis.ODE.SturmSeparation.WronskianSignOfRef

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
