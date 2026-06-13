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
