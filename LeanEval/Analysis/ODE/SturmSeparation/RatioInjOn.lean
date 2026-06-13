import Mathlib
import LeanEval.Analysis.ODE.SturmSeparation.RatioStrictMonoOn
import LeanEval.Analysis.ODE.SturmSeparation.RatioStrictAntiOn
import LeanEval.Analysis.ODE.SturmSeparation.WronskianMulPos

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
