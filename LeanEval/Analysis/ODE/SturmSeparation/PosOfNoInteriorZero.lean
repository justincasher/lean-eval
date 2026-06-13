import Mathlib

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
