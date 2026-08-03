import Mathlib
import EvalTools.Markers
import LeanEval.Analysis.ODE.CubicDecay.ClosedForm
import LeanEval.Analysis.ODE.CubicDecay.Cube

/-!
Uniqueness of the solution via Grönwall's trajectory comparison: any solution `y` of
`y' = -y³` with `y 0 = 1`, continuous on `[0, ∞)`, equals the closed form `g`. Helper file
for `LeanEval.Analysis.ODE.CubicDecay`.
-/

namespace LeanEval
namespace Analysis
namespace ODE

open Filter Topology

variable {y : ℝ → ℝ}

/-- Continuity of a solution (`lem:solution-continuous`): a solution `y` is continuous on
`[0, ∞)`. -/
theorem solution_continuousOn
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Set.Ici 0) 0) :
    ContinuousOn y (Set.Ici 0) := by
  intro t ht
  rw [Set.mem_Ici] at ht
  rcases eq_or_lt_of_le ht with h | h
  · subst h; exact hy_cont
  · exact (hy_diff t h).continuousAt.continuousWithinAt

/-- Solution as an `Ici` trajectory (`lem:solution-traj`): for `0 < a ≤ t` and `M` bounding
`|y|` on `[0, t]`, on `[a, t]` the solution has derivative `-y(s)³` within `Ici s`, is
continuous on `[a, t]`, and stays in `[-M, M]`. -/
theorem solution_traj
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Set.Ici 0) 0)
    (a t M : ℝ) (ha : 0 < a) (_hat : a ≤ t)
    (hM : ∀ s ∈ Set.Icc (0 : ℝ) t, |y s| ≤ M) :
    (∀ s ∈ Set.Icc a t, HasDerivWithinAt y (-(y s) ^ 3) (Set.Ici s) s) ∧
      ContinuousOn y (Set.Icc a t) ∧
      (∀ s ∈ Set.Icc a t, y s ∈ Set.Icc (-M) M) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    have : 0 < s := lt_of_lt_of_le ha hs.1
    exact (hy_diff s this).hasDerivWithinAt
  · apply (solution_continuousOn hy_diff hy_cont).mono
    intro x hx
    exact Set.mem_Ici.mpr (le_trans ha.le hx.1)
  · intro s hs
    have hmem : s ∈ Set.Icc (0 : ℝ) t := ⟨le_trans ha.le hs.1, hs.2⟩
    rw [Set.mem_Icc]
    exact abs_le.mp (hM s hmem)

/-- Closed form as an `Ici` trajectory (`lem:closed-form-traj`): for `0 < a ≤ t` and `M`
bounding `|g|` on `[0, t]`, on `[a, t]` the closed form has derivative `-g(s)³` within `Ici s`,
is continuous on `[a, t]`, and stays in `[-M, M]`. -/
theorem closedForm_traj
    (a t M : ℝ) (ha : 0 < a) (_hat : a ≤ t)
    (hM : ∀ s ∈ Set.Icc (0 : ℝ) t, |closedForm s| ≤ M) :
    (∀ s ∈ Set.Icc a t, HasDerivWithinAt closedForm (-(closedForm s) ^ 3) (Set.Ici s) s) ∧
      ContinuousOn closedForm (Set.Icc a t) ∧
      (∀ s ∈ Set.Icc a t, closedForm s ∈ Set.Icc (-M) M) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
    exact (closedForm_hasDerivAt s (by linarith)).hasDerivWithinAt
  · apply closedForm_continuousOn.mono
    intro x hx
    exact Set.mem_Ici.mpr (le_trans ha.le hx.1)
  · intro s hs
    have hmem : s ∈ Set.Icc (0 : ℝ) t := ⟨le_trans ha.le hs.1, hs.2⟩
    rw [Set.mem_Icc]
    exact abs_le.mp (hM s hmem)

/-- Grönwall distance bound (`lem:gronwall-bound`): for `t > 0` and `M` bounding `|y|` and
`|g|` on `[0, t]`, every `0 < a ≤ t` satisfies
`|y(t) - g(t)| ≤ |y(a) - g(a)| · exp(3M²(t - a))`. -/
theorem gronwall_bound
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Set.Ici 0) 0)
    (t M : ℝ) (_ht : 0 < t)
    (hMy : ∀ s ∈ Set.Icc (0 : ℝ) t, |y s| ≤ M)
    (hMg : ∀ s ∈ Set.Icc (0 : ℝ) t, |closedForm s| ≤ M)
    (a : ℝ) (ha : 0 < a) (hat : a ≤ t) :
    |y t - closedForm t| ≤ |y a - closedForm a| * Real.exp (3 * M ^ 2 * (t - a)) := by
  -- M must be nonnegative
  have hM0 : 0 ≤ M := by
    have ha_mem : a ∈ Set.Icc (0 : ℝ) t := Set.mem_Icc.mpr ⟨by linarith, hat⟩
    exact le_trans (abs_nonneg (y a)) (hMy a ha_mem)

  -- trajectory data for y and closedForm on [a, t]
  rcases solution_traj hy_diff hy_cont a t M ha hat hMy with ⟨hy_diff', hy_cont', hy_mem⟩
  rcases closedForm_traj a t M ha hat hMg with ⟨hg_diff', hg_cont', hg_mem⟩

  -- Lipschitz condition on the vector field
  have hv : ∀ t' ∈ Set.Ico a t,
      LipschitzOnWith (3 * M.toNNReal ^ 2) (fun (z : ℝ) => -(z ^ 3)) (Set.Icc (-M) M) := by
    intro t' ht'
    exact cube_lipschitzOnWith M hM0

  -- Restrict all Icc-hypotheses to Ico (the Grönwall lemma's time set)
  have hy_diff_Ico : ∀ t' ∈ Set.Ico a t, HasDerivWithinAt y (-(y t') ^ 3) (Set.Ici t') t' := by
    intro t' ht'
    exact hy_diff' t' (Set.Ico_subset_Icc_self ht')

  have hy_mem_Ico : ∀ t' ∈ Set.Ico a t, y t' ∈ Set.Icc (-M) M := by
    intro t' ht'
    exact hy_mem t' (Set.Ico_subset_Icc_self ht')

  have hg_diff_Ico : ∀ t' ∈ Set.Ico a t,
      HasDerivWithinAt closedForm (-(closedForm t') ^ 3) (Set.Ici t') t' := by
    intro t' ht'
    exact hg_diff' t' (Set.Ico_subset_Icc_self ht')

  have hg_mem_Ico : ∀ t' ∈ Set.Ico a t, closedForm t' ∈ Set.Icc (-M) M := by
    intro t' ht'
    exact hg_mem t' (Set.Ico_subset_Icc_self ht')

  have ha_dist : dist (y a) (closedForm a) ≤ |y a - closedForm a| := by
    rw [Real.dist_eq]

  have h_all := dist_le_of_trajectories_ODE_of_mem hv hy_cont' hy_diff_Ico hy_mem_Ico
    hg_cont' hg_diff_Ico hg_mem_Ico ha_dist

  have h_t_mem : t ∈ Set.Icc a t := Set.mem_Icc.mpr ⟨hat, le_refl t⟩
  have h_bound := h_all t h_t_mem

  rw [Real.dist_eq] at h_bound

  simpa [hM0] using h_bound

/-- Uniform bound on a compact interval (`lem:compact-bound`): for a solution `y` and `t ≥ 0`
there is `M ≥ 0` bounding both `|y|` and `|g|` on `[0, t]`. -/
theorem compact_bound
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Set.Ici 0) 0)
    (t : ℝ) (ht : 0 ≤ t) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ s ∈ Set.Icc (0 : ℝ) t, |y s| ≤ M) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) t, |closedForm s| ≤ M) := by
  have h_comp : IsCompact (Set.Icc (0 : ℝ) t) := isCompact_Icc
  have hy_contOn : ContinuousOn y (Set.Icc (0 : ℝ) t) :=
    (solution_continuousOn hy_diff hy_cont).mono Set.Icc_subset_Ici_self
  have hg_contOn : ContinuousOn closedForm (Set.Icc (0 : ℝ) t) :=
    closedForm_continuousOn.mono Set.Icc_subset_Ici_self
  rcases h_comp.exists_bound_of_continuousOn hy_contOn with ⟨Cy, hCy⟩
  rcases h_comp.exists_bound_of_continuousOn hg_contOn with ⟨Cg, hCg⟩
  refine ⟨max Cy Cg, ?_, ?_, ?_⟩
  · have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨le_refl 0, ht⟩
    have h_nonneg_abs : 0 ≤ |y 0| := abs_nonneg _
    have h_norm_le : |y 0| ≤ Cy := by
      have := hCy 0 hzero
      rwa [Real.norm_eq_abs] at this
    have h_nonneg_Cy : 0 ≤ Cy := le_trans h_nonneg_abs h_norm_le
    exact le_trans h_nonneg_Cy (le_max_left _ _)
  · intro s hs
    have h := hCy s hs
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)
  · intro s hs
    have h := hCg s hs
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_right _ _)

/-- A vanishing right limit forces nonpositivity (`lem:limit-forces-nonpos`): if `h → 0`
along `𝓝[>] 0` and `c ≤ h(a)` for all `a ∈ (0, t]`, then `c ≤ 0`. -/
theorem limit_forces_nonpos {h : ℝ → ℝ} {c t : ℝ} (ht : 0 < t)
    (hlim : Tendsto h (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hle : ∀ a ∈ Set.Ioc (0 : ℝ) t, c ≤ h a) : c ≤ 0 := by
  have hmem : Set.Ioo (0 : ℝ) t ∈ 𝓝[>] (0 : ℝ) := by
    have hmem' : Set.Ioo (0 : ℝ) t = Set.Ioo ((-1 : ℝ) : ℝ) t ∩ Set.Ioi (0 : ℝ) := by
      ext x
      constructor
      · intro hx
        have hxpos : 0 < x := Set.mem_Ioo.mp hx |>.left
        refine ⟨Set.mem_Ioo.mpr ⟨by linarith, Set.mem_Ioo.mp hx |>.right⟩, Set.mem_Ioi.mpr hxpos⟩
      · intro hx
        rcases hx with ⟨hx, hx'⟩
        have hxpos : 0 < x := Set.mem_Ioi.mp hx'
        exact Set.mem_Ioo.mpr ⟨hxpos, Set.mem_Ioo.mp hx |>.right⟩
    rw [hmem']
    apply mem_nhdsWithin.mpr
    refine ⟨Set.Ioo ((-1 : ℝ) : ℝ) t, isOpen_Ioo, ?_, ?_⟩
    · exact Set.mem_Ioo.mpr ⟨by norm_num, ht⟩
    · intro y hy
      exact hy
  have h_evenually : ∀ᶠ a in 𝓝[>] (0 : ℝ), c ≤ h a := by
    filter_upwards [hmem] with a ha
    have ha' : a ∈ Set.Ioc (0 : ℝ) t := by
      rcases Set.mem_Ioo.mp ha with ⟨ha_left, ha_right⟩
      exact Set.mem_Ioc.mpr ⟨ha_left, ha_right.le⟩
    exact hle a ha'
  exact ge_of_tendsto hlim h_evenually

/-- The Grönwall bound vanishes at `0⁺` (`lem:gronwall-rhs-tendsto`): the map
`a ↦ |y(a) - g(a)| · exp(3M²(t - a))` tends to `0` along `𝓝[>] 0`. -/
theorem gronwall_rhs_tendsto
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Set.Ici 0) 0)
    (hy0 : y 0 = 1) (t M : ℝ) (_ht : 0 < t) :
    Tendsto (fun a : ℝ => |y a - closedForm a| * Real.exp (3 * M ^ 2 * (t - a)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hy_tendsto : Tendsto y (𝓝[>] 0) (𝓝 (y 0)) := by
    have hcont : ContinuousWithinAt y (Set.Ici 0) 0 :=
      (solution_continuousOn hy_diff hy_cont).continuousWithinAt (Set.mem_Ici.mpr (le_refl 0))
    exact hcont.tendsto.mono_left (nhdsWithin_mono 0 Set.Ioi_subset_Ici_self)
  have hg_tendsto : Tendsto closedForm (𝓝[>] 0) (𝓝 (closedForm 0)) := by
    have hcont : ContinuousWithinAt closedForm (Set.Ici 0) 0 :=
      closedForm_continuousOn.continuousWithinAt (Set.mem_Ici.mpr (le_refl 0))
    exact hcont.tendsto.mono_left (nhdsWithin_mono 0 Set.Ioi_subset_Ici_self)
  have h_sub_tendsto : Tendsto (fun a : ℝ => y a - closedForm a) (𝓝[>] 0)
      (𝓝 (y 0 - closedForm 0)) :=
    hy_tendsto.sub hg_tendsto
  have h_sub_zero : y 0 - closedForm 0 = 0 := by
    rw [hy0, closedForm_zero, sub_self]
  have h_abs_tendsto : Tendsto (fun a : ℝ => |y a - closedForm a|) (𝓝[>] 0) (𝓝 0) := by
    simpa [h_sub_zero] using h_sub_tendsto.abs
  have h_id_tendsto : Tendsto (fun a : ℝ => a) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    continuousAt_id.tendsto.mono_left (by
      simpa using (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi 0)))
  have h_t_minus_a_tendsto : Tendsto (fun a : ℝ => t - a) (𝓝[>] (0 : ℝ)) (𝓝 t) := by
    simpa using (tendsto_const_nhds.sub h_id_tendsto)
  have h_inner_tendsto : Tendsto (fun a : ℝ => 3 * M ^ 2 * (t - a)) (𝓝[>] (0 : ℝ))
      (𝓝 (3 * M ^ 2 * t)) := by
    have : (fun a : ℝ => 3 * M ^ 2 * (t - a)) = (fun a : ℝ => (3 * M ^ 2) * (t - a)) := by
      ext a; ring
    rw [this]
    exact (tendsto_const_nhds.mul h_t_minus_a_tendsto)
  have h_exp_tendsto : Tendsto (fun a : ℝ => Real.exp (3 * M ^ 2 * (t - a))) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.exp (3 * M ^ 2 * t))) :=
    ((Real.continuous_exp.tendsto (3 * M ^ 2 * t)).comp h_inner_tendsto)
  have h_mul : Tendsto (fun a : ℝ => |y a - closedForm a| * Real.exp (3 * M ^ 2 * (t - a)))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 * Real.exp (3 * M ^ 2 * t))) :=
    h_abs_tendsto.mul h_exp_tendsto
  simpa [zero_mul] using h_mul

/-- Uniqueness (`lem:uniqueness`): any solution `y` equals the closed form on `[0, ∞)`. -/
theorem uniqueness
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Set.Ici 0) 0)
    (hy0 : y 0 = 1) :
    ∀ t : ℝ, 0 ≤ t → y t = closedForm t := by
  intro t ht
  rcases eq_or_lt_of_le ht with h | ht0
  · -- case h : 0 = t
    rw [← h, hy0, closedForm_zero]
  · -- case ht0 : 0 < t
    have ht_nonneg : 0 ≤ t := by linarith
    obtain ⟨M, hM0, hMy, hMg⟩ := compact_bound hy_diff hy_cont t ht_nonneg
    have key : ∀ a ∈ Set.Ioc (0 : ℝ) t, |y t - closedForm t| ≤ |y a - closedForm a| * Real.exp (3 * M ^ 2 * (t - a)) := by
      intro a ha
      exact gronwall_bound hy_diff hy_cont t M ht0 hMy hMg a ha.1 ha.2
    have hnp : |y t - closedForm t| ≤ 0 :=
      limit_forces_nonpos ht0 (gronwall_rhs_tendsto hy_diff hy_cont hy0 t M ht0) key
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hnp (abs_nonneg _)))

end ODE
end Analysis
end LeanEval
