import Mathlib
import EvalTools.Markers

/-!
# From qualitative recurrence to a return-time sequence

These lemmas upgrade the qualitative recurrence statement (for every `ε > 0`
there is a return time `n ≥ 1` with all `T^[j n] x` within `ε` of `x`) into a
genuine convergent return-time sequence `T^[j n_k] x → x`, handling both the case
of arbitrarily large small returns (subsequence extraction) and the bounded case
(which forces a periodic point).
-/

namespace LeanEval
namespace Dynamics

open scoped Topology

variable {X : Type*} [MetricSpace X] (T : X ≃ₜ X)

/-- **Subsequence extraction from frequent small returns.** If small return gaps
occur at arbitrarily large times, there is a strictly increasing `n_k` with
`T^[j n_k] x → x` for every `1 ≤ j ≤ d`. -/
theorem recurrence_subseq (x : X) (d : ℕ)
    (h : ∀ N : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ n, N < n ∧ ∀ j, 1 ≤ j → j ≤ d → dist ((T : X → X)^[j * n] x) x < ε) :
    ∃ n : ℕ → ℕ, StrictMono n ∧
      ∀ j, 1 ≤ j → j ≤ d →
        Filter.Tendsto (fun k => (T : X → X)^[j * n k] x) Filter.atTop (𝓝 x) := by
  have hpos : ∀ k : ℕ, 0 < (1 : ℝ) / ((k : ℝ) + 1) := by
    intro k
    refine div_pos (by norm_num) (by positivity)
  have hpos_alt : ∀ k : ℕ, 0 < (1 : ℝ) / ((k : ℝ) + 2) := by
    intro k
    refine div_pos (by norm_num) (by positivity)

  -- define the subsequence n : ℕ → ℕ recursively
  let n : ℕ → ℕ := Nat.rec
    (Classical.choose (h 0 (1 : ℝ) (by norm_num)))
    (fun k nk => Classical.choose (h nk ((1 : ℝ) / ((k : ℝ) + 2)) (hpos_alt k)))

  -- prove n k < n (k+1)
  have hn_lt_succ : ∀ k, n k < n (k+1) := by
    intro k
    dsimp [n]
    have hk := h (n k) ((1 : ℝ) / ((k : ℝ) + 2)) (hpos_alt k)
    have hk_spec := Classical.choose_spec hk
    exact hk_spec.1

  -- hence StrictMono
  have hmono : StrictMono n :=
    strictMono_nat_of_lt_succ hn_lt_succ

  -- prove the distance bound: dist(T^[j * n k] x, x) < 1 / (k+1)
  have hbound : ∀ (k j : ℕ), 1 ≤ j → j ≤ d → dist ((T : X → X)^[j * n k] x) x < (1 : ℝ) / ((k : ℝ) + 1) := by
    intro k
    induction' k with k ih
    · -- base case k = 0
      intro j hj1 hjd
      have h0_spec := Classical.choose_spec (h 0 (1 : ℝ) (by norm_num))
      simpa [show (1 : ℝ) / ((0 : ℕ).cast + 1) = (1 : ℝ) by norm_num] using h0_spec.2 j hj1 hjd
    · -- step: k.succ
      intro j hj1 hjd
      have hk_spec := Classical.choose_spec (h (n k) ((1 : ℝ) / ((k : ℝ) + 2)) (hpos_alt k))
      have hk_res : dist ((T : X → X)^[j * n (k+1)] x) x < (1 : ℝ) / ((k : ℝ) + 2) :=
        hk_spec.2 j hj1 hjd
      have h_eq : (1 : ℝ) / ((k : ℝ) + 2) = (1 : ℝ) / (((k+1 : ℕ) : ℝ) + 1) := by
        push_cast; ring
      simpa [h_eq] using hk_res

  refine ⟨n, hmono, ?_⟩
  intro j hj1 hjd
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hK : ∃ K : ℕ, (1 : ℝ) / ((K : ℝ) + 1) < ε := by
    have h_arch : ∃ K : ℕ, (1 / ε : ℝ) < (K : ℝ) := exists_nat_gt (1 / ε)
    rcases h_arch with ⟨K, hK⟩
    use K
    have hpos_eps : 0 < ε := hε
    have hpos_denom : 0 < (K : ℝ) + 1 := by
      nlinarith [show (0 : ℝ) ≤ K from Nat.cast_nonneg _]
    have hpos_one_div_eps : 0 < 1 / ε := div_pos (by norm_num) hpos_eps
    have h_ineq : (1 : ℝ) / ε < (K : ℝ) + 1 := by
      linarith
    calc
      (1 : ℝ) / ((K : ℝ) + 1) < (1 : ℝ) / (1 / ε) :=
        (one_div_lt_one_div hpos_denom hpos_one_div_eps).mpr h_ineq
      _ = ε := by field_simp [hε.ne']
  rcases hK with ⟨K, hK⟩
  refine Filter.eventually_atTop.mpr ⟨K, ?_⟩
  intro k hk
  have h_dist : dist ((T : X → X)^[j * n k] x) x < (1 : ℝ) / ((k : ℝ) + 1) :=
    hbound k j hj1 hjd
  have h_eps : (1 : ℝ) / ((k : ℝ) + 1) < ε := by
    have hk_ge_add : (K : ℕ).succ ≤ k.succ := Nat.succ_le_succ hk
    have hpos_k : 0 < (k : ℝ) + 1 := by positivity
    have hpos_K : 0 < (K : ℝ) + 1 := by positivity
    calc
      (1 : ℝ) / ((k : ℝ) + 1) ≤ (1 : ℝ) / ((K : ℝ) + 1) :=
        (one_div_le_one_div hpos_k hpos_K).mpr (by exact_mod_cast hk_ge_add)
      _ < ε := hK
  linarith

/-- **A return time recurs across all scales.** If the qualitative hypothesis holds
but small returns are not arbitrarily large, some fixed `n* ∈ {1, …, N₀}` has gap
below `1/m` for infinitely many `m`. -/
theorem pigeonhole_fixed_return (x : X) (d : ℕ)
    (h1 : ∀ ε : ℝ, 0 < ε →
      ∃ n, 1 ≤ n ∧ ∀ j, 1 ≤ j → j ≤ d → dist ((T : X → X)^[j * n] x) x < ε)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (N₀ : ℕ)
    (h2 : ∀ n, N₀ < n →
      ¬ (∀ j, 1 ≤ j → j ≤ d → dist ((T : X → X)^[j * n] x) x < ε₀)) :
    ∃ nstar : ℕ, 1 ≤ nstar ∧ nstar ≤ N₀ ∧
      {m : ℕ | ∀ j, 1 ≤ j → j ≤ d →
        dist ((T : X → X)^[j * nstar] x) x < 1 / (m : ℝ)}.Infinite := by
  have h_choice : ∀ m : ℕ, ∃ n : ℕ, 1 ≤ n ∧ n ≤ N₀ ∧
      ∀ j, 1 ≤ j → j ≤ d → dist ((T : X → X)^[j * n] x) x < 1 / ((m+1 : ℝ)) := by
    intro m
    let ε := min ε₀ (1 / ((m+1 : ℝ)))
    have hεpos : 0 < ε := by
      refine lt_min_iff.mpr ⟨hε₀, ?_⟩
      have hpos : 0 < (m+1 : ℝ) := by exact mod_cast (Nat.succ_pos m)
      positivity
    rcases h1 ε hεpos with ⟨n, hn1, hn⟩
    have hnle : n ≤ N₀ := by
      by_contra! h
      have hNlt : N₀ < n := by omega
      rcases h2 n hNlt with h2n
      apply h2n
      intro j hj1 hj2
      have hdist := hn j hj1 hj2
      have hle : ε ≤ ε₀ := min_le_left _ _
      linarith
    refine ⟨n, hn1, hnle, ?_⟩
    intro j hj1 hj2
    have hdist := hn j hj1 hj2
    have hle : ε ≤ 1 / ((m+1 : ℝ)) := min_le_right _ _
    linarith
  choose n_m hn_m1 hn_m_le hn_m_dist using h_choice
  let f : ℕ → Fin (N₀.succ) := fun m => ⟨n_m m, by
    have := hn_m_le m
    omega⟩
  have h_finite : Finite (Fin (N₀.succ)) := inferInstance
  have h_infinite : Infinite ℕ := inferInstance
  rcases Finite.exists_infinite_fiber f with ⟨y, hy⟩
  have hy_val_le_N0 : y.val ≤ N₀ := by
    have h_lt : y.val < N₀.succ := y.2
    omega
  refine ⟨y.val, ?_, hy_val_le_N0, ?_⟩
  · -- 1 ≤ y.val
    have h_nonempty : (f⁻¹' {y}).Nonempty := by
      have : (f⁻¹' {y}).Infinite := (Set.infinite_coe_iff.mp hy)
      exact this.nonempty
    rcases h_nonempty with ⟨m, hm⟩
    have h_eq : n_m m = y.val := by
      have h_fm_eq_y : f m = y := by simpa using hm
      have h_val : (f m).val = y.val := Fin.ext_iff.mp h_fm_eq_y
      simpa [f] using h_val
    rw [← h_eq]
    exact hn_m1 m
  · -- {m | ...}.Infinite
    have h_pre_set_infinite : (f⁻¹' {y}).Infinite := Set.infinite_coe_iff.mp hy
    have h_subset : f⁻¹' {y} \ ({0} : Set ℕ) ⊆
        {m | ∀ j, 1 ≤ j → j ≤ d → dist ((T : X → X)^[j * y.val] x) x < 1 / (m : ℝ)} := by
      intro m hm
      rcases hm with ⟨hm_pre, hm_not0⟩
      have hm_pos : 0 < m := Nat.pos_of_ne_zero hm_not0
      have h_eq : n_m m = y.val := by
        have h_fm_eq_y : f m = y := by simpa using hm_pre
        have h_val : (f m).val = y.val := Fin.ext_iff.mp h_fm_eq_y
        simpa [f] using h_val
      intro j hj1 hj2
      have h_dist' : dist ((T : X → X)^[j * y.val] x) x < 1 / ((m+1 : ℝ)) := by
        simpa [h_eq] using hn_m_dist m j hj1 hj2
      have hm_pos' : 0 < (m : ℝ) := by exact_mod_cast hm_pos
      have hm_succ_pos' : 0 < (m : ℝ) + 1 := by nlinarith
      have h_div_lt : 1 / ((m : ℝ) + 1) < 1 / (m : ℝ) :=
        ((one_div_lt_one_div hm_succ_pos' hm_pos').mpr (by
          nlinarith))
      linarith
    have h_fin_singleton : ({0} : Set ℕ).Finite := Set.finite_singleton 0
    have h_pre' : (f⁻¹' {y} \ ({0} : Set ℕ)).Infinite := by
      intro hfin
      apply h_pre_set_infinite
      have h_eq : f⁻¹' {y} = (f⁻¹' {y} \ ({0} : Set ℕ)) ∪ (f⁻¹' {y} ∩ ({0} : Set ℕ)) := by
        ext m; simp
      rw [h_eq]
      apply Set.Finite.union hfin
      have h_inter_subset : (f⁻¹' {y} ∩ ({0} : Set ℕ)) ⊆ ({0} : Set ℕ) := by
        intro x hx; exact hx.2
      exact Set.Finite.subset h_fin_singleton h_inter_subset
    exact Set.Infinite.mono h_subset h_pre'

/-- **A gap below every scale is zero.** A nonnegative real that is below `1/m` for
infinitely many `m` is zero. -/
theorem small_inf_implies_zero {a : ℝ} (ha : 0 ≤ a)
    (h : {m : ℕ | a < 1 / (m : ℝ)}.Infinite) : a = 0 := by
  set S := {m : ℕ | a < 1 / (m : ℝ)} with hS
  have hS_infinite : S.Infinite := h
  by_cases ha_pos : a > 0
  · rcases exists_nat_gt (1 / a) with ⟨N, hN⟩
    have hS_subset : S ⊆ {m : ℕ | m < N} := by
      intro m hm
      have hineq : a < 1 / (m : ℝ) := hm
      by_cases hm_zero : m = 0
      · exfalso
        subst hm_zero
        norm_num at hineq
        nlinarith
      · have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hm_zero)
        have hmul : a * (m : ℝ) < 1 := by
          calc
            a * (m : ℝ) < (1 / (m : ℝ)) * (m : ℝ) := by nlinarith
            _ = 1 := by field_simp [hm_pos.ne.symm]
        have h_m_lt_one_div_a : (m : ℝ) < 1 / a := by
          have ha_ne : a ≠ 0 := by linarith
          field_simp [ha_ne]
          nlinarith
        have h_m_lt_N : (m : ℝ) < (N : ℝ) := by nlinarith
        exact_mod_cast h_m_lt_N
    have hS_finite : S.Finite := Set.Finite.subset (Set.finite_lt_nat N) hS_subset
    exact absurd hS_finite hS_infinite
  · have ha_nonpos : a ≤ 0 := by linarith
    exact le_antisymm ha_nonpos ha

/-- **Bounded return times force a periodic point.** Under the qualitative
hypothesis, if small returns are not arbitrarily large then there is `n* ≥ 1`
with `T^[j n*] x = x` for all `1 ≤ j ≤ d`. -/
theorem recurrence_periodic (x : X) (d : ℕ)
    (h1 : ∀ ε : ℝ, 0 < ε →
      ∃ n, 1 ≤ n ∧ ∀ j, 1 ≤ j → j ≤ d → dist ((T : X → X)^[j * n] x) x < ε)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (N₀ : ℕ)
    (h2 : ∀ n, N₀ < n →
      ¬ (∀ j, 1 ≤ j → j ≤ d → dist ((T : X → X)^[j * n] x) x < ε₀)) :
    ∃ nstar : ℕ, 1 ≤ nstar ∧ ∀ j, 1 ≤ j → j ≤ d → (T : X → X)^[j * nstar] x = x := by
  -- Pigeonhole lemma gives nstar with infinite return times at scale 1/m
  have hp := pigeonhole_fixed_return T x d h1 ε₀ hε₀ N₀ h2
  rcases hp with ⟨nstar, hnstar1, hnstar2, hinf⟩
  refine ⟨nstar, hnstar1, λ j hj1 hj2 => ?_⟩
  -- For this j, the distance a = dist (T^[j*nstar] x) x is nonnegative
  have ha_nonneg : 0 ≤ dist ((T : X → X)^[j * nstar] x) x := dist_nonneg
  -- The set of m where the condition holds for all j (from hinf) is contained in
  -- the set where it holds for this particular j, so the latter is also infinite
  have h_sub : {m : ℕ | ∀ j', 1 ≤ j' → j' ≤ d → dist ((T : X → X)^[j' * nstar] x) x < 1 / (m : ℝ)}
    ⊆ {m : ℕ | dist ((T : X → X)^[j * nstar] x) x < 1 / (m : ℝ)} := by
    intro m hm; exact hm j hj1 hj2
  have hS_infinite : {m : ℕ | dist ((T : X → X)^[j * nstar] x) x < 1 / (m : ℝ)}.Infinite :=
    Set.Infinite.mono h_sub hinf
  -- A nonnegative real less than 1/m for infinitely many m must be zero
  have ha_eq_zero : dist ((T : X → X)^[j * nstar] x) x = 0 :=
    small_inf_implies_zero ha_nonneg hS_infinite
  -- Distance zero implies equality in a metric space
  exact (dist_eq_zero).mp ha_eq_zero

/-- **Qualitative recurrence yields a recurrence sequence.** Under the qualitative
hypothesis there is a strictly increasing `n_k` with `T^[j n_k] x → x` for every
`1 ≤ j ≤ d`. -/
theorem recurrence_sequential (x : X) (d : ℕ) (hd : 1 ≤ d)
    (h : ∀ ε : ℝ, 0 < ε →
      ∃ n, 1 ≤ n ∧ ∀ j, 1 ≤ j → j ≤ d → dist ((T : X → X)^[j * n] x) x < ε) :
    ∃ n : ℕ → ℕ, StrictMono n ∧
      ∀ j, 1 ≤ j → j ≤ d →
        Filter.Tendsto (fun k => (T : X → X)^[j * n k] x) Filter.atTop (𝓝 x) := by
  by_cases h_arb : ∀ N : ℕ, ∀ ε : ℝ, 0 < ε → ∃ n, N < n ∧ ∀ j, 1 ≤ j → j ≤ d → dist ((T : X → X)^[j * n] x) x < ε
  · rcases recurrence_subseq (x := x) (d := d) (h := h_arb) with ⟨n, hn_mono, hn⟩
    exact ⟨n, hn_mono, hn⟩
  · push_neg at h_arb
    rcases h_arb with ⟨N₀, ε₀, hε₀, h2⟩
    have h2' : ∀ n, N₀ < n → ¬ (∀ j, 1 ≤ j → j ≤ d → dist ((T : X → X)^[j * n] x) x < ε₀) := by
      intro n hn h_all
      rcases h2 n hn with ⟨j, hj1, hjd, hge⟩
      have hlt := h_all j hj1 hjd
      linarith
    rcases recurrence_periodic (x := x) (d := d) (h1 := h) (ε₀ := ε₀) (hε₀ := hε₀) (N₀ := N₀) (h2 := h2') with ⟨nstar, hnstar_ge1, hnstar_eq⟩
    let n : ℕ → ℕ := fun k => (k + 1) * nstar
    have hn_mono : StrictMono n := by
      intro a b h
      have hpos : 0 < nstar := by omega
      have : (a + 1) * nstar < (b + 1) * nstar :=
        Nat.mul_lt_mul_of_pos_right (by omega) hpos
      exact this
    have h_tendsto : ∀ j, 1 ≤ j → j ≤ d →
      Filter.Tendsto (fun k : ℕ => (T : X → X)^[j * n k] x) Filter.atTop (𝓝 x) := by
      intro j hj1 hjd
      have h_eq : ∀ k : ℕ, (T : X → X)^[j * n k] x = x := by
        intro k
        calc
          (T : X → X)^[j * n k] x = (T : X → X)^[j * ((k + 1) * nstar)] x := rfl
          _ = (T : X → X)^[(j * nstar) * (k + 1)] x := by
            have : j * ((k + 1) * nstar) = (j * nstar) * (k + 1) := by
              simp [mul_assoc, mul_comm, mul_left_comm]
            rw [this]
          _ = ((T : X → X)^[j * nstar])^[k + 1] x := by
            simpa using congrArg (· x) (Function.iterate_mul (j * nstar) (k + 1) (f := (T : X → X)))
          _ = x := Function.iterate_fixed (hnstar_eq j hj1 hjd) (k + 1)
      have h_const : (fun k : ℕ => (T : X → X)^[j * n k] x) = fun _ => x := by
        ext k; exact h_eq k
      rw [h_const]
      exact tendsto_const_nhds
    exact ⟨n, hn_mono, h_tendsto⟩

end Dynamics
end LeanEval
