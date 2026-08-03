import EvalTools.Markers
import LeanEval.Dynamics.FurstenbergTopological.VdW
import LeanEval.Dynamics.FurstenbergTopological.Minimal

/-!
# Approximate multiple recurrence and density of the recurrence sets

Building on van der Waerden's theorem and the minimal-subsystem machinery, this
file proves the *approximate* multiple recurrence statement (by colouring an
orbit with a finite `ε`-net) and then, inside a minimal system, that the
recurrence sets `A_{d,ε}` are open and dense.  A Baire-category argument yields a
single point that is recurrent at every order in the qualitative sense.
-/

namespace LeanEval
namespace Dynamics

open scoped Topology

variable {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]

/-- The recurrence set `A_{d,ε} = {x | ∃ n ≥ 1, ∀ 1 ≤ j ≤ d, dist (T^[j n] x) x < ε}`. -/
def recurrenceSet (T : X → X) (d : ℕ) (ε : ℝ) : Set X :=
  {x | ∃ n : ℕ, 1 ≤ n ∧ ∀ j, 1 ≤ j → j ≤ d → dist (T^[j * n] x) x < ε}

variable (T : X ≃ₜ X)

omit [Nonempty X] in
/-- **Finite `ε`-cover of a compact space.** For every `ε > 0` there is a finite
set of centres whose `ε`-balls cover `X`. -/
theorem finite_eps_cover (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset X, (Set.univ : Set X) ⊆ ⋃ c ∈ s, Metric.ball c ε := by
  have h_univ_compact : IsCompact (Set.univ : Set X) := isCompact_univ
  rcases finite_cover_balls_of_compact h_univ_compact hε with ⟨t, ht_sub, ht_fin, h_cover⟩
  refine ⟨ht_fin.toFinset, ?_⟩
  simpa [ht_fin.coe_toFinset] using h_cover

omit [CompactSpace X] [Nonempty X] in
/-- **Orbit colouring by an `ε`-net.** Given centres whose `ε/2`-balls cover `X`,
each orbit time `i` can be assigned a centre `col i` whose ball contains
`T^[i] z`. -/
theorem orbit_colouring (ε : ℝ) (_hε : 0 < ε) (z : X) (s : Finset X)
    (hs : (Set.univ : Set X) ⊆ ⋃ c ∈ s, Metric.ball c (ε / 2)) :
    ∃ col : ℕ → X, (∀ i, col i ∈ s) ∧
      ∀ i, dist ((T : X → X)^[i] z) (col i) < ε / 2 := by
  have hcover (x : X) : ∃ c ∈ s, x ∈ Metric.ball c (ε / 2) := by
    simpa using hs (Set.mem_univ x)
  have horbit (i : ℕ) : ∃ c : X, c ∈ s ∧ dist ((T : X → X)^[i] z) c < ε / 2 := by
    rcases hcover ((T : X → X)^[i] z) with ⟨c, hcs, hmem⟩
    have hdist : dist ((T : X → X)^[i] z) c < ε / 2 := by
      rwa [Metric.mem_ball] at hmem
    exact ⟨c, hcs, hdist⟩
  choose col hcol using horbit
  refine ⟨col, ?_, ?_⟩
  · intro i
    exact (hcol i).1
  · intro i
    exact (hcol i).2

omit [CompactSpace X] [Nonempty X] in
/-- **A common ball bounds the distance.** Two points in a common `ε/2`-ball are
within `ε` of each other. -/
theorem common_ball_dist {a b c : X} {ε : ℝ}
    (ha : a ∈ Metric.ball c (ε / 2)) (hb : b ∈ Metric.ball c (ε / 2)) :
    dist a b < ε := by
  have ha_dist : dist a c < ε / 2 := Metric.mem_ball.1 ha
  have hb_dist : dist b c < ε / 2 := Metric.mem_ball.1 hb
  have h_tri : dist a b ≤ dist a c + dist b c := by
    have h := dist_triangle a c b
    -- h : dist a b ≤ dist a c + dist c b
    rw [dist_comm c b] at h
    exact h
  calc
    dist a b ≤ dist a c + dist b c := h_tri
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

/-- **Approximate multiple recurrence.** For every `ε > 0` and `d ≥ 1` there are a
point `x` and `n ≥ 1` with `dist (T^[j n] x) x < ε` for all `1 ≤ j ≤ d`. -/
theorem eps_multiple_recurrence (ε : ℝ) (hε : 0 < ε) (d : ℕ) (hd : 1 ≤ d) :
    ∃ (x : X) (n : ℕ), 1 ≤ n ∧
      ∀ j, 1 ≤ j → j ≤ d → dist ((T : X → X)^[j * n] x) x < ε := by
  have hε2 : 0 < ε / 2 := by linarith
  rcases finite_eps_cover (X := X) (ε / 2) hε2 with ⟨s, hs⟩
  have hz : X := by
    have : Nonempty X := by
      exact inferInstance
    exact this.some
  let z := hz
  rcases orbit_colouring T ε hε z s hs with ⟨col, hcol_s, hcol_dist⟩
  let χ : ℕ → s := λ i => ⟨col i, hcol_s i⟩
  have hL : 1 ≤ d + 1 := by omega
  rcases van_der_waerden χ hL with ⟨s0, m, hm, c, h⟩
  set x := (T : X → X)^[s0] z with hx_def
  refine ⟨x, m, hm, ?_⟩
  intro j hj1 hjd
  have hjt : j < d + 1 := by omega
  have hχj : χ (s0 + j * m) = c := h j hjt
  have hcol_j : col (s0 + j * m) = c.val := by
    have := congrArg Subtype.val hχj
    simpa [χ] using this
  have hxj : dist ((T : X → X)^[s0 + j * m] z) (c.val) < ε / 2 := by
    simpa [hcol_j] using hcol_dist (s0 + j * m)
  have hx0 : dist ((T : X → X)^[s0] z) (c.val) < ε / 2 := by
    have hχ0 : χ s0 = c := by
      simpa [zero_mul, add_zero] using h 0 (by omega)
    have hcol0 : col s0 = c.val := by
      have := congrArg Subtype.val hχ0
      simpa [χ] using this
    simpa [hcol0] using hcol_dist s0
  have hx_mem : x ∈ Metric.ball (c.val) (ε / 2) := by
    rw [Metric.mem_ball, hx_def]
    exact hx0
  have hTx_mem : ((T : X → X)^[j * m] x) ∈ Metric.ball (c.val) (ε / 2) := by
    rw [Metric.mem_ball]
    calc
      dist ((T : X → X)^[j * m] x) (c.val)
          = dist ((T : X → X)^[j * m] ((T : X → X)^[s0] z)) (c.val) := rfl
      _ = dist ((T : X → X)^[j * m + s0] z) (c.val) := by
        simp [Function.iterate_add]
      _ = dist ((T : X → X)^[s0 + j * m] z) (c.val) := by
        rw [add_comm (j * m) s0]
      _ < ε / 2 := hxj
  have htemp := common_ball_dist (a := x) (b := ((T : X → X)^[j * m] x)) (c := c.val) hx_mem hTx_mem
  simpa [dist_comm] using htemp

omit [CompactSpace X] [Nonempty X] in
/-- **The recurrence sets are open.** -/
theorem recurrenceSet_open (d : ℕ) (ε : ℝ) :
    IsOpen (recurrenceSet (T : X → X) d ε) := by
  have hT_cont : Continuous (T : X → X) := T.continuous
  have hT_iter_cont (k : ℕ) : Continuous ((T : X → X)^[k]) :=
    hT_cont.iterate k
  -- For each k, the set where dist(T^[k] x, x) < ε is open
  have h_pre (k : ℕ) : IsOpen {x | dist ((T : X → X)^[k] x) x < ε} := by
    have h_cont : Continuous (fun x : X => dist ((T : X → X)^[k] x) x) :=
      continuous_dist.comp ((hT_iter_cont k).prodMk continuous_id)
    simpa [Set.preimage, Set.mem_Iio] using IsOpen.preimage h_cont isOpen_Iio
  -- For fixed n, the set where ∀ j, 1 ≤ j → j ≤ d → dist(T^[j*n] x, x) < ε
  -- is a finite intersection of open sets, hence is open.  Prove by induction on d.
  have h_pre_n (n : ℕ) : IsOpen {x | ∀ j, 1 ≤ j → j ≤ d → dist ((T : X → X)^[j * n] x) x < ε} := by
    induction' d with d ih
    · -- d = 0: vacuously true, set is the whole space
      have : {x | ∀ j, 1 ≤ j → j ≤ 0 → dist ((T : X → X)^[j * n] x) x < ε} = Set.univ := by
        ext x; simp; intro j hj; omega
      rw [this]
      exact isOpen_univ
    · -- d+1 case: the condition splits into j = d+1 and j ≤ d
      have h_eq : {x | ∀ j, 1 ≤ j → j ≤ d.succ → dist ((T : X → X)^[j * n] x) x < ε} =
          {x | ∀ j, 1 ≤ j → j ≤ d → dist ((T : X → X)^[j * n] x) x < ε} ∩
          {x | dist ((T : X → X)^[((d.succ) * n)] x) x < ε} := by
        ext x; constructor
        · intro hx; constructor
          · intro j hj1 hj2; exact hx j hj1 (Nat.le_succ_of_le hj2)
          · exact hx (d.succ) (by omega) (le_refl _)
        · intro ⟨hx, hx_succ⟩ j hj1 hj2
          rcases Nat.eq_or_lt_of_le hj2 with (rfl | hlt)
          · exact hx_succ
          · exact hx j hj1 (Nat.lt_succ_iff.mp hlt)
      rw [h_eq]
      exact IsOpen.inter ih (h_pre (d.succ * n))
  -- Then recurrenceSet is a union over n ≥ 1 of these open sets
  have h_recurrenceSet_eq : recurrenceSet (T : X → X) d ε =
      ⋃ n ∈ {n | 1 ≤ n}, {x | ∀ j, 1 ≤ j → j ≤ d → dist ((T : X → X)^[j * n] x) x < ε} := by
    ext x; simp [recurrenceSet]
  rw [h_recurrenceSet_eq]
  apply isOpen_biUnion
  intro n hn
  exact h_pre_n n

omit [Nonempty X] in
/-- **Orbit preimages cover a minimal system.** In a minimal system every point's
forward orbit meets a given nonempty open set. -/
theorem orbit_preimage_cover (hmin : IsMinimal (T : X → X)) {U : Set X}
    (hU : IsOpen U) (hUne : U.Nonempty) (x : X) :
    ∃ k : ℕ, (T : X → X)^[k] x ∈ U := by
  have hdens : Dense (Set.range (fun k : ℕ => (T : X → X)^[k] x)) :=
    minimal_forward_dense T hmin x
  have h_inter : (U ∩ Set.range (fun k : ℕ => (T : X → X)^[k] x)).Nonempty :=
    hdens.inter_open_nonempty U hU hUne
  rcases h_inter with ⟨y, ⟨hy_U, hy_range⟩⟩
  rcases hy_range with ⟨k, hk⟩
  use k
  have hk' : (T : X → X)^[k] x = y := by simpa using hk
  rw [hk']
  exact hy_U

omit [Nonempty X] in
/-- **Finite cover by orbit preimages.** In a minimal system the preimages
`T^{-k} U` (`k ≤ K`) cover the whole space for some `K`. -/
theorem cover_by_preimages (hmin : IsMinimal (T : X → X)) {U : Set X}
    (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ K : ℕ, ∀ x : X, ∃ k, k ≤ K ∧ (T : X → X)^[k] x ∈ U := by
  set V : ℕ → Set X := λ k => {x | (T : X → X)^[k] x ∈ U} with hV
  have hV_open (k : ℕ) : IsOpen (V k) := by
    dsimp [V]
    have h_cont : Continuous ((T : X → X)^[k]) :=
      T.continuous.iterate k
    exact h_cont.isOpen_preimage _ hU
  have h_cover : Set.univ ⊆ ⋃ k, V k := by
    intro x hx
    rcases orbit_preimage_cover T hmin hU hUne x with ⟨k, hk⟩
    have hxV : x ∈ V k := by
      dsimp [V]
      exact hk
    exact Set.mem_iUnion.mpr ⟨k, hxV⟩
  have h_compact : IsCompact (Set.univ : Set X) := isCompact_univ
  rcases h_compact.elim_finite_subcover V hV_open h_cover with ⟨t : Finset ℕ, ht⟩
  -- ht : Set.univ ⊆ ⋃ i ∈ t, V i
  have h_nonempty : t.Nonempty := by
    rcases hUne with ⟨u, hu⟩
    have hmem : u ∈ ⋃ i ∈ t, V i := ht (Set.mem_univ u)
    rcases (Set.mem_iUnion₂.1 hmem) with ⟨i, hi, hiV⟩
    exact ⟨i, hi⟩
  let K : ℕ := t.max' h_nonempty
  refine ⟨K, ?_⟩
  intro x
  have hmem : x ∈ ⋃ i ∈ t, V i := ht (Set.mem_univ x)
  rcases (Set.mem_iUnion₂.1 hmem) with ⟨i, hi, hiV⟩
  have hi_mem : i ∈ t := hi
  have hi_le : i ≤ K := Finset.le_max' t i hi_mem
  refine ⟨i, hi_le, ?_⟩
  simpa [V] using hiV

/-- **Positive minimum over a finite family of moduli.** A finite family of strictly
positive reals indexed by `{0, …, K}` has a strictly positive lower bound. -/
theorem finite_min_pos (K : ℕ) (δ : ℕ → ℝ) (hδ : ∀ k ≤ K, 0 < δ k) :
    ∃ d : ℝ, 0 < d ∧ ∀ k ≤ K, d ≤ δ k := by
  let s : Finset ℕ := Finset.range (K + 1)
  have hs_nonempty : s.Nonempty := by
    refine ⟨0, ?_⟩
    simp [s]
  let d : ℝ := s.inf' hs_nonempty δ
  refine ⟨d, ?_, ?_⟩
  · rw [Finset.lt_inf'_iff hs_nonempty]
    intro i hi
    rcases Finset.mem_range.1 hi with hi_bound
    have hi_le_K : i ≤ K := by omega
    exact hδ i hi_le_K
  · intro k hk
    have hk_mem : k ∈ s := by
      dsimp [s]
      rw [Finset.mem_range]
      omega
    exact Finset.inf'_le δ hk_mem

omit [Nonempty X] in
/-- **Uniform modulus for finitely many iterates.** On a compact space, for every
`ε > 0` there is `δ > 0` controlling `T^[k]` simultaneously for all `k ≤ K`. -/
theorem uniform_modulus (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a b : X, dist a b < δ →
      ∀ k ≤ K, dist ((T : X → X)^[k] a) ((T : X → X)^[k] b) < ε := by
  have hcont : ∀ k, Continuous ((T : X → X)^[k]) := by
    intro k
    exact T.continuous.iterate k
  have hunif : ∀ k, UniformContinuous ((T : X → X)^[k]) := by
    intro k
    exact CompactSpace.uniformContinuous_of_continuous (hcont k)
  have hδ (k : ℕ) : ∃ δ > 0, ∀ a b : X, dist a b < δ → dist ((T : X → X)^[k] a) ((T : X → X)^[k] b) < ε := by
    rcases (Metric.uniformContinuous_iff.1 (hunif k)) ε hε with ⟨δ, hδpos, hδ⟩
    exact ⟨δ, hδpos, hδ⟩
  induction' K with K ih
  · rcases hδ 0 with ⟨δ, hδpos, hδ⟩
    refine ⟨δ, hδpos, λ a b hdist k hk => ?_⟩
    have hk0 : k = 0 := by omega
    subst hk0
    exact hδ a b hdist
  · rcases ih with ⟨δ_prev, hδpos_prev, hδprev⟩
    rcases hδ (K+1) with ⟨δ_k, hδpos_k, hδk⟩
    set δ := min δ_prev δ_k with hδ_def
    have hδpos' : 0 < δ := lt_min hδpos_prev hδpos_k
    refine ⟨δ, hδpos', λ a b hdist k hk => ?_⟩
    have h_cases : k ≤ K ∨ k = K + 1 := by omega
    rcases h_cases with (hkle | hkeq)
    · apply hδprev a b ?_ k hkle
      have hδ_le : δ ≤ δ_prev := min_le_left δ_prev δ_k
      linarith
    · subst hkeq
      apply hδk a b ?_
      have hδ_le : δ ≤ δ_k := min_le_right δ_prev δ_k
      linarith

/-- **The recurrence sets are dense.** In a minimal system each `A_{d,ε}`
(`d ≥ 1`, `ε > 0`) is dense. -/
theorem recurrenceSet_dense (hmin : IsMinimal (T : X → X)) (d : ℕ) (hd : 1 ≤ d)
    (ε : ℝ) (hε : 0 < ε) : Dense (recurrenceSet (T : X → X) d ε) := by
  rw [dense_iff_inter_open]
  intro U hU hUne
  have hU_nonempty : U.Nonempty := hUne
  rcases cover_by_preimages T hmin hU hU_nonempty with ⟨K, hK⟩
  rcases uniform_modulus T K ε hε with ⟨δ, hδpos, hδ⟩
  rcases eps_multiple_recurrence T δ hδpos d hd with ⟨x, n, hnpos, hx⟩
  rcases hK x with ⟨k, hk_le, hTk_x⟩
  set y := (T : X → X)^[k] x with hy_def
  have hyU : y ∈ U := hTk_x
  have hy_rec : y ∈ recurrenceSet (T : X → X) d ε := by
    dsimp [recurrenceSet]
    refine ⟨n, hnpos, ?_⟩
    intro j hj1 hjd
    have hx_j : dist ((T : X → X)^[j * n] x) x < δ := hx j hj1 hjd
    have h_comm : (T : X → X)^[j * n] ((T : X → X)^[k] x) = (T : X → X)^[k] ((T : X → X)^[j * n] x) := by
      calc
        (T : X → X)^[j * n] ((T : X → X)^[k] x) = (T : X → X)^[j * n + k] x := by
          simp [Function.iterate_add_apply]
        _ = (T : X → X)^[k + j * n] x := by rw [add_comm (j * n) k]
        _ = (T : X → X)^[k] ((T : X → X)^[j * n] x) := by simp [Function.iterate_add_apply]
    calc
      dist ((T : X → X)^[j * n] y) y
          = dist ((T : X → X)^[j * n] ((T : X → X)^[k] x)) ((T : X → X)^[k] x) := rfl
      _ = dist ((T : X → X)^[k] ((T : X → X)^[j * n] x)) ((T : X → X)^[k] x) := by rw [h_comm]
      _ < ε := hδ ((T : X → X)^[j * n] x) x hx_j k hk_le
  have h_inter : (U ∩ recurrenceSet (T : X → X) d ε).Nonempty := by
    refine ⟨y, hyU, hy_rec⟩
  exact h_inter

/-- **A residual point exists.** The countable intersection of the recurrence sets
`A_{d+1, 1/(m+1)}` is dense (hence nonempty) in a minimal system. -/
theorem recurrence_residual_dense (hmin : IsMinimal (T : X → X)) :
    Dense (⋂ d : ℕ, ⋂ m : ℕ, recurrenceSet (T : X → X) (d + 1) (1 / ((m : ℝ) + 1))) := by
  let f : ℕ × ℕ → Set X := λ ⟨d, m⟩ => recurrenceSet (T : X → X) (d + 1) (1 / ((m : ℝ) + 1))
  have h_eq : (⋂ p : ℕ × ℕ, f p) = (⋂ d : ℕ, ⋂ m : ℕ, recurrenceSet (T : X → X) (d + 1) (1 / ((m : ℝ) + 1))) := by
    ext x
    simp [Set.mem_iInter, f]
  rw [← h_eq]
  refine dense_iInter_of_isOpen (ι := ℕ × ℕ) ?_ ?_
  · intro p
    rcases p with ⟨d, m⟩
    exact recurrenceSet_open T (d + 1) (1 / ((m : ℝ) + 1))
  · intro p
    rcases p with ⟨d, m⟩
    have hd1 : 1 ≤ d + 1 := by omega
    have hpos : 0 < 1 / ((m : ℝ) + 1) := by
      have hm_nonneg : (0 : ℝ) ≤ m := by exact mod_cast (Nat.zero_le m)
      have hpos_sum : 0 < (m : ℝ) + 1 := by nlinarith
      exact div_pos (by norm_num) hpos_sum
    exact recurrenceSet_dense T hmin (d + 1) hd1 (1 / ((m : ℝ) + 1)) hpos

/-- **A point recurrent at every order.** In a minimal system there is a point `x`
such that for every `d ≥ 1` and `ε > 0` there is `n ≥ 1` with
`dist (T^[j n] x) x < ε` for all `1 ≤ j ≤ d`. -/
theorem residual_recurrent (hmin : IsMinimal (T : X → X)) :
    ∃ x : X, ∀ d : ℕ, 1 ≤ d → ∀ ε : ℝ, 0 < ε →
      ∃ n : ℕ, 1 ≤ n ∧ ∀ j, 1 ≤ j → j ≤ d → dist ((T : X → X)^[j * n] x) x < ε := by
  have h_dense : Dense (⋂ d : ℕ, ⋂ m : ℕ, recurrenceSet (T : X → X) (d + 1) (1 / ((m : ℝ) + 1))) :=
    recurrence_residual_dense T hmin
  have h_nonempty : Set.Nonempty (⋂ d : ℕ, ⋂ m : ℕ, recurrenceSet (T : X → X) (d + 1) (1 / ((m : ℝ) + 1))) :=
    h_dense.nonempty
  rcases h_nonempty with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  intro d hd ε hε
  have h_exists_m : ∃ m : ℕ, (1 : ℝ) / ((m : ℝ) + 1) < ε := by
    rcases exists_nat_gt (1 / ε) with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have hpos : (0 : ℝ) < (m : ℝ) + 1 := by
      have : (0 : ℕ) ≤ m := Nat.zero_le _
      positivity
    have h_lt_inv : 1 / ε < (m : ℝ) + 1 := by
      linarith
    calc
      (1 : ℝ) / ((m : ℝ) + 1) < (1 : ℝ) / (1 / ε) := by
        exact ((one_div_lt_one_div (by positivity : 0 < (m : ℝ) + 1)
          (by positivity : 0 < 1 / ε)).mpr h_lt_inv)
      _ = ε := by field_simp [ne_of_gt hε]
  rcases h_exists_m with ⟨m, hm⟩
  have hx_m : x ∈ recurrenceSet (T : X → X) (d + 1) (1 / ((m : ℝ) + 1)) := by
    have hx_all : x ∈ (⋂ d : ℕ, ⋂ m : ℕ, recurrenceSet (T : X → X) (d + 1) (1 / ((m : ℝ) + 1))) := hx
    have hx_d : x ∈ (⋂ m : ℕ, recurrenceSet (T : X → X) (d + 1) (1 / ((m : ℝ) + 1))) :=
      (Set.mem_iInter.mp hx_all) d
    exact (Set.mem_iInter.mp hx_d) m
  rcases hx_m with ⟨n, hn1, hn⟩
  refine ⟨n, hn1, ?_⟩
  intro j hj1 hjd
  have hjd_succ : j ≤ d + 1 := by omega
  have h_lt_j : dist ((T : X → X)^[j * n] x) x < (1 : ℝ) / ((m : ℝ) + 1) :=
    hn j hj1 hjd_succ
  linarith

end Dynamics
end LeanEval
