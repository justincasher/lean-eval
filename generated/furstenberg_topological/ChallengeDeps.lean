import Mathlib

/-!
# Combinatorial core: van der Waerden via Hales–Jewett

This file contains the combinatorial input to the Furstenberg–Weiss topological
multiple recurrence theorem: van der Waerden's theorem on monochromatic
arithmetic progressions, obtained from the Hales–Jewett theorem
(`Combinatorics.Line.exists_mono_in_high_dimension`) already in Mathlib.

The Hales–Jewett theorem itself is used directly from Mathlib and is therefore
not restated here.
-/

namespace LeanEval
namespace Dynamics

open Combinatorics

/-- **Line-sum identity.** Let `l` be a combinatorial line in `(Fin L) ^ ι` over
the alphabet `Fin L`. For every `t : Fin L`, the coordinate sum of the `t`-th
point `l t` splits into a constant part coming from the fixed coordinates
(`idxFun i ≠ none`) plus `|I| · t`, where `I = {i | idxFun i = none}` is the set
of moving coordinates. -/
theorem line_sum_identity {L : ℕ} {ι : Type*} [Fintype ι] [DecidableEq (Option (Fin L))]
    (l : Line (Fin L) ι) (t : Fin L) :
    (∑ i, ((l t i : ℕ)))
      = (∑ i ∈ Finset.univ.filter (fun i => l.idxFun i ≠ none),
            (((l.idxFun i).getD t : Fin L) : ℕ))
        + (Finset.univ.filter (fun i => l.idxFun i = none)).card * (t : ℕ) := by
  classical
    let S_none := Finset.univ.filter (fun i => l.idxFun i = none)
    have h_sum_none : (∑ i ∈ S_none, ((l t i : ℕ))) = S_none.card * (t : ℕ) := by
      calc
        (∑ i ∈ S_none, ((l t i : ℕ))) = (∑ i ∈ S_none, ((t : ℕ))) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have hi_none : l.idxFun i = none := by
            simpa [S_none, Finset.mem_filter] using hi
          rw [l.apply_none t i hi_none]
        _ = S_none.card * (t : ℕ) := by
          apply Finset.sum_const_nat (fun i hi => rfl)
    have h_eq_total : (∑ i, ((l t i : ℕ))) =
        (∑ i ∈ Finset.univ.filter (fun i => l.idxFun i ≠ none), ((l t i : ℕ)))
        + S_none.card * (t : ℕ) := by
      calc
        (∑ i, ((l t i : ℕ))) = (∑ i ∈ S_none, ((l t i : ℕ))) + (∑ i ∈ S_noneᶜ, ((l t i : ℕ))) := by
          symm; exact Finset.sum_add_sum_compl S_none (fun i => ((l t i : ℕ)))
        _ = S_none.card * (t : ℕ) + (∑ i ∈ S_noneᶜ, ((l t i : ℕ))) := by rw [h_sum_none]
        _ = (∑ i ∈ S_noneᶜ, ((l t i : ℕ))) + S_none.card * (t : ℕ) := by rw [add_comm]
        _ = (∑ i ∈ Finset.univ.filter (fun i => l.idxFun i ≠ none), ((l t i : ℕ)))
            + S_none.card * (t : ℕ) := by
          have : S_noneᶜ = Finset.univ.filter (fun i => l.idxFun i ≠ none) := by
            ext i; simp [S_none]
          rw [this]
    have h_some_sum_eq :
        (∑ i ∈ Finset.univ.filter (fun i => l.idxFun i ≠ none), ((l t i : ℕ))) =
        (∑ i ∈ Finset.univ.filter (fun i => l.idxFun i ≠ none),
          (((l.idxFun i).getD t : Fin L) : ℕ)) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [l.apply_def]
    calc
      (∑ i, ((l t i : ℕ))) = (∑ i ∈ Finset.univ.filter (fun i => l.idxFun i ≠ none), ((l t i : ℕ)))
          + S_none.card * (t : ℕ) := h_eq_total
      _ = (∑ i ∈ Finset.univ.filter (fun i => l.idxFun i ≠ none),
            (((l.idxFun i).getD t : Fin L) : ℕ))
          + S_none.card * (t : ℕ) := by rw [h_some_sum_eq]
      _ = (∑ i ∈ Finset.univ.filter (fun i => l.idxFun i ≠ none),
            (((l.idxFun i).getD t : Fin L) : ℕ))
          + (Finset.univ.filter (fun i => l.idxFun i = none)).card * (t : ℕ) := by
        simp [S_none]

/-- **From a combinatorial line to an arithmetic progression.** Fix `L ≥ 1` and a
colouring `χ : ℕ → κ`. Colour the hypercube `ι → Fin L` by `v ↦ χ (∑ i, v i)`. A
monochromatic line of this colouring yields a `χ`-monochromatic arithmetic
progression `s, s + m, …, s + (L-1) m` of length `L` with common difference
`m ≥ 1`. -/
theorem line_to_progression {L : ℕ} (hL : 1 ≤ L) {κ : Type*} (χ : ℕ → κ)
    {ι : Type*} [Fintype ι] (l : Line (Fin L) ι)
    (hl : l.IsMono (fun v : ι → Fin L => χ (∑ i, (v i : ℕ)))) :
    ∃ s m : ℕ, 1 ≤ m ∧ ∃ c : κ, ∀ t : ℕ, t < L → χ (s + t * m) = c := by
  have h0L : 0 < L := by omega
  let h0 : Fin L := ⟨0, h0L⟩
  -- I = set of moving coordinates (where idxFun i = none)
  let I : Finset ι := Finset.univ.filter (fun i => l.idxFun i = none)
  have hI_nonempty : I.Nonempty := by
    rcases l.proper with ⟨i, hi⟩
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  have hm : 1 ≤ I.card := by
    have hpos : 0 < I.card := (Finset.card_pos.mpr hI_nonempty)
    omega
  -- J = set of fixed coordinates (where idxFun i ≠ none)
  let J : Finset ι := Finset.univ.filter (fun i => l.idxFun i ≠ none)
  -- constant colour c and the fixed sum s = sum of coordinates at h0
  rcases hl with ⟨c, hc⟩
  let s : ℕ := ∑ i, ((l h0 i : ℕ))
  refine ⟨s, I.card, hm, c, λ t ht => ?_⟩
  let t' : Fin L := ⟨t, ht⟩
  -- line_sum_identity at t' and at h0
  have h_id_t' : (∑ i, ((l t' i : ℕ))) =
      (∑ i ∈ J, (((l.idxFun i).getD t' : Fin L) : ℕ)) + I.card * (t' : ℕ) := by
    simpa [I, J] using line_sum_identity l t'
  have h_id_0 : (∑ i, ((l h0 i : ℕ))) =
      (∑ i ∈ J, (((l.idxFun i).getD h0 : Fin L) : ℕ)) + I.card * (h0 : ℕ) := by
    simpa [I, J] using line_sum_identity l h0
  -- the sum over fixed coordinates J is the same for t' and h0
  have h_fixed_sum_eq : (∑ i ∈ J, (((l.idxFun i).getD t' : Fin L) : ℕ))
      = (∑ i ∈ J, (((l.idxFun i).getD h0 : Fin L) : ℕ)) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rcases Finset.mem_filter.mp hi with ⟨_, hJ⟩
    rcases Option.ne_none_iff_exists.mp hJ with ⟨y, hy⟩
    simp [hy.symm]
  -- from h_id_0 we have s = J_sum (since (h0 : ℕ) = 0)
  have h_J_sum : (∑ i ∈ J, (((l.idxFun i).getD h0 : Fin L) : ℕ)) = s := by
    have h0_val : (h0 : ℕ) = 0 := rfl
    rw [h0_val] at h_id_0
    simp [mul_zero, add_zero] at h_id_0
    calc
      (∑ i ∈ J, (((l.idxFun i).getD h0 : Fin L) : ℕ)) = (∑ i, ((l h0 i : ℕ))) := h_id_0.symm
      _ = s := rfl
  have h_sum_eq : (∑ i, ((l t' i : ℕ))) = s + t * I.card := by
    calc
      (∑ i, ((l t' i : ℕ))) = (∑ i ∈ J, (((l.idxFun i).getD t' : Fin L) : ℕ)) + I.card * (t' : ℕ) := h_id_t'
      _ = (∑ i ∈ J, (((l.idxFun i).getD h0 : Fin L) : ℕ)) + I.card * (t' : ℕ) := by rw [h_fixed_sum_eq]
      _ = s + I.card * (t' : ℕ) := by rw [h_J_sum]
      _ = s + I.card * t := by simp [t']
      _ = s + t * I.card := by ring
  have hc_at_t' : χ (∑ i, ((l t' i : ℕ))) = c := hc t'
  rw [h_sum_eq] at hc_at_t'
  exact hc_at_t'

/-- **Van der Waerden's theorem.** For every finite colouring `χ : ℕ → κ` of the
naturals and every length `L ≥ 1` there is a monochromatic arithmetic
progression of length `L` with common difference `m ≥ 1`. -/
theorem van_der_waerden {κ : Type*} [Finite κ] (χ : ℕ → κ) {L : ℕ} (_hL : 1 ≤ L) :
    ∃ s m : ℕ, 1 ≤ m ∧ ∃ c : κ, ∀ t : ℕ, t < L → χ (s + t * m) = c := by
  obtain ⟨m, hm_pos, s, c, h⟩ :=
    exists_mono_homothetic_copy (Finset.range L : Finset ℕ) χ
  refine ⟨s, m, by omega, c, λ t ht => ?_⟩
  have ht_mem : t ∈ Finset.range L := Finset.mem_range.2 ht
  simpa [add_comm, mul_comm, smul_eq_mul] using h t ht_mem

end Dynamics
end LeanEval
/-!
# Minimal subsystems and ω-limit sets

For a homeomorphism `T` of a compact metric space `X` we develop the structural
input to the Furstenberg–Weiss recurrence theorem: the existence of a minimal
subsystem (a nonempty closed invariant set with no proper nonempty closed
invariant subset), and the basic properties of forward ω-limit sets.

A set `M` is *invariant* when `T '' M = M` (the two-sided / `ℤ`-action
convention).  We deliberately phrase minimality directly as a property of closed
invariant sets rather than via Mathlib's one-sided `MulAction`/`IsMinimal`
notions.
-/

namespace LeanEval
namespace Dynamics

open scoped Topology

variable {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]

/-- **The iteration system of `T`.** For an invariant set `M` (`∀ x, x ∈ M ↔ T x ∈ M`)
the homeomorphism `T` restricts to a self-homeomorphism `T|_M : M ≃ₜ M` of the
compact subspace `M`, given on representatives by `(T|_M) x = T x`. -/
def restrict (T : X ≃ₜ X) (M : Set X) (hM : ∀ x, x ∈ M ↔ T x ∈ M) : M ≃ₜ M :=
  @Homeomorph.subtype X X _ _ (· ∈ M) (· ∈ M) T hM

/-- A self-map `S` of a space is *minimal* when the only nonempty closed invariant
subset is the whole space. -/
def IsMinimal {Y : Type*} [TopologicalSpace Y] (S : Y → Y) : Prop :=
  ∀ C : Set Y, IsClosed C → S '' C = C → C.Nonempty → C = Set.univ

/-- The forward `ω`-limit set of `x` under `f`: `ω(x) = ⋂_N closure {f^[k] x : k ≥ N}`,
expressed via Mathlib's `omegaLimit` of the singleton `{x}` along `atTop`. -/
def omegaFwd (f : X → X) (x : X) : Set X :=
  omegaLimit Filter.atTop (fun n : ℕ => f^[n]) {x}

variable (T : X ≃ₜ X)

omit [Nonempty X] in
/-- **Directed intersections of compact sets are nonempty.** A downward-directed
family of nonempty closed subsets of a compact space has nonempty intersection. -/
theorem directed_inter_nonempty {ι : Type*} [Nonempty ι] (C : ι → Set X)
    (hdir : Directed (· ⊇ ·) C) (hne : ∀ i, (C i).Nonempty) (hcl : ∀ i, IsClosed (C i)) :
    (⋂ i, C i).Nonempty :=
  IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hdir hne
    (fun i => (hcl i).isCompact) hcl

omit [Nonempty X] in
/-- **Chains of subsystems have a subsystem lower bound.** A nonempty
downward-directed family of nonempty closed invariant sets has an intersection
that is again nonempty, closed, and invariant. -/
theorem chain_inter_invariant {ι : Type*} [Nonempty ι] (C : ι → Set X)
    (hdir : Directed (· ⊇ ·) C) (hne : ∀ i, (C i).Nonempty) (hcl : ∀ i, IsClosed (C i))
    (hinv : ∀ i, (T : X → X) '' C i = C i) :
    (⋂ i, C i).Nonempty ∧ IsClosed (⋂ i, C i) ∧
      (T : X → X) '' (⋂ i, C i) = ⋂ i, C i := by
  have h_nonempty : (⋂ i, C i).Nonempty :=
    directed_inter_nonempty C hdir hne hcl
  have h_closed : IsClosed (⋂ i, C i) :=
    isClosed_iInter hcl
  have h_inv : (T : X → X) '' (⋂ i, C i) = ⋂ i, C i := by
    have hT_inj : Function.Injective (T : X → X) := T.injective
    have hT_inj_on : Set.InjOn (T : X → X) (⋃ i, C i) :=
      Set.injOn_of_injective hT_inj
    calc
      (T : X → X) '' (⋂ i, C i) = ⋂ i, ((T : X → X) '' C i) := by
        rw [Set.InjOn.image_iInter_eq hT_inj_on]
      _ = ⋂ i, C i := by
        simp_rw [hinv]
  exact And.intro h_nonempty (And.intro h_closed h_inv)

/-- **Existence of a minimal subsystem.** There is a nonempty closed invariant set
`M` with no proper nonempty closed invariant subset. -/
theorem exists_minimal_subsystem :
    ∃ M : Set X, M.Nonempty ∧ IsClosed M ∧ (T : X → X) '' M = M ∧
      ∀ C : Set X, C ⊆ M → C.Nonempty → IsClosed C → (T : X → X) '' C = C → C = M := by
  -- S is the set of nonempty closed invariant subsets of X
  let S : Set (Set X) := {M | M.Nonempty ∧ IsClosed M ∧ (T : X → X) '' M = M}
  have huniv : Set.univ ∈ S := by
    refine ⟨Set.univ_nonempty, isClosed_univ, ?_⟩
    calc
      (T : X → X) '' Set.univ = Set.range (T : X → X) := Set.image_univ
      _ = Set.univ := T.surjective.range_eq
  -- Every chain in S (ordered by ⊆) has a lower bound in S
  have hchain : ∀ c ⊆ S, IsChain (· ⊆ ·) c → ∃ lb ∈ S, ∀ s ∈ c, lb ⊆ s := by
    intro c hcS hchain
    by_cases hcne : c.Nonempty
    · -- c is nonempty: use intersection as lower bound
      rcases hcne with ⟨s0, hs0⟩
      have h_nonempty_ι : Nonempty c := ⟨⟨s0, hs0⟩⟩
      let f : c → Set X := Subtype.val
      have hdir : Directed (· ⊇ ·) f := by
        intro i j
        rcases hchain.total i.2 j.2 with (h | h)
        · -- h : f i ⊆ f j, so f i is the smaller; take k := i
          exact ⟨i, Set.Subset.refl _, h⟩
        · -- h : f j ⊆ f i, so f j is the smaller; take k := j
          exact ⟨j, h, Set.Subset.refl _⟩
      have hne : ∀ i : c, (f i).Nonempty := by
        intro i; exact (hcS i.2).1
      have hcl : ∀ i : c, IsClosed (f i) := by
        intro i; exact (hcS i.2).2.1
      have hinv : ∀ i : c, (T : X → X) '' f i = f i := by
        intro i; exact (hcS i.2).2.2
      have h_chain_inter := chain_inter_invariant T f hdir hne hcl hinv
      refine ⟨⋂ i : c, f i, ?_, ?_⟩
      · exact ⟨h_chain_inter.1, h_chain_inter.2.1, h_chain_inter.2.2⟩
      · intro s hs
        exact Set.iInter_subset (fun (i : c) => f i) ⟨s, hs⟩
    · -- c is empty: use Set.univ as lower bound
      refine ⟨Set.univ, huniv, ?_⟩
      intro s hs
      exfalso; exact hcne ⟨s, hs⟩
  rcases zorn_superset S hchain with ⟨M, hM⟩
  rcases hM.1 with ⟨hM_nonempty, hM_closed, hM_inv⟩
  refine ⟨M, hM_nonempty, hM_closed, hM_inv, ?_⟩
  intro C hC_sub hC_nonempty hC_closed hC_inv
  have hC_S : C ∈ S := ⟨hC_nonempty, hC_closed, hC_inv⟩
  have hM_sub_C : M ⊆ C := hM.2 hC_S hC_sub
  exact Set.Subset.antisymm hC_sub hM_sub_C

omit [Nonempty X] in
/-- **`ω`-limit sets are nonempty.** -/
theorem omega_nonempty (x : X) : (omegaFwd (T : X → X) x).Nonempty := by
  unfold omegaFwd
  exact nonempty_omegaLimit Filter.atTop (fun n : ℕ => (T : X → X)^[n]) {x} (Set.singleton_nonempty x)

omit [CompactSpace X] [Nonempty X] in
/-- **`ω`-limit sets are closed.** -/
theorem omega_closed (x : X) : IsClosed (omegaFwd (T : X → X) x) := by
  -- omegaFwd expands to omegaLimit, and Mathlib's isClosed_omegaLimit handles the rest
  simpa [omegaFwd] using isClosed_omegaLimit (f := Filter.atTop)
    (ϕ := fun (n : ℕ) => (T : X → X)^[n]) (s := {x})

omit [CompactSpace X] [Nonempty X] in
/-- **`ω`-limit sets are forward invariant**: `T (ω(x)) ⊆ ω(x)`. -/
theorem omega_forward_invariant (x : X) :
    (T : X → X) '' omegaFwd (T : X → X) x ⊆ omegaFwd (T : X → X) x := by
  have hT_cont : Continuous (T : X → X) := T.continuous
  have h_comm (t : ℕ) (z : X) : (T : X → X) ((T : X → X)^[t] z) = ((T : X → X)^[t]) ((T : X → X) z) := by
    calc
      (T : X → X) ((T : X → X)^[t] z) = (T : X → X)^[t+1] z := by
        rw [Function.iterate_succ_apply']
      _ = ((T : X → X)^[t]) ((T : X → X) z) := by
        rw [Function.iterate_succ_apply]

  -- Step 1: mapsTo_omegaLimit gives T(ω(x)) ⊆ ω(T x)
  have h_mapsTo_Tx : Set.MapsTo (T : X → X) (omegaFwd (T : X → X) x) (omegaFwd (T : X → X) (T x)) := by
    have hs : Set.MapsTo (T : X → X) ({x} : Set X) ({T x} : Set X) := by
      intro z hz
      simp at hz
      subst hz
      simp
    have h := mapsTo_omegaLimit (f := Filter.atTop) (α' := X) (β' := X) (ϕ := fun (n : ℕ) => (T : X → X)^[n])
      (ϕ' := fun (n : ℕ) => (T : X → X)^[n]) (ga := (T : X → X)) (s' := {T x})
      (hs := hs) (hg := h_comm) (hgc := hT_cont)
    simpa [omegaFwd] using h

  -- Step 2: omegaLimit_image_eq + omegaLimit_subset_of_tendsto give ω(T x) ⊆ ω(x)
  have h_shift_tendsto : Filter.Tendsto (fun (n : ℕ) => n + 1) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_atTop.mpr
    intro N
    refine ⟨N, ?_⟩
    intro m hm
    omega

  have h_eq_shift : omegaFwd (T : X → X) (T x) = omegaLimit Filter.atTop (fun (n : ℕ) => (T : X → X)^[n+1]) {x} := by
    calc
      omegaFwd (T : X → X) (T x) = omegaLimit Filter.atTop (fun (n : ℕ) => (T : X → X)^[n]) {T x} := rfl
      _ = omegaLimit Filter.atTop (fun (n : ℕ) => (T : X → X)^[n]) ((T : X → X) '' {x}) := by simp
      _ = omegaLimit Filter.atTop (fun (n : ℕ) (z : X) => ((T : X → X)^[n]) ((T : X → X) z)) {x} := by
        rw [omegaLimit_image_eq]
      _ = omegaLimit Filter.atTop (fun (n : ℕ) => (T : X → X)^[n+1]) {x} := by
        apply congrArg (fun (ψ : ℕ → X → X) => omegaLimit Filter.atTop ψ {x})
        ext n z
        simp

  have h_subset : omegaFwd (T : X → X) (T x) ⊆ omegaFwd (T : X → X) x := by
    rw [h_eq_shift, omegaFwd]
    change omegaLimit Filter.atTop
      (fun (n : ℕ) (z : X) => ((T : X → X)^[n]) (T z)) {x}
        ⊆ omegaLimit Filter.atTop (fun (n : ℕ) => (T : X → X)^[n]) {x}
    exact omegaLimit_subset_of_tendsto (m := fun (n : ℕ) => n + 1) (hf := h_shift_tendsto)
      (ϕ := fun (n : ℕ) => (T : X → X)^[n]) (s := {x})

  -- Step 3: Combine
  have h_image_subset : (T : X → X) '' omegaFwd (T : X → X) x ⊆ omegaFwd (T : X → X) (T x) :=
    h_mapsTo_Tx.image_subset
  exact Set.Subset.trans h_image_subset h_subset

omit [CompactSpace X] [Nonempty X] in
/-- **`ω`-limit sets are shift-invariant**: `ω(T x) = ω(x)`. The forward orbit of
`T x` is the forward orbit of `x` shifted by one step, so the two `ω`-limit sets
agree (the `ω`-limit depends only on the tail of the orbit). -/
theorem omega_shift_eq (x : X) :
    omegaFwd (T : X → X) (T x) = omegaFwd (T : X → X) x := by
  apply Set.eq_of_subset_of_subset
  · -- ω(T x) ⊆ ω(x): every late return of the shifted orbit is a late return of the orbit
    intro y hy
    unfold omegaFwd at hy ⊢
    rw [mem_omegaLimit_iff_frequently] at hy ⊢
    intro N hN
    have hf := hy N hN
    rw [Filter.frequently_atTop] at hf ⊢
    intro a
    obtain ⟨b, hba, hbN⟩ := hf a
    refine ⟨b + 1, by omega, ?_⟩
    simp only [Set.singleton_inter_nonempty, Set.mem_preimage] at hbN ⊢
    rw [Function.iterate_succ_apply]
    exact hbN
  · -- ω(x) ⊆ ω(T x): a late return at time b ≥ 1 is a late return of the shifted orbit at b - 1
    intro y hy
    unfold omegaFwd at hy ⊢
    rw [mem_omegaLimit_iff_frequently] at hy ⊢
    intro N hN
    have hf := hy N hN
    rw [Filter.frequently_atTop] at hf ⊢
    intro a
    obtain ⟨b, hba, hbN⟩ := hf (a + 1)
    refine ⟨b - 1, by omega, ?_⟩
    simp only [Set.singleton_inter_nonempty, Set.mem_preimage] at hbN ⊢
    have hstep : (T : X → X)^[b - 1] (T x) = (T : X → X)^[b] x := by
      rw [← Function.iterate_succ_apply]
      congr 1
      omega
    rw [hstep]
    exact hbN

omit [CompactSpace X] [Nonempty X] in
/-- **`ω`-limit sets are invariant**: `T (ω(x)) = ω(x)`. -/
theorem omega_two_sided_invariant (x : X) :
    (T : X → X) '' omegaFwd (T : X → X) x = omegaFwd (T : X → X) x := by
  apply Set.eq_of_subset_of_subset
  · -- forward inclusion is already available
    exact omega_forward_invariant T x
  · -- reverse inclusion via the continuous inverse `T.symm`
    have hsymm_cont : Continuous (T.symm : X → X) := T.symm.continuous
    have h_comm : ∀ (t : ℕ) (z : X),
        (T.symm : X → X) ((T : X → X)^[t] z) = ((T : X → X)^[t]) ((T.symm : X → X) z) := by
      intro t
      induction t with
      | zero => intro z; simp
      | succ k ih =>
        intro z
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih (T z)]
        simp [Homeomorph.symm_apply_apply, Homeomorph.apply_symm_apply]
    have hs : Set.MapsTo (T.symm : X → X) ({T x} : Set X) ({(T.symm : X → X) (T x)} : Set X) := by
      intro z hz
      simp only [Set.mem_singleton_iff] at hz
      subst hz
      simp
    have h_maps : Set.MapsTo (T.symm : X → X) (omegaFwd (T : X → X) (T x))
        (omegaFwd (T : X → X) ((T.symm : X → X) (T x))) := by
      have h := mapsTo_omegaLimit (f := Filter.atTop)
        (ϕ := fun (n : ℕ) => (T : X → X)^[n]) (ϕ' := fun (n : ℕ) => (T : X → X)^[n])
        (ga := (T.symm : X → X)) (s' := {(T.symm : X → X) (T x)})
        (hs := hs) (hg := h_comm) (hgc := hsymm_cont)
      simpa [omegaFwd] using h
    have hx_eq : (T.symm : X → X) (T x) = x := T.symm_apply_apply x
    rw [hx_eq] at h_maps
    rw [omega_shift_eq T x] at h_maps
    intro y hy
    exact ⟨(T.symm : X → X) y, h_maps hy, T.apply_symm_apply y⟩

omit [Nonempty X] in
/-- **`ω`-limit sets are subsystems**: nonempty, closed, and invariant. -/
theorem omega_limit_properties (x : X) :
    (omegaFwd (T : X → X) x).Nonempty ∧ IsClosed (omegaFwd (T : X → X) x) ∧
      (T : X → X) '' omegaFwd (T : X → X) x = omegaFwd (T : X → X) x := by
  have h_nonempty : (omegaFwd (T : X → X) x).Nonempty := omega_nonempty T x
  have h_closed : IsClosed (omegaFwd (T : X → X) x) := omega_closed T x
  have h_inv : (T : X → X) '' omegaFwd (T : X → X) x = omegaFwd (T : X → X) x :=
    omega_two_sided_invariant T x
  exact ⟨h_nonempty, h_closed, h_inv⟩

omit [Nonempty X] in
/-- **Forward orbits are dense in a minimal system.** If `T` is minimal then for
every `x` the forward orbit `{T^[k] x : k ≥ 0}` is dense. -/
theorem minimal_forward_dense (hmin : IsMinimal (T : X → X)) (x : X) :
    Dense (Set.range (fun k : ℕ => (T : X → X)^[k] x)) := by
  have hprops := omega_limit_properties T x
  rcases hprops with ⟨hne, hcl, hinv⟩
  have huniv : omegaFwd (T : X → X) x = Set.univ :=
    hmin (omegaFwd (T : X → X) x) hcl hinv hne
  have hsubset : omegaFwd (T : X → X) x ⊆ closure (Set.range (fun k : ℕ => (T : X → X)^[k] x)) := by
    calc
      omegaFwd (T : X → X) x = omegaLimit Filter.atTop (fun n : ℕ => (T : X → X)^[n]) {x} := rfl
      _ ⊆ closure (Set.image2 (fun n : ℕ => (T : X → X)^[n]) Set.univ {x}) :=
        omegaLimit_subset_closure_image2 (f := Filter.atTop) (ϕ := fun n : ℕ => (T : X → X)^[n])
          (s := {x}) (u := Set.univ) (hu := Filter.univ_mem)
      _ = closure ((fun n : ℕ => (T : X → X)^[n] x) '' Set.univ) := by rw [Set.image2_singleton_right]
      _ = closure (Set.range (fun k : ℕ => (T : X → X)^[k] x)) := by simp
  have hunivsubset : Set.univ ⊆ closure (Set.range (fun k : ℕ => (T : X → X)^[k] x)) := by
    rw [← huniv]
    exact hsubset
  rw [dense_iff_closure_eq]
  exact Set.Subset.antisymm (Set.subset_univ _) hunivsubset

end Dynamics
end LeanEval
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
      simpa [n, show (1 : ℝ) / ((0 : ℕ).cast + 1) = (1 : ℝ) by norm_num] using
        h0_spec.2 j hj1 hjd
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
theorem recurrence_sequential (x : X) (d : ℕ) (_hd : 1 ≤ d)
    (h : ∀ ε : ℝ, 0 < ε →
      ∃ n, 1 ≤ n ∧ ∀ j, 1 ≤ j → j ≤ d → dist ((T : X → X)^[j * n] x) x < ε) :
    ∃ n : ℕ → ℕ, StrictMono n ∧
      ∀ j, 1 ≤ j → j ≤ d →
        Filter.Tendsto (fun k => (T : X → X)^[j * n k] x) Filter.atTop (𝓝 x) := by
  by_cases h_arb : ∀ N : ℕ, ∀ ε : ℝ, 0 < ε → ∃ n, N < n ∧ ∀ j, 1 ≤ j → j ≤ d → dist ((T : X → X)^[j * n] x) x < ε
  · rcases recurrence_subseq (x := x) (d := d) (h := h_arb) with ⟨n, hn_mono, hn⟩
    exact ⟨n, hn_mono, hn⟩
  · push Not at h_arb
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
namespace LeanEval
namespace Dynamics

/-!
# Furstenberg–Weiss topological multiple recurrence (single-transformation form)

For every homeomorphism `T` of a nonempty compact metric space `X`,
there is a point `x ∈ X` that is **multiply recurrent**: for every
`d ≥ 1`, the iterates `T, T², …, T^d` of `x` return arbitrarily close
to `x` along a single common time sequence — `T^{j · n_k}(x) → x` as
`k → ∞` for every `j ∈ {1, …, d}`, with a strictly increasing
`n : ℕ → ℕ` shared across `j`.

This is the single-transformation formulation in Knill §56, which
specialises the full Furstenberg–Weiss recurrence theorem to the
family `T, T², …, T^d` instead of arbitrary commuting homeomorphisms.

Compact-Hausdorff alone is insufficient for this sequential
formulation: on the shift over `Ultrafilter ℤ` (compact Hausdorff, not
first-countable), every convergent sequence is eventually constant, so
`T^{j · n_k}(x) → x` along a strictly increasing `n_k` would force
`n_k = 0` eventually. First-countability would suffice as a hypothesis;
the compact-metric form is the standard Furstenberg–Weiss statement.
-/

open Filter Topology

/-- A point `x : X` is **multiply recurrent** for `T : X → X` if for
every `d ≥ 1` there is a strictly increasing `n : ℕ → ℕ` such that
`T^{j · n_k}(x) → x` for every `j ∈ {1, …, d}`. -/
def IsMultiplyRecurrent {X : Type*} [TopologicalSpace X]
    (T : X → X) (x : X) : Prop :=
  ∀ d : ℕ, 1 ≤ d →
    ∃ n : ℕ → ℕ, StrictMono n ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ d →
        Tendsto (fun k : ℕ => T^[j * n k] x) atTop (𝓝 x)

/-- **Restricted iterates agree with ambient iterates.** For a subsystem `M`
(`∀ x, x ∈ M ↔ T x ∈ M`), the iterate `(T|_M)^[k] x`, viewed in `X`, equals
`T^[k] x`. (The inclusion `M ↪ X` is moreover an isometric embedding, so subspace
and ambient distances coincide, by `isometry_subtype_coe`.) -/
theorem restricted_iterate_agreement {X : Type*} [MetricSpace X]
    (T : X ≃ₜ X) (M : Set X) (hM : ∀ x, x ∈ M ↔ T x ∈ M) (x : M) (k : ℕ) :
    (↑(((restrict T M hM : M → M))^[k] x) : X) = (T : X → X)^[k] (x : X) := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    calc
      (↑(((restrict T M hM : M → M))^[k.succ] x) : X)
          = (T : X → X) (↑(((restrict T M hM : M → M))^[k] x) : X) := by
        simp [Function.iterate_succ_apply', restrict, Homeomorph.subtype_apply_coe]
      _ = (T : X → X) ((T : X → X)^[k] (x : X)) := by
        rw [ih]
      _ = (T : X → X)^[k.succ] (x : X) := by
        simp [Function.iterate_succ_apply']

/-- **Transfer from a minimal subsystem to the ambient space.** If `x ∈ M` is
multiply recurrent for the restricted homeomorphism `T|_M`, then it is multiply
recurrent for `T` in `X`. -/
theorem minimal_transfer {X : Type*} [MetricSpace X]
    (T : X ≃ₜ X) (M : Set X) (hM : ∀ x, x ∈ M ↔ T x ∈ M) (x : M)
    (hx : IsMultiplyRecurrent (restrict T M hM : M → M) x) :
    IsMultiplyRecurrent (T : X → X) (x : X) := by
  intro d hd
  rcases hx d hd with ⟨n, hn_mono, hn⟩
  refine ⟨n, hn_mono, ?_⟩
  intro j hj1 hjd
  have h_tendsto_M : Filter.Tendsto (fun k : ℕ => ((restrict T M hM : M → M)^[j * n k] x))
      Filter.atTop (𝓝 x) := hn j hj1 hjd
  have h_cont : Continuous (fun (z : M) => (z : X)) := continuous_subtype_val
  have h_sq : Filter.Tendsto (fun (z : M) => (z : X)) (𝓝 x) (𝓝 (x : X)) :=
    h_cont.tendsto x
  have h_comp : Filter.Tendsto (fun k : ℕ => ((restrict T M hM : M → M)^[j * n k] x : X))
      Filter.atTop (𝓝 (x : X)) :=
    h_sq.comp h_tendsto_M
  have h_agreement (k : ℕ) : (((restrict T M hM : M → M)^[j * n k] x : M) : X) = (T : X → X)^[j * n k] (x : X) := by
    simpa using restricted_iterate_agreement T M hM x (j * n k)
  simpa [h_agreement] using h_comp



end Dynamics
end LeanEval
