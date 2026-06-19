import Mathlib
import EvalTools.Markers

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
theorem van_der_waerden {κ : Type*} [Finite κ] (χ : ℕ → κ) {L : ℕ} (hL : 1 ≤ L) :
    ∃ s m : ℕ, 1 ≤ m ∧ ∃ c : κ, ∀ t : ℕ, t < L → χ (s + t * m) = c := by
  obtain ⟨m, hm_pos, s, c, h⟩ :=
    exists_mono_homothetic_copy (Finset.range L : Finset ℕ) χ
  refine ⟨s, m, by omega, c, λ t ht => ?_⟩
  have ht_mem : t ∈ Finset.range L := Finset.mem_range.2 ht
  simpa [add_comm, mul_comm, smul_eq_mul] using h t ht_mem

end Dynamics
end LeanEval
