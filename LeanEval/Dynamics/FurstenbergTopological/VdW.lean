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
  sorry

/-- **From a combinatorial line to an arithmetic progression.** Fix `L ≥ 1` and a
colouring `χ : ℕ → κ`. Colour the hypercube `ι → Fin L` by `v ↦ χ (∑ i, v i)`. A
monochromatic line of this colouring yields a `χ`-monochromatic arithmetic
progression `s, s + m, …, s + (L-1) m` of length `L` with common difference
`m ≥ 1`. -/
theorem line_to_progression {L : ℕ} (hL : 1 ≤ L) {κ : Type*} (χ : ℕ → κ)
    {ι : Type*} [Fintype ι] (l : Line (Fin L) ι)
    (hl : l.IsMono (fun v : ι → Fin L => χ (∑ i, (v i : ℕ)))) :
    ∃ s m : ℕ, 1 ≤ m ∧ ∃ c : κ, ∀ t : ℕ, t < L → χ (s + t * m) = c := by
  sorry

/-- **Van der Waerden's theorem.** For every finite colouring `χ : ℕ → κ` of the
naturals and every length `L ≥ 1` there is a monochromatic arithmetic
progression of length `L` with common difference `m ≥ 1`. -/
theorem van_der_waerden {κ : Type*} [Finite κ] (χ : ℕ → κ) {L : ℕ} (hL : 1 ≤ L) :
    ∃ s m : ℕ, 1 ≤ m ∧ ∃ c : κ, ∀ t : ℕ, t < L → χ (s + t * m) = c := by
  sorry

end Dynamics
end LeanEval
