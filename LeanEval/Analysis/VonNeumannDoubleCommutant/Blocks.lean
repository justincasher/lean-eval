import Mathlib
import EvalTools.Markers
import LeanEval.Analysis.VonNeumannDoubleCommutant.Amplification

namespace LeanEval
namespace Analysis

open scoped ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {n : ℕ}

/-- The `j`-th coordinate inclusion `sⱼ : H → H^n` as a continuous linear map.
It sends `x` to the vector of `H^n = PiLp 2 (fun _ : Fin n => H)` whose `j`-th
coordinate is `x` and all others are `0`. It is built from
`ContinuousLinearMap.single` transported into the `ℓ²` copy along
`PiLp.continuousLinearEquiv`. -/
noncomputable def ampSingle (j : Fin n) : H →L[ℂ] (PiLp 2 (fun _ : Fin n => H)) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.single ℂ (fun _ : Fin n => H) j

/-- The `(i, j)` block entry `B_{ij} = pᵢ ∘ B ∘ sⱼ` of an operator
`B : H^n →L[ℂ] H^n`, as a continuous linear map `H →L[ℂ] H`. -/
noncomputable def blockEntry (B : (PiLp 2 (fun _ : Fin n => H)) →L[ℂ] (PiLp 2 (fun _ : Fin n => H)))
    (i j : Fin n) : H →L[ℂ] H :=
  (ampProj i) ∘L B ∘L (ampSingle j)

/-- `pᵢ ∘ sⱼ = id` when `i = j` and `0` otherwise. -/
theorem ampProj_comp_ampSingle (i j : Fin n) :
    (ampProj i) ∘L (ampSingle (H := H) j) = if i = j then ContinuousLinearMap.id ℂ H else 0 := by
  sorry

/-- `lem:proj-reduction`: two operators into `H^n` are equal iff their
compositions with every coordinate projection `pᵢ` agree. -/
theorem proj_reduction
    (B C : (PiLp 2 (fun _ : Fin n => H)) →L[ℂ] (PiLp 2 (fun _ : Fin n => H))) :
    B = C ↔ ∀ i : Fin n, (ampProj i) ∘L B = (ampProj i) ∘L C := by
  constructor
  · intro h i
    rw [h]
  · intro h
    ext v i
    have h' : (ampProj i) (B v) = (ampProj i) (C v) := by
      calc
        (ampProj i) (B v) = ((ampProj i) ∘L B) v := rfl
        _ = ((ampProj i) ∘L C) v := by rw [h i]
        _ = (ampProj i) (C v) := rfl
    simpa [PiLp.proj_apply] using h'

/-- `lem:single-reduction`: two operators on `H^n` are equal iff their
compositions with every coordinate inclusion `sⱼ` agree. -/
theorem single_reduction
    (B C : (PiLp 2 (fun _ : Fin n => H)) →L[ℂ] (PiLp 2 (fun _ : Fin n => H))) :
    B = C ↔ ∀ j : Fin n, B ∘L (ampSingle j) = C ∘L (ampSingle j) := by
  sorry

/-- `lem:blocks-eq`: two operators on `H^n` are equal iff all their block
entries `pᵢ ∘ B ∘ sⱼ` agree. -/
theorem blocks_eq
    (B C : (PiLp 2 (fun _ : Fin n => H)) →L[ℂ] (PiLp 2 (fun _ : Fin n => H))) :
    B = C ↔ ∀ i j : Fin n, blockEntry B i j = blockEntry C i j := by
  constructor
  · intro h i j
    rw [h]
  · intro h
    apply (single_reduction B C).mpr
    intro j
    have h_proj : ∀ i : Fin n, (ampProj i) ∘L (B ∘L ampSingle j) = (ampProj i) ∘L (C ∘L ampSingle j) := by
      intro i
      calc
        (ampProj i) ∘L (B ∘L ampSingle j) = ((ampProj i) ∘L B) ∘L ampSingle j := by
          rw [ContinuousLinearMap.comp_assoc]
        _ = blockEntry B i j := rfl
        _ = blockEntry C i j := h i j
        _ = ((ampProj i) ∘L C) ∘L ampSingle j := rfl
        _ = (ampProj i) ∘L (C ∘L ampSingle j) := by
          rw [ContinuousLinearMap.comp_assoc]
    ext x : 1
    ext i
    simpa [ContinuousLinearMap.comp_apply, PiLp.proj_apply, ampProj] using
      congrArg (fun f : H →L[ℂ] H => f x) (h_proj i)

/-- `lem:block-amp-left`: the `(i, j)` block of `Δ(A) ∘ B` is `A ∘ B_{ij}`. -/
theorem block_amp_left (A : H →L[ℂ] H)
    (B : (PiLp 2 (fun _ : Fin n => H)) →L[ℂ] (PiLp 2 (fun _ : Fin n => H))) (i j : Fin n) :
    blockEntry (amplificationMap A ∘L B) i j = A ∘L (blockEntry B i j) := by
  dsimp [blockEntry]
  calc
    (ampProj i) ∘L (amplificationMap A ∘L B) ∘L (ampSingle j)
        = ((ampProj i) ∘L amplificationMap A) ∘L B ∘L (ampSingle j) := by
      simp [ContinuousLinearMap.comp_assoc]
    _ = (A ∘L (ampProj i)) ∘L B ∘L (ampSingle j) := by
      rw [ampProj_comp_amplificationMap A i]
    _ = A ∘L ((ampProj i) ∘L B ∘L (ampSingle j)) := by
      simp [ContinuousLinearMap.comp_assoc]

/-- `lem:block-amp-right`: the `(i, j)` block of `B ∘ Δ(A)` is `B_{ij} ∘ A`. -/
theorem block_amp_right (A : H →L[ℂ] H)
    (B : (PiLp 2 (fun _ : Fin n => H)) →L[ℂ] (PiLp 2 (fun _ : Fin n => H))) (i j : Fin n) :
    blockEntry (B ∘L amplificationMap A) i j = (blockEntry B i j) ∘L A := by
  sorry

/-- `lem:amp-commute-iff-blocks`: `Δ(A)` commutes with `B` iff `A` commutes with
every block entry `B_{ij}`. -/
theorem amp_commute_iff_blocks (A : H →L[ℂ] H)
    (B : (PiLp 2 (fun _ : Fin n => H)) →L[ℂ] (PiLp 2 (fun _ : Fin n => H))) :
    amplificationMap A * B = B * amplificationMap A ↔
      ∀ i j : Fin n, A ∘L (blockEntry B i j) = (blockEntry B i j) ∘L A := by
  sorry

variable (S : StarSubalgebra ℂ (H →L[ℂ] H))

/-- `lem:commutant-amplification-entrywise`: an operator `B` on `H^n` commutes
with `Δ(A)` for every `A ∈ S` iff every block entry `B_{ij}` lies in the
commutant `S'`. -/
theorem commutant_amplification_entrywise
    (B : (PiLp 2 (fun _ : Fin n => H)) →L[ℂ] (PiLp 2 (fun _ : Fin n => H))) :
    (∀ A ∈ S, amplificationMap A * B = B * amplificationMap A) ↔
      ∀ i j : Fin n, blockEntry B i j ∈ (S : Set (H →L[ℂ] H)).centralizer := by
  constructor
  · intro h i j
    rw [Set.mem_centralizer_iff]
    intro A hA
    have hAmp := h A hA
    have hblocks := (amp_commute_iff_blocks A B).mp hAmp
    have hblock := hblocks i j
    simpa [ContinuousLinearMap.mul_def] using hblock
  · intro h A hA
    apply (amp_commute_iff_blocks A B).mpr
    intro i j
    have hmem := h i j
    rw [Set.mem_centralizer_iff] at hmem
    have hcentral := hmem A hA
    simpa [ContinuousLinearMap.mul_def] using hcentral

/-- `lem:amplification-double-commutant`: if `T ∈ S''`, then
`Δ(T) ∈ (Δ(S))''`. -/
theorem amplification_double_commutant (T : H →L[ℂ] H)
    (hT : T ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer) :
    amplificationMap (n := n) T ∈
      ((amplificationSubalgebra (n := n) S : Set _).centralizer.centralizer) := by
  sorry

end Analysis
end LeanEval
