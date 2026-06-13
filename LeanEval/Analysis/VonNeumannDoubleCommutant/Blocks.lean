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
  constructor
  · intro h j
    rw [h]
  · intro h
    let E := fun _ : Fin n => H
    let equiv : PiLp 2 E ≃L[ℂ] ∀ i : Fin n, H := PiLp.continuousLinearEquiv 2 ℂ E
    let L : (∀ i : Fin n, H) →L[ℂ] PiLp 2 E := equiv.symm.toContinuousLinearMap

    have h_equiv_proj : ∀ (v : PiLp 2 E) (j : Fin n), (equiv v) j = (ampProj j) v := by
      intro v j
      simp [ampProj, equiv, PiLp.proj_apply]

    -- ampSingle j = L.comp (ContinuousLinearMap.single ℂ E j) by definition
    have h_amp_comp : ∀ j, ampSingle (H := H) j = L.comp (ContinuousLinearMap.single ℂ E j) := by
      intro j
      calc
        ampSingle (H := H) j = (equiv.symm.toContinuousLinearMap ∘L ContinuousLinearMap.single ℂ E j) := rfl
        _ = L ∘L ContinuousLinearMap.single ℂ E j := rfl
        _ = L.comp (ContinuousLinearMap.single ℂ E j) := rfl

    -- Key identity: (∑ⱼ sⱼ ∘ pⱼ) v = v for all v
    have h_sum_id : (∑ j : Fin n, ampSingle (H := H) j ∘L ampProj j) = ContinuousLinearMap.id ℂ (PiLp 2 E) := by
      refine ContinuousLinearMap.ext fun v => ?_
      calc
        (∑ j : Fin n, ampSingle (H := H) j ∘L ampProj j) v
            = ∑ j : Fin n, (ampSingle (H := H) j ∘L ampProj j) v := by
          simp [ContinuousLinearMap.sum_apply]
        _ = ∑ j : Fin n, (ampSingle (H := H) j) ((ampProj j) v) := by
          simp
        _ = ∑ j : Fin n, (ampSingle (H := H) j) ((equiv v) j) := by
          simp [h_equiv_proj v]
        _ = ∑ j : Fin n, (L.comp (ContinuousLinearMap.single ℂ E j)) ((equiv v) j) := by
          simp [h_amp_comp]
        _ = L (equiv v) :=
          ContinuousLinearMap.sum_comp_single (ι := Fin n) (φ := E) (R := ℂ) (M := PiLp 2 E) L (equiv v)
        _ = v := by
          simp [L, equiv]

    refine ContinuousLinearMap.ext fun v => ?_
    calc
      B v = B ((∑ j : Fin n, ampSingle (H := H) j ∘L ampProj j) v) := by
        rw [h_sum_id, ContinuousLinearMap.id_apply]
      _ = B (∑ j : Fin n, (ampSingle (H := H) j ∘L ampProj j) v) := by
        simp [ContinuousLinearMap.sum_apply]
      _ = ∑ j : Fin n, B ((ampSingle (H := H) j ∘L ampProj j) v) := by
        rw [map_sum B]
      _ = ∑ j : Fin n, (B ∘L ampSingle (H := H) j) ((ampProj j) v) := by
        simp
      _ = ∑ j : Fin n, (C ∘L ampSingle (H := H) j) ((ampProj j) v) := by
        simp [h]
      _ = ∑ j : Fin n, C ((ampSingle (H := H) j ∘L ampProj j) v) := by
        simp
      _ = C (∑ j : Fin n, (ampSingle (H := H) j ∘L ampProj j) v) := by
        rw [map_sum C]
      _ = C ((∑ j : Fin n, ampSingle (H := H) j ∘L ampProj j) v) := by
        simp [ContinuousLinearMap.sum_apply]
      _ = C v := by
        rw [h_sum_id, ContinuousLinearMap.id_apply]

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

/-- `(ampSingle j) x = PiLp.single 2 j x` pointwise. -/
lemma ampSingle_apply_eq (j : Fin n) (x : H) : (ampSingle j) x = PiLp.single 2 j x := by
  calc
    (ampSingle j) x = ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm
      (ContinuousLinearMap.single ℂ (fun _ : Fin n => H) j x)) := rfl
    _ = (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm (Pi.single j x) := by
      simp
    _ = PiLp.single 2 j x := by
      rw [PiLp.continuousLinearEquiv_symm_apply, PiLp.single]

/-- `Δ(A) ∘ sⱼ = sⱼ ∘ A` as an operator equality. -/
lemma amplificationMap_comp_ampSingle (A : H →L[ℂ] H) (j : Fin n) :
    (amplificationMap A) ∘L (ampSingle (H := H) j) = (ampSingle (H := H) j) ∘L A := by
  apply ContinuousLinearMap.ext
  intro x
  calc
    ((amplificationMap A) ∘L (ampSingle j)) x = (amplificationMap A) ((ampSingle j) x) := rfl
    _ = (amplificationMap A) (PiLp.single 2 j x) := by rw [ampSingle_apply_eq j x]
    _ = PiLp.single 2 j (A x) := by rw [amplificationMap_single A j x]
    _ = (ampSingle j) (A x) := by rw [ampSingle_apply_eq j (A x)]
    _ = ((ampSingle j) ∘L A) x := rfl

/-- `lem:block-amp-right`: the `(i, j)` block of `B ∘ Δ(A)` is `B_{ij} ∘ A`. -/
theorem block_amp_right (A : H →L[ℂ] H)
    (B : (PiLp 2 (fun _ : Fin n => H)) →L[ℂ] (PiLp 2 (fun _ : Fin n => H))) (i j : Fin n) :
    blockEntry (B ∘L amplificationMap A) i j = (blockEntry B i j) ∘L A := by
  dsimp [blockEntry]
  calc
    (ampProj i) ∘L (B ∘L amplificationMap A) ∘L (ampSingle j)
        = (ampProj i) ∘L B ∘L ((amplificationMap A) ∘L (ampSingle j)) := by
      simp [ContinuousLinearMap.comp_assoc]
    _ = (ampProj i) ∘L B ∘L ((ampSingle j) ∘L A) := by
      rw [amplificationMap_comp_ampSingle A j]
    _ = ((ampProj i) ∘L B ∘L (ampSingle j)) ∘L A := by
      simp [ContinuousLinearMap.comp_assoc]

/-- `lem:amp-commute-iff-blocks`: `Δ(A)` commutes with `B` iff `A` commutes with
every block entry `B_{ij}`. -/
theorem amp_commute_iff_blocks (A : H →L[ℂ] H)
    (B : (PiLp 2 (fun _ : Fin n => H)) →L[ℂ] (PiLp 2 (fun _ : Fin n => H))) :
    amplificationMap A * B = B * amplificationMap A ↔
      ∀ i j : Fin n, A ∘L (blockEntry B i j) = (blockEntry B i j) ∘L A := by
  -- `ampSingle` equals `PiLp.single` pointwise
  have h_ampSingle_eq (j : Fin n) (x : H) : ampSingle j x = PiLp.single 2 j x := by
    simp [ampSingle]
  -- internal proof of block_amp_right needed below
  have h_block_amp_right (A : H →L[ℂ] H)
      (B : (PiLp 2 (fun _ : Fin n => H)) →L[ℂ] (PiLp 2 (fun _ : Fin n => H))) (i j : Fin n) :
      blockEntry (B ∘L amplificationMap A) i j = (blockEntry B i j) ∘L A := by
    -- key identity: amplificationMap A ∘L ampSingle j = ampSingle j ∘L A
    have h_comm : amplificationMap A ∘L ampSingle (H := H) j = ampSingle (H := H) j ∘L A := by
      apply ContinuousLinearMap.ext
      intro x
      calc
        (amplificationMap A ∘L ampSingle j) x = amplificationMap A (ampSingle j x) := rfl
        _ = amplificationMap A (PiLp.single 2 j x) := by rw [h_ampSingle_eq j x]
        _ = PiLp.single 2 j (A x) := by rw [amplificationMap_single A j x]
        _ = ampSingle j (A x) := by rw [h_ampSingle_eq j (A x)]
        _ = (ampSingle j ∘L A) x := rfl
    calc
      blockEntry (B ∘L amplificationMap A) i j
          = (ampProj i) ∘L (B ∘L amplificationMap A) ∘L (ampSingle j) := rfl
      _ = (ampProj i) ∘L B ∘L (amplificationMap A ∘L ampSingle j) := by
        simp [ContinuousLinearMap.comp_assoc]
      _ = (ampProj i) ∘L B ∘L (ampSingle j ∘L A) := by rw [h_comm]
      _ = ((ampProj i) ∘L B ∘L (ampSingle j)) ∘L A := by
        simp [ContinuousLinearMap.comp_assoc]
      _ = (blockEntry B i j) ∘L A := rfl
  -- main proof using blocks_eq, block_amp_left, and h_block_amp_right
  constructor
  · intro h i j
    have hblocks := (blocks_eq (amplificationMap A * B) (B * amplificationMap A)).mp ?_
    · have hblock := hblocks i j
      calc
        A ∘L (blockEntry B i j) = blockEntry (amplificationMap A * B) i j := by
          symm; simpa [ContinuousLinearMap.mul_def] using block_amp_left A B i j
        _ = blockEntry (B * amplificationMap A) i j := hblock
        _ = (blockEntry B i j) ∘L A := by
          simpa [ContinuousLinearMap.mul_def] using h_block_amp_right A B i j
    · simpa [ContinuousLinearMap.mul_def] using h
  · intro h
    apply (blocks_eq (amplificationMap A * B) (B * amplificationMap A)).mpr
    intro i j
    calc
      blockEntry (amplificationMap A * B) i j = A ∘L (blockEntry B i j) := by
        simpa [ContinuousLinearMap.mul_def] using block_amp_left A B i j
      _ = (blockEntry B i j) ∘L A := h i j
      _ = blockEntry (B * amplificationMap A) i j := by
        simpa [ContinuousLinearMap.mul_def] using (h_block_amp_right A B i j).symm

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
  rw [Set.mem_centralizer_iff]
  intro B hB
  rw [Set.mem_centralizer_iff] at hB
  have h_commutes_all_A : ∀ A ∈ S, amplificationMap A * B = B * amplificationMap A := by
    intro A hA
    apply hB
    dsimp [amplificationSubalgebra]
    refine ⟨A, hA, ?_⟩
    rfl
  have h_block_entries : ∀ i j : Fin n, blockEntry B i j ∈ (S : Set (H →L[ℂ] H)).centralizer :=
    ((commutant_amplification_entrywise S B).mp h_commutes_all_A)
  rw [Set.mem_centralizer_iff] at hT
  have h_T_commutes_blocks : ∀ i j : Fin n, T * (blockEntry B i j) = (blockEntry B i j) * T := by
    intro i j
    have h_entry : blockEntry B i j ∈ (S : Set (H →L[ℂ] H)).centralizer := h_block_entries i j
    exact (hT (blockEntry B i j) h_entry).symm
  have h_comm : amplificationMap T * B = B * amplificationMap T :=
    (amp_commute_iff_blocks T B).mpr (by
      intro i j
      simpa [ContinuousLinearMap.mul_def] using h_T_commutes_blocks i j)
  exact h_comm.symm

end Analysis
end LeanEval
