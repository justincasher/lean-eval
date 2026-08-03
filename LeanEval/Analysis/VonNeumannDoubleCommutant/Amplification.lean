import Mathlib
import EvalTools.Markers

namespace LeanEval
namespace Analysis

open scoped ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {n : ℕ}

/-- The `i`-th coordinate projection on the amplified space `H^n = PiLp 2 (fun _ : Fin n => H)`,
as a continuous linear map (`PiLp.proj`). -/
abbrev ampProj (i : Fin n) : (PiLp 2 (fun _ : Fin n => H)) →L[ℂ] H :=
  PiLp.proj 2 (fun _ : Fin n => H) i

/-- `def:amplification-map`: the diagonal amplification map
`Δ : B(H) → B(H^n)` sending `A` to the operator `v ↦ (i ↦ A (v i))` on
`H^n = PiLp 2 (fun _ : Fin n => H)`. It is built as
`ContinuousLinearMap.pi (fun i => A ∘L pᵢ)` (transported back to the `ℓ²` copy
along `PiLp.continuousLinearEquiv`), where `pᵢ` is the `i`-th coordinate
projection. -/
noncomputable def amplificationMap (A : H →L[ℂ] H) :
    (PiLp 2 (fun _ : Fin n => H)) →L[ℂ] (PiLp 2 (fun _ : Fin n => H)) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun i => A ∘L ampProj i)

omit [CompleteSpace H] in
/-- `lem:amp-proj`: `Δ` commutes with coordinate projections, i.e.
`pᵢ ∘ Δ(A) = A ∘ pᵢ` for every `A` and index `i`. -/
theorem ampProj_comp_amplificationMap (A : H →L[ℂ] H) (i : Fin n) :
    (ampProj i) ∘L (amplificationMap A) = A ∘L (ampProj i) := by
  ext v
  calc
    (ampProj i) ((amplificationMap A) v)
        = (ampProj i) ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm
            ((ContinuousLinearMap.pi (fun j => A ∘L ampProj j)) v)) := rfl
    _ = ((ContinuousLinearMap.pi (fun j => A ∘L ampProj j)) v) i := by
      simp [PiLp.proj_apply]
    _ = (A ∘L ampProj i) v := by
      simp
    _ = A ((ampProj i) v) := rfl
    _ = (A ∘L (ampProj i)) v := rfl

omit [CompleteSpace H] in
/-- `lem:amp-apply`: the `i`-th coordinate of an amplified vector is
`(Δ(A) v)ᵢ = A (vᵢ)`. -/
theorem amplificationMap_apply (A : H →L[ℂ] H) (v : PiLp 2 (fun _ : Fin n => H)) (i : Fin n) :
    (amplificationMap A v).ofLp i = A (v.ofLp i) := by
  calc
    (amplificationMap A v).ofLp i = (ampProj i) (amplificationMap A v) := by
      rw [PiLp.proj_apply]
    _ = ((ampProj i) ∘L (amplificationMap A)) v := by
      rw [ContinuousLinearMap.comp_apply]
    _ = (A ∘L (ampProj i)) v := by
      rw [ampProj_comp_amplificationMap A i]
    _ = A ((ampProj i) v) := by
      rw [ContinuousLinearMap.comp_apply]
    _ = A (v.ofLp i) := by
      rw [PiLp.proj_apply]

omit [CompleteSpace H] in
/-- `lem:amp-single`: `Δ` commutes with coordinate inclusions, i.e.
`Δ(A) (sⱼ x) = sⱼ (A x)`, where `sⱼ x = PiLp.single 2 j x` is the `j`-th
coordinate inclusion of `H` into `H^n`. -/
theorem amplificationMap_single (A : H →L[ℂ] H) (j : Fin n) (x : H) :
    amplificationMap A (PiLp.single 2 j x) = PiLp.single 2 j (A x) := by
  apply PiLp.ext
  intro i
  by_cases h : i = j
  · subst h
    simp [amplificationMap_apply]
  · simp [h, amplificationMap_apply, map_zero]

omit [CompleteSpace H] in
/-- `lem:amp-map-mul`: `Δ` is multiplicative, `Δ(A B) = Δ(A) Δ(B)`. -/
theorem amplificationMap_mul (A B : H →L[ℂ] H) :
    amplificationMap (n := n) (A * B) = amplificationMap A * amplificationMap B := by
  ext v
  rename_i i
  simp [amplificationMap_apply]

omit [CompleteSpace H] in
/-- `lem:amp-map-one`: `Δ` preserves the identity, `Δ(1) = 1`. -/
theorem amplificationMap_one : amplificationMap (n := n) (1 : H →L[ℂ] H) = 1 := by
  ext v
  rw [amplificationMap_apply]
  simp

omit [CompleteSpace H] in
/-- `lem:amp-map-add`: `Δ` is additive, `Δ(A + B) = Δ(A) + Δ(B)`. -/
theorem amplificationMap_add (A B : H →L[ℂ] H) :
    amplificationMap (n := n) (A + B) = amplificationMap A + amplificationMap B := by
  let X := (PiLp 2 (fun _ : Fin n => H)) →L[ℂ] (PiLp 2 (fun _ : Fin n => H))
  have h : ∀ (i : Fin n), (ampProj i) ∘L (amplificationMap (A + B) : X) = (ampProj i) ∘L ((amplificationMap A : X) + (amplificationMap B : X)) := by
    intro i
    calc
      (ampProj i) ∘L (amplificationMap (A + B) : X) = (A + B) ∘L (ampProj i) := by
        rw [ampProj_comp_amplificationMap]
      _ = A ∘L (ampProj i) + B ∘L (ampProj i) := by
        rw [ContinuousLinearMap.add_comp]
      _ = (ampProj i) ∘L (amplificationMap A : X) + (ampProj i) ∘L (amplificationMap B : X) := by
        rw [ampProj_comp_amplificationMap A i, ampProj_comp_amplificationMap B i]
      _ = (ampProj i) ∘L ((amplificationMap A : X) + (amplificationMap B : X)) := by
        rw [ContinuousLinearMap.comp_add]
  refine ContinuousLinearMap.ext fun v => ?_
  refine PiLp.ext fun i => ?_
  calc
    ((amplificationMap (A + B) : X) v).ofLp i
        = (ampProj i) (((amplificationMap (A + B) : X) v)) := by rw [PiLp.proj_apply]
    _ = ((ampProj i) ∘L (amplificationMap (A + B) : X)) v := by rw [ContinuousLinearMap.comp_apply]
    _ = ((ampProj i) ∘L ((amplificationMap A : X) + (amplificationMap B : X))) v := by rw [h i]
    _ = (ampProj i) (((amplificationMap A : X) + (amplificationMap B : X)) v) := by rw [ContinuousLinearMap.comp_apply]
    _ = (ampProj i) ((amplificationMap A : X) v + (amplificationMap B : X) v) := by rw [add_apply]
    _ = (ampProj i) ((amplificationMap A : X) v) + (ampProj i) ((amplificationMap B : X) v) := by rw [map_add]
    _ = ((amplificationMap A : X) v).ofLp i + ((amplificationMap B : X) v).ofLp i := by
      simp [PiLp.proj_apply]
    _ = (((amplificationMap A : X) v) + ((amplificationMap B : X) v)).ofLp i := by rw [PiLp.add_apply]
    _ = (((amplificationMap A : X) + (amplificationMap B : X)) v).ofLp i := by rw [add_apply]

omit [CompleteSpace H] in
/-- `lem:amp-map-smul`: `Δ` is `ℂ`-linear in scalars, `Δ(c • A) = c • Δ(A)`. -/
theorem amplificationMap_smul (c : ℂ) (A : H →L[ℂ] H) :
    amplificationMap (n := n) (c • A) = c • amplificationMap A := by
  have h1 : ContinuousLinearMap.pi (fun i : Fin n => (c • A) ∘L ampProj i) =
      c • ContinuousLinearMap.pi (fun i : Fin n => A ∘L ampProj i) := by
    ext v i
    simp
  calc
    amplificationMap (c • A) = ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm).toContinuousLinearMap ∘L
        ContinuousLinearMap.pi (fun i : Fin n => (c • A) ∘L ampProj i) := rfl
    _ = ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm).toContinuousLinearMap ∘L
        (c • ContinuousLinearMap.pi (fun i : Fin n => A ∘L ampProj i)) := by rw [h1]
    _ = c • (((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm).toContinuousLinearMap ∘L
        ContinuousLinearMap.pi (fun i : Fin n => A ∘L ampProj i)) := by
      rw [ContinuousLinearMap.comp_smul]
    _ = c • amplificationMap A := rfl

/-- `lem:amp-adjoint`: `Δ` intertwines adjoints, `(Δ(A))^* = Δ(A^*)`. -/
theorem amplificationMap_adjoint (A : H →L[ℂ] H) :
    ContinuousLinearMap.adjoint (amplificationMap (n := n) A)
      = amplificationMap (ContinuousLinearMap.adjoint A) := by
  refine ContinuousLinearMap.ext fun u => ?_
  apply ext_inner_left (𝕜 := ℂ)
  intro v
  calc
    inner ℂ v (ContinuousLinearMap.adjoint (amplificationMap A) u)
        = inner ℂ (amplificationMap A v) u := by
          rw [ContinuousLinearMap.adjoint_inner_right]
    _ = ∑ i : Fin n, inner ℂ ((amplificationMap A v).ofLp i) (u.ofLp i) := by
      rw [PiLp.inner_apply]
    _ = ∑ i : Fin n, inner ℂ (A (v.ofLp i)) (u.ofLp i) := by
      simp [amplificationMap_apply]
    _ = ∑ i : Fin n, inner ℂ (v.ofLp i) ((ContinuousLinearMap.adjoint A) (u.ofLp i)) := by
      simp [ContinuousLinearMap.adjoint_inner_right]
    _ = inner ℂ v (amplificationMap (ContinuousLinearMap.adjoint A) u) := by
      simp [PiLp.inner_apply, amplificationMap_apply]

/-- `def:amplification`: the diagonal amplification as a unital `*`-algebra
homomorphism `Δ : B(H) →⋆ₐ[ℂ] B(H^n)`, bundling `amplificationMap` with the
structure lemmas (`amplificationMap_add`, `amplificationMap_smul`,
`amplificationMap_mul`, `amplificationMap_one`, `amplificationMap_adjoint`). -/
noncomputable def amplification :
    (H →L[ℂ] H) →⋆ₐ[ℂ]
      ((PiLp 2 (fun _ : Fin n => H)) →L[ℂ] (PiLp 2 (fun _ : Fin n => H))) where
  toFun := amplificationMap
  map_one' := amplificationMap_one
  map_mul' := amplificationMap_mul
  map_zero' := by
    have h := amplificationMap_add (n := n) (0 : H →L[ℂ] H) 0
    rw [add_zero] at h
    exact add_right_cancel (a := amplificationMap (0 : H →L[ℂ] H)) (by rw [zero_add]; exact h.symm)
  map_add' := amplificationMap_add
  commutes' := by
    intro r
    have h1 := amplificationMap_smul (n := n) r (1 : H →L[ℂ] H)
    have h2 := amplificationMap_one (H := H) (n := n)
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [h1, h2]
  map_star' := by
    intro x
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
      amplificationMap_adjoint]

/-- `lem:amplification-subalgebra`: the image `Δ(S)` of a unital `*`-subalgebra
`S` under the amplification homomorphism is again a unital `*`-subalgebra of
`B(H^n)`, namely `StarSubalgebra.map amplification S`. -/
noncomputable def amplificationSubalgebra
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    StarSubalgebra ℂ ((PiLp 2 (fun _ : Fin n => H)) →L[ℂ] (PiLp 2 (fun _ : Fin n => H))) :=
  StarSubalgebra.map (amplification (n := n)) S

end Analysis
end LeanEval
