import Mathlib
import LeanEval.RepresentationTheory.SchurWeyl.Defs
import LeanEval.RepresentationTheory.SchurWeyl.Polarization

/-!
The identification `(End_R V)^⊗k ≅ End_R(V^⊗k)` and the polarization step identifying the
centralizer of `S_k` with the symmetric tensors / the span of the diagonal maps.

These declarations support the blueprint
`schur-weyl-duality-s-k-image-equals-centralizer-of-glv-image`.
-/

namespace LeanEval
namespace RepresentationTheory

open scoped TensorProduct

variable {R : Type*} [Field R] {M : Type*} [AddCommGroup M] [Module R M] {k : ℕ}

/-- The tensor-power-of-`End` algebra map `Φ : (End_R V)^⊗k → End_R(V^⊗k)`, sending a pure
tensor `m₁ ⊗ ⋯ ⊗ m_k` to the diagonal map `PiTensorProduct.map (fun i => m i)`. -/
noncomputable def endTensorHom (R M : Type*) [Field R] [AddCommGroup M] [Module R M] (k : ℕ) :
    (⨂[R]^k (Module.End R M)) →ₐ[R] Module.End R (⨂[R]^k M) :=
  AlgHom.ofLinearMap
    (PiTensorProduct.lift
      (PiTensorProduct.mapMultilinear (R := R) (s := fun _ : Fin k => M)
        (t := fun _ : Fin k => M)))
    sorry sorry

/-- The two endomorphism spaces have equal (finite) dimension, both `(dim V)^(2k)`. -/
theorem finrank_endTensor_eq [FiniteDimensional R M] :
    Module.finrank R (⨂[R]^k (Module.End R M)) =
      Module.finrank R (Module.End R (⨂[R]^k M)) := by
  sorry

/-- `Φ` is bijective. -/
theorem endTensorHom_bijective [FiniteDimensional R M] :
    Function.Bijective (endTensorHom R M k) := by
  sorry

/-- The tensor-power-of-`End` algebra equivalence `Φ^~ : (End_R V)^⊗k ≃ End_R(V^⊗k)`. -/
noncomputable def endTensorEquiv (R M : Type*) [Field R] [AddCommGroup M] [Module R M]
    [FiniteDimensional R M] (k : ℕ) :
    (⨂[R]^k (Module.End R M)) ≃ₐ[R] Module.End R (⨂[R]^k M) :=
  AlgEquiv.ofBijective (endTensorHom R M k) (endTensorHom_bijective (R := R) (M := M) (k := k))

/-- `Φ` intertwines the factor-permuting `S_k`-action with conjugation by `symAction`. -/
theorem endTensorHom_intertwine (σ : Equiv.Perm (Fin k)) (x : ⨂[R]^k (Module.End R M)) :
    endTensorHom R M k (symAction R (Module.End R M) k σ x) =
      symAction R M k σ * endTensorHom R M k x * symAction R M k σ⁻¹ := by
  sorry

/-- Generic shifts are invertible: for `m ∈ End_R V`, the endomorphism `m + t·id` fails to be
invertible for only finitely many `t`, at most `dim V` of them. -/
theorem finite_not_isUnit_shift [FiniteDimensional R M] (m : Module.End R M) :
    {t : R | ¬ IsUnit (m + t • (1 : Module.End R M))}.Finite ∧
      {t : R | ¬ IsUnit (m + t • (1 : Module.End R M))}.ncard ≤ Module.finrank R M := by
  sorry

/-- The `GL(V)`-orbit spans the same space as the diagonal `End_R V`-orbit: the span of
`{ glAction g : g ∈ GL(V) }` equals the span of `{ map (fun i => m) : m ∈ End_R V }`. -/
theorem span_range_glAction_eq_span_map [FiniteDimensional R M] [Invertible (k.factorial : R)] :
    Submodule.span R (Set.range (glAction R M k)) =
      Submodule.span R (Set.range fun m : Module.End R M =>
        PiTensorProduct.map (fun _ : Fin k => m)) := by
  sorry

/-- The centralizer of `range symAction` equals (as a set) the span of the diagonal maps
`{ map (fun i => m) : m ∈ End_R V }`, i.e. the symmetric tensors transported by `Φ^~`. -/
theorem centralizer_range_symAction_eq_span_map [FiniteDimensional R M]
    [Invertible (k.factorial : R)] :
    (Subalgebra.centralizer R (Set.range (symAction R M k)) :
        Set (Module.End R (⨂[R]^k M))) =
      (Submodule.span R (Set.range fun m : Module.End R M =>
        PiTensorProduct.map (fun _ : Fin k => m)) : Set (Module.End R (⨂[R]^k M))) := by
  sorry

/-- The centralizer of a set equals the centralizer of its `R`-linear span. -/
theorem centralizer_eq_centralizer_span (S : Set (Module.End R (⨂[R]^k M))) :
    Subalgebra.centralizer R S =
      Subalgebra.centralizer R (Submodule.span R S : Set (Module.End R (⨂[R]^k M))) := by
  sorry

end RepresentationTheory
end LeanEval
