import Mathlib
import EvalTools.Markers

namespace LeanEval
namespace Analysis

/-!
# Orbits of a subalgebra and the single-vector approximation

Supporting material for the hard implication of von Neumann's double commutant theorem.
Given a unital subalgebra `R` of bounded operators on a Hilbert space `K` and a vector
`x : K`, the *orbit* `M₀ = {A x : A ∈ R}` is a linear subspace of `K` containing `x` and
invariant under `R`. Its topological closure `M` is a closed invariant subspace, and when
`R` is a `*`-subalgebra the orthogonal projection onto `M` lies in the commutant `R'`. This
yields the single-vector approximation `T x ∈ closure {A x : A ∈ R}` for `T ∈ R''`.

Blueprint labels: `lem:orbit-submodule` through `lem:single-vector-approx`.
-/

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The orbit submodule `M₀ = {A x : A ∈ R}`, defined as the image of the unital subalgebra
`R` of `K →L[ℂ] K` under the linear evaluation `A ↦ A x`.  (Blueprint: `lem:orbit-submodule`.) -/
noncomputable def orbitSubmodule (R : Subalgebra ℂ (K →L[ℂ] K)) (x : K) : Submodule ℂ K :=
  (Subalgebra.toSubmodule R).map (ContinuousLinearMap.apply ℂ K x).toLinearMap

/-- The topological closure `M` of the orbit `M₀ = {A x : A ∈ R}`.
(Blueprint: `lem:invariant-closure`.) -/
noncomputable def orbitClosure (R : Subalgebra ℂ (K →L[ℂ] K)) (x : K) : Submodule ℂ K :=
  (orbitSubmodule R x).topologicalClosure

/-- The orbit `M₀ = {A x : A ∈ R}` is a submodule containing `x`.  (Blueprint:
`lem:orbit-submodule`.) -/
theorem mem_orbitSubmodule (R : Subalgebra ℂ (K →L[ℂ] K)) (x : K) :
    x ∈ orbitSubmodule R x := by
  sorry

/-- For every `A ∈ R`, the orbit `M₀` is invariant under `A`, i.e. `A (M₀) ⊆ M₀`.
(Blueprint: `lem:orbit-invariant`.) -/
theorem orbitSubmodule_mem_invtSubmodule (R : Subalgebra ℂ (K →L[ℂ] K)) (x : K)
    {A : K →L[ℂ] K} (hA : A ∈ R) :
    orbitSubmodule R x ∈ Module.End.invtSubmodule A.toLinearMap := by
  sorry

/-- The closure `M` of the orbit is a closed invariant subspace containing `x`: `x ∈ M`, and
for every `A ∈ R` the subspace `M` is invariant under `A`.  (Blueprint:
`lem:invariant-closure`.) -/
theorem orbitClosure_invariant (R : Subalgebra ℂ (K →L[ℂ] K)) (x : K) :
    x ∈ orbitClosure R x ∧
      ∀ {A : K →L[ℂ] K}, A ∈ R →
        orbitClosure R x ∈ Module.End.invtSubmodule A.toLinearMap := by
  sorry

/-- Adjoint-invariance passes to the orthogonal complement: if a closed subspace `V` is
invariant under `A∗`, then `Vᗮ` is invariant under `A`.  (Blueprint:
`lem:orthogonal-invariant`.) -/
theorem orthogonal_invariant (A : K →L[ℂ] K) (V : Submodule ℂ K)
    [V.HasOrthogonalProjection]
    (hV : V ∈ Module.End.invtSubmodule (ContinuousLinearMap.adjoint A).toLinearMap) :
    Vᗮ ∈ Module.End.invtSubmodule A.toLinearMap := by
  sorry

/-- If `A (V) ⊆ V`, then the orthogonal projection `P = P_V` fixes `A (P v)`:
`P (A (P v)) = A (P v)`.  (Blueprint: `lem:proj-on-invariant`.) -/
theorem starProjection_apply_of_invariant (A : K →L[ℂ] K) (V : Submodule ℂ K)
    [V.HasOrthogonalProjection]
    (hV : V ∈ Module.End.invtSubmodule A.toLinearMap) (v : K) :
    V.starProjection (A (V.starProjection v)) = A (V.starProjection v) := by
  sorry

/-- If `A (Vᗮ) ⊆ Vᗮ`, then the projection `P = P_V` annihilates the orthogonal part:
`P (A ((1 - P) v)) = 0`.  (Blueprint: `lem:proj-on-orthogonal`.) -/
theorem starProjection_apply_of_orthogonal_invariant (A : K →L[ℂ] K) (V : Submodule ℂ K)
    [V.HasOrthogonalProjection]
    (hV : Vᗮ ∈ Module.End.invtSubmodule A.toLinearMap) (v : K) :
    V.starProjection (A (Vᗮ.starProjection v)) = 0 := by
  sorry

/-- If a closed subspace `V` is invariant under both `A` and `A∗`, then the orthogonal
projection onto `V` commutes with `A`: `A * P = P * A`.  (Blueprint:
`lem:projection-commutes`.) -/
theorem starProjection_commute (A : K →L[ℂ] K) (V : Submodule ℂ K)
    [V.HasOrthogonalProjection]
    (hA : V ∈ Module.End.invtSubmodule A.toLinearMap)
    (hAstar : V ∈ Module.End.invtSubmodule (ContinuousLinearMap.adjoint A).toLinearMap) :
    A * V.starProjection = V.starProjection * A := by
  sorry

/-- For a unital `*`-subalgebra `R` and `x : K`, the orthogonal projection `P` onto the orbit
closure `M` lies in the commutant `R'`.  (Blueprint: `lem:projection-in-commutant`.) -/
theorem starProjection_orbitClosure_mem_centralizer
    (R : StarSubalgebra ℂ (K →L[ℂ] K)) (x : K)
    [(orbitClosure R.toSubalgebra x).HasOrthogonalProjection] :
    (orbitClosure R.toSubalgebra x).starProjection ∈
      Set.centralizer (R : Set (K →L[ℂ] K)) := by
  sorry

/-- Single-vector approximation: for a unital `*`-subalgebra `R` and `T ∈ R''`, every vector
`x : K` satisfies `T x ∈ closure {A x : A ∈ R}`.  (Blueprint: `lem:single-vector-approx`.) -/
theorem single_vector_approx (R : StarSubalgebra ℂ (K →L[ℂ] K))
    {T : K →L[ℂ] K}
    (hT : T ∈ Set.centralizer (Set.centralizer (R : Set (K →L[ℂ] K)))) (x : K) :
    T x ∈ closure {y : K | ∃ A ∈ R, A x = y} := by
  sorry

end Analysis
end LeanEval
