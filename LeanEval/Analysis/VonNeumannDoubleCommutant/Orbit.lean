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

omit [CompleteSpace K] in
/-- The orbit `M₀ = {A x : A ∈ R}` is a submodule containing `x`.  (Blueprint:
`lem:orbit-submodule`.) -/
theorem mem_orbitSubmodule (R : Subalgebra ℂ (K →L[ℂ] K)) (x : K) :
    x ∈ orbitSubmodule R x := by
  rw [orbitSubmodule]
  refine Submodule.mem_map.mpr ?_
  refine ⟨(1 : K →L[ℂ] K), ?_, ?_⟩
  · exact (Subalgebra.mem_toSubmodule (S := R)).mpr (Subalgebra.one_mem R)
  · simp

omit [CompleteSpace K] in
/-- For every `A ∈ R`, the orbit `M₀` is invariant under `A`, i.e. `A (M₀) ⊆ M₀`.
(Blueprint: `lem:orbit-invariant`.) -/
theorem orbitSubmodule_mem_invtSubmodule (R : Subalgebra ℂ (K →L[ℂ] K)) (x : K)
    {A : K →L[ℂ] K} (hA : A ∈ R) :
    orbitSubmodule R x ∈ Module.End.invtSubmodule A.toLinearMap := by
  rw [Module.End.mem_invtSubmodule_iff_mapsTo]
  intro v hv
  rw [orbitSubmodule] at hv
  rcases Submodule.mem_map.mp hv with ⟨B, hB, hv'⟩
  have hBx : B x = v := by simpa using hv'
  have hAB : A * B ∈ R := R.mul_mem hA hB
  have h_eq : A v = (A * B) x := by
    calc
      A v = A (B x) := by rw [hBx]
      _ = (A * B) x := rfl
  rw [orbitSubmodule]
  apply Submodule.mem_map.mpr
  refine ⟨A * B, hAB, ?_⟩
  simp [h_eq]

omit [CompleteSpace K] in
/-- The closure `M` of the orbit is a closed invariant subspace containing `x`: `x ∈ M`, and
for every `A ∈ R` the subspace `M` is invariant under `A`.  (Blueprint:
`lem:invariant-closure`.) -/
theorem orbitClosure_invariant (R : Subalgebra ℂ (K →L[ℂ] K)) (x : K) :
    x ∈ orbitClosure R x ∧
      ∀ {A : K →L[ℂ] K}, A ∈ R →
        orbitClosure R x ∈ Module.End.invtSubmodule A.toLinearMap := by
  have hx : x ∈ orbitSubmodule R x := mem_orbitSubmodule R x
  have hx_cl : x ∈ orbitClosure R x := by
    dsimp [orbitClosure]
    exact Submodule.le_topologicalClosure (orbitSubmodule R x) hx
  have h_inv : ∀ {A : K →L[ℂ] K}, A ∈ R →
      orbitClosure R x ∈ Module.End.invtSubmodule A.toLinearMap := by
    intro A hA
    have hOrbit_inv : orbitSubmodule R x ∈ Module.End.invtSubmodule A.toLinearMap :=
      orbitSubmodule_mem_invtSubmodule R x hA
    dsimp [orbitClosure]
    simpa using
      Submodule.topologicalClosure_mem_invtSubmodule (s := orbitSubmodule R x) (f := A) hOrbit_inv
  exact And.intro hx_cl h_inv

/-- Adjoint-invariance passes to the orthogonal complement: if a closed subspace `V` is
invariant under `A∗`, then `Vᗮ` is invariant under `A`.  (Blueprint:
`lem:orthogonal-invariant`.) -/
theorem orthogonal_invariant (A : K →L[ℂ] K) (V : Submodule ℂ K)
    [V.HasOrthogonalProjection]
    (hV : V ∈ Module.End.invtSubmodule (ContinuousLinearMap.adjoint A).toLinearMap) :
    Vᗮ ∈ Module.End.invtSubmodule A.toLinearMap := by
  -- This is exactly ContinuousLinearMap.orthogonal_mem_invtSubmodule
  exact ContinuousLinearMap.orthogonal_mem_invtSubmodule hV

omit [CompleteSpace K] in
/-- If `A (V) ⊆ V`, then the orthogonal projection `P = P_V` fixes `A (P v)`:
`P (A (P v)) = A (P v)`.  (Blueprint: `lem:proj-on-invariant`.) -/
theorem starProjection_apply_of_invariant (A : K →L[ℂ] K) (V : Submodule ℂ K)
    [V.HasOrthogonalProjection]
    (hV : V ∈ Module.End.invtSubmodule A.toLinearMap) (v : K) :
    V.starProjection (A (V.starProjection v)) = A (V.starProjection v) := by
  have hproj_mem : V.starProjection v ∈ V := by
    have h_idem : V.starProjection (V.starProjection v) = V.starProjection v := by
      calc
        V.starProjection (V.starProjection v) = (V.starProjection * V.starProjection) v := rfl
        _ = V.starProjection v := by
          have h_idem_elem : IsIdempotentElem (V.starProjection : K →L[ℂ] K) :=
            Submodule.isIdempotentElem_starProjection (K := V)
          simpa only [mul_apply_eq_comp] using congrArg (· v) h_idem_elem.eq
    exact ((Submodule.starProjection_eq_self_iff (K := V) (v := V.starProjection v)).mp h_idem)
  have hA_mem : A (V.starProjection v) ∈ V := by
    have hV' : V ≤ V.comap A.toLinearMap := (Module.End.mem_invtSubmodule (f := A.toLinearMap)).mp hV
    exact hV' hproj_mem
  rw [Submodule.starProjection_eq_self_iff]
  exact hA_mem

omit [CompleteSpace K] in
/-- If `A (Vᗮ) ⊆ Vᗮ`, then the projection `P = P_V` annihilates the orthogonal part:
`P (A ((1 - P) v)) = 0`.  (Blueprint: `lem:proj-on-orthogonal`.) -/
theorem starProjection_apply_of_orthogonal_invariant (A : K →L[ℂ] K) (V : Submodule ℂ K)
    [V.HasOrthogonalProjection]
    (hV : Vᗮ ∈ Module.End.invtSubmodule A.toLinearMap) (v : K) :
    V.starProjection (A (Vᗮ.starProjection v)) = 0 := by
  have hmem : Vᗮ.starProjection v ∈ Vᗮ := Submodule.starProjection_apply_mem _ _
  have hle : Vᗮ ≤ (Vᗮ).comap A.toLinearMap := by
    -- invtSubmodule's carrier is {p | p ≤ p.comap f}
    simpa [Module.End.invtSubmodule] using hV
  have hA : A (Vᗮ.starProjection v) ∈ Vᗮ := by
    apply hle
    exact hmem
  rw [Submodule.starProjection_apply_eq_zero_iff]
  exact hA

/-- If a closed subspace `V` is invariant under both `A` and `A∗`, then the orthogonal
projection onto `V` commutes with `A`: `A * P = P * A`.  (Blueprint:
`lem:projection-commutes`.) -/
theorem starProjection_commute (A : K →L[ℂ] K) (V : Submodule ℂ K)
    [V.HasOrthogonalProjection]
    (hA : V ∈ Module.End.invtSubmodule A.toLinearMap)
    (hAstar : V ∈ Module.End.invtSubmodule (ContinuousLinearMap.adjoint A).toLinearMap) :
    A * V.starProjection = V.starProjection * A := by
  have hVperp : Vᗮ ∈ Module.End.invtSubmodule A.toLinearMap :=
    orthogonal_invariant A V hAstar
  ext v
  have hzero : V.starProjection (A (Vᗮ.starProjection v)) = 0 :=
    starProjection_apply_of_orthogonal_invariant A V hVperp v
  calc
    (A * V.starProjection) v = A (V.starProjection v) := rfl
    _ = V.starProjection (A (V.starProjection v)) := by
      symm; exact starProjection_apply_of_invariant A V hA _
    _ = V.starProjection (A (V.starProjection v)) + 0 := by rw [add_zero]
    _ = V.starProjection (A (V.starProjection v)) + V.starProjection (A (Vᗮ.starProjection v)) := by rw [hzero]
    _ = V.starProjection (A (V.starProjection v) + A (Vᗮ.starProjection v)) := by rw [← map_add]
    _ = V.starProjection (A (V.starProjection v + Vᗮ.starProjection v)) := by rw [← map_add]
    _ = V.starProjection (A v) := by rw [Submodule.starProjection_add_starProjection_orthogonal v]
    _ = (V.starProjection * A) v := rfl

/-- For a unital `*`-subalgebra `R` and `x : K`, the orthogonal projection `P` onto the orbit
closure `M` lies in the commutant `R'`.  (Blueprint: `lem:projection-in-commutant`.) -/
theorem starProjection_orbitClosure_mem_centralizer
    (R : StarSubalgebra ℂ (K →L[ℂ] K)) (x : K)
    [(orbitClosure R.toSubalgebra x).HasOrthogonalProjection] :
    (orbitClosure R.toSubalgebra x).starProjection ∈
      Set.centralizer (R : Set (K →L[ℂ] K)) := by
  rw [Set.mem_centralizer_iff]
  intro A hA
  have hA_sub : A ∈ R.toSubalgebra := hA
  have hAstar : star A ∈ R := R.star_mem' hA
  have hAstar_sub : star A ∈ R.toSubalgebra := hAstar
  have h_inv : orbitClosure R.toSubalgebra x ∈ Module.End.invtSubmodule A.toLinearMap :=
    (orbitClosure_invariant R.toSubalgebra x).2 hA_sub
  have h_inv_adj : orbitClosure R.toSubalgebra x ∈
      Module.End.invtSubmodule (ContinuousLinearMap.adjoint A).toLinearMap :=
    (orbitClosure_invariant R.toSubalgebra x).2 hAstar_sub
  exact starProjection_commute A (orbitClosure R.toSubalgebra x) h_inv h_inv_adj

/-- Single-vector approximation: for a unital `*`-subalgebra `R` and `T ∈ R''`, every vector
`x : K` satisfies `T x ∈ closure {A x : A ∈ R}`.  (Blueprint: `lem:single-vector-approx`.) -/
theorem single_vector_approx (R : StarSubalgebra ℂ (K →L[ℂ] K))
    {T : K →L[ℂ] K}
    (hT : T ∈ Set.centralizer (Set.centralizer (R : Set (K →L[ℂ] K)))) (x : K) :
    T x ∈ closure {y : K | ∃ A ∈ R, A x = y} := by
  set M := orbitClosure R.toSubalgebra x with hM
  have h_closed : IsClosed ((M : Set K)) := by
    rw [hM, orbitClosure]
    exact Submodule.isClosed_topologicalClosure _
  haveI : M.HasOrthogonalProjection := by
    let M_closed : ClosedSubmodule ℂ K :=
      { M with isClosed' := h_closed }
    have h : (M_closed : Submodule ℂ K).HasOrthogonalProjection :=
      Submodule.instHasOrthogonalProjectionOfCompleteSpace (K := M_closed)
    simpa using h
  set P := M.starProjection with hP
  have hP_central : P ∈ Set.centralizer (R : Set (K →L[ℂ] K)) :=
    starProjection_orbitClosure_mem_centralizer R x
  have hT_comm_P : P * T = T * P := by
    rw [Set.mem_centralizer_iff] at hT
    exact hT P hP_central
  have hxM : x ∈ M := (orbitClosure_invariant R.toSubalgebra x).1
  have hPx : P x = x := by
    rw [Submodule.starProjection_eq_self_iff]
    exact hxM
  have hTx_PTx : T x = P (T x) := by
    calc
      T x = T (P x) := by rw [hPx]
      _ = (T * P) x := rfl
      _ = (P * T) x := by rw [hT_comm_P]
      _ = P (T x) := rfl
  have hPTx_in_M : P (T x) ∈ (M : Set K) := by
    have h_mem : P (T x) ∈ (M.starProjection : K →ₗ[ℂ] K).range := by
      apply LinearMap.mem_range.mpr
      exact ⟨T x, by simp [hP]⟩
    have h_rng : (M.starProjection : K →ₗ[ℂ] K).range = M := Submodule.range_starProjection M
    simpa [h_rng] using h_mem
  have hTx_in_M : T x ∈ (M : Set K) := by
    rw [hTx_PTx]
    exact hPTx_in_M
  have h_orbit_set_eq : (orbitSubmodule R.toSubalgebra x : Set K) = {y : K | ∃ A ∈ R, A x = y} := by
    ext y
    constructor
    · intro hy
      have hy' : y ∈ orbitSubmodule R.toSubalgebra x := hy
      rw [orbitSubmodule, Submodule.mem_map] at hy'
      rcases hy' with ⟨A, hA, hAy⟩
      refine ⟨A, ?_, hAy⟩
      rw [Subalgebra.mem_toSubmodule] at hA
      exact hA
    · intro ⟨A, hA, hAy⟩
      have h_mem : y ∈ orbitSubmodule R.toSubalgebra x := by
        rw [orbitSubmodule, Submodule.mem_map]
        refine ⟨A, ?_, hAy⟩
        rw [Subalgebra.mem_toSubmodule]
        exact hA
      exact h_mem
  have hM_set_eq : (M : Set K) = closure {y : K | ∃ A ∈ R, A x = y} := by
    calc
      (M : Set K) = closure ((orbitSubmodule R.toSubalgebra x : Set K)) := by
        rw [hM, orbitClosure, Submodule.topologicalClosure_coe]
      _ = closure {y : K | ∃ A ∈ R, A x = y} := by rw [h_orbit_set_eq]
  rw [hM_set_eq] at hTx_in_M
  exact hTx_in_M

end Analysis
end LeanEval
