import Mathlib

/-!
Topological facts about the two "type copies" of `B(H)` used in the von Neumann
double commutant theorem: the weak operator topology `ContinuousLinearMapWOT`
(inclusion `ContinuousLinearMapWOT.ofCLM`) and the strong operator topology /
pointwise-convergence topology `PointwiseConvergenceCLM` (inclusion
`ContinuousLinearMap.toPointwiseConvergenceCLM`). Helper file for
`LeanEval.Analysis.VonNeumannDoubleCommutant`.

Note. The ambient Mathlib used here defines `ContinuousLinearMapWOT σ E F` as an
irreducible type copy of `E →SL[σ] F` carrying only the additive/topological
structure of the weak operator topology; it does not register a multiplicative
(ring) structure on the type copy. We therefore transport the ring structure
from `H →L[ℂ] H` along the equivalence `ContinuousLinearMapWOT.equiv.symm`, so
that the multiplication-dependent statements (commutants, `Commute`, …) can be
phrased faithfully on the WOT type copy. The two inclusions `ι_W` and `ι_S` are
recorded as plain equivalences `wotEquiv` and `sotEquiv` (each the underlying map
of the corresponding Mathlib inclusion, i.e. the identity on operators).
-/

namespace LeanEval
namespace Analysis

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The WOT inclusion `ι_W : H →L[ℂ] H → (H →WOT[ℂ] H)` as an equivalence, the
underlying map of `ContinuousLinearMapWOT.ofCLM` (the identity on operators). -/
noncomputable def wotEquiv :
    (H →L[ℂ] H) ≃ (ContinuousLinearMapWOT (RingHom.id ℂ) H H) :=
  ContinuousLinearMapWOT.equiv.symm

/-- The SOT inclusion `ι_S : H →L[ℂ] H → (H →Lₚₜ[ℂ] H)` as an equivalence, the
underlying map of `ContinuousLinearMap.toPointwiseConvergenceCLM` (the identity on
operators). -/
noncomputable def sotEquiv :
    (H →L[ℂ] H) ≃ (PointwiseConvergenceCLM (RingHom.id ℂ) H H) :=
  (ContinuousLinearMap.toUniformConvergenceCLM (𝕜₁ := ℂ) (𝕜₂ := ℂ)
    (σ := RingHom.id ℂ) (E := H) (F := H) {s : Set H | Finite s}).toEquiv

/-- The ring structure on the WOT type copy, transported from `H →L[ℂ] H` along the
inclusion `ι_W`. This is the multiplicative structure under which the WOT inclusion
is a ring homomorphism. -/
noncomputable instance : Ring (ContinuousLinearMapWOT (RingHom.id ℂ) H H) :=
  Equiv.ring (wotEquiv (H := H)).symm

/-- The WOT type copy `ContinuousLinearMapWOT` is a `T2Space` (`lem:wot-t2space`). -/
theorem wot_t2space :
    T2Space (ContinuousLinearMapWOT (RingHom.id ℂ) H H) := by
  infer_instance

/-- Multiplication on the WOT type copy is separately continuous
(`lem:wot-separately-continuous-mul`). -/
theorem wot_separatelyContinuousMul :
    SeparatelyContinuousMul (ContinuousLinearMapWOT (RingHom.id ℂ) H H) where
  continuous_const_mul {a} := by
    refine ContinuousLinearMapWOT.continuous_of_dual_apply_continuous ?_
    intro x y
    exact ContinuousLinearMapWOT.continuous_dual_apply x (y.comp (wotEquiv.symm a))
  continuous_mul_const {a} := by
    refine ContinuousLinearMapWOT.continuous_of_dual_apply_continuous ?_
    intro x y
    exact ContinuousLinearMapWOT.continuous_dual_apply ((wotEquiv.symm a) x) y

/-- For any subset `Y` of the WOT type copy, its centralizer is closed
(`lem:wot-centralizer-closed`). -/
theorem wot_centralizer_isClosed
    (Y : Set (ContinuousLinearMapWOT (RingHom.id ℂ) H H)) :
    IsClosed (Set.centralizer Y) := by
  haveI : T2Space (ContinuousLinearMapWOT (RingHom.id ℂ) H H) := wot_t2space
  haveI : SeparatelyContinuousMul (ContinuousLinearMapWOT (RingHom.id ℂ) H H) :=
    wot_separatelyContinuousMul
  exact Set.isClosed_centralizer Y

/-- The WOT inclusion preserves commuting: `Commute S T` in `B(H)` iff
`Commute (ι_W S) (ι_W T)` in the WOT type copy (`lem:wot-commute-iff`). -/
theorem wot_commute_iff (S T : H →L[ℂ] H) :
    Commute S T ↔
      Commute (wotEquiv (H := H) S) (wotEquiv (H := H) T) := by
  let f : (H →L[ℂ] H) ≃+* (ContinuousLinearMapWOT (RingHom.id ℂ) H H) :=
    (Equiv.ringEquiv (wotEquiv (H := H)).symm).symm
  have hfS (A : H →L[ℂ] H) : f A = wotEquiv A := rfl
  constructor
  · intro h
    have hST : S * T = T * S := h
    calc
      f S * f T = f (S * T) := (f.map_mul S T).symm
      _ = f (T * S) := by rw [hST]
      _ = f T * f S := f.map_mul T S
  · intro h
    have hf_commute : Commute (f S) (f T) := by simpa [hfS] using h
    have h_eq : f (S * T) = f (T * S) := by
      calc
        f (S * T) = f S * f T := f.map_mul S T
        _ = f T * f S := hf_commute
        _ = f (T * S) := (f.map_mul T S).symm
    exact f.injective h_eq

/-- The WOT inclusion preserves commutants: for every `X ⊆ B(H)`,
`ι_W (X') = (ι_W X)'` (`lem:toWOT-centralizer`). -/
theorem toWOT_centralizer (X : Set (H →L[ℂ] H)) :
    (wotEquiv (H := H)) '' (Set.centralizer X) =
      Set.centralizer ((wotEquiv (H := H)) '' X) := by
  ext U
  constructor
  · intro h
    rcases h with ⟨T, hT, rfl⟩
    rw [Set.mem_centralizer_iff] at hT ⊢
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have h_comm : Commute x T := by
      rw [commute_iff_eq]
      exact hT x hx
    rw [← commute_iff_eq]
    exact (wot_commute_iff x T).mp h_comm
  · intro h
    have h_surj : Function.Surjective (wotEquiv (H := H)) := wotEquiv.surjective
    rcases h_surj U with ⟨T, rfl⟩
    refine ⟨T, ?_, rfl⟩
    rw [Set.mem_centralizer_iff]
    intro x hx
    have h_mem : wotEquiv (H := H) x ∈ (wotEquiv (H := H)) '' X :=
      (Set.mem_image (wotEquiv (H := H)) X (wotEquiv (H := H) x)).mpr ⟨x, hx, rfl⟩
    have h_central := (Set.mem_centralizer_iff.mp h) (wotEquiv (H := H) x) h_mem
    rw [← commute_iff_eq]
    apply (wot_commute_iff x T).mpr
    rw [commute_iff_eq]
    exact h_central

/-- `(1) ⇒ (2)`: if `S'' = S` then the WOT image of `S` is closed
(`lem:dct-wot-closed`). -/
theorem dct_wot_closed (S : Set (H →L[ℂ] H))
    (hS : Set.centralizer (Set.centralizer S) = S) :
    IsClosed ((wotEquiv (H := H)) '' S) := by
  have hcalc : (wotEquiv (H := H)) '' S =
      Set.centralizer (Set.centralizer ((wotEquiv (H := H)) '' S)) := by
    calc
      (wotEquiv (H := H)) '' S =
          (wotEquiv (H := H)) '' (Set.centralizer (Set.centralizer S)) := by
        rw [hS]
      _ = Set.centralizer ((wotEquiv (H := H)) '' (Set.centralizer S)) := by
        rw [toWOT_centralizer]
      _ = Set.centralizer (Set.centralizer ((wotEquiv (H := H)) '' S)) := by
        rw [toWOT_centralizer]
  rw [hcalc]
  exact wot_centralizer_isClosed (Set.centralizer ((wotEquiv (H := H)) '' S))

/-- Each WOT pairing `T ↦ ⟪T x, y⟫` is continuous on the SOT type copy
(`lem:sot-pairing-continuous`). The element `T` of the SOT type copy is evaluated
through its underlying operator via `ι_S⁻¹`. -/
theorem sot_pairing_continuous (x y : H) :
    Continuous (fun T : PointwiseConvergenceCLM (RingHom.id ℂ) H H =>
      (inner ℂ ((sotEquiv (H := H)).symm T x) y : ℂ)) := by
  have h_eval : Continuous (fun T : PointwiseConvergenceCLM (RingHom.id ℂ) H H => T x) :=
    continuous_eval_const x
  have h_comp : Continuous (fun T : PointwiseConvergenceCLM (RingHom.id ℂ) H H => (sotEquiv (H := H)).symm T x) := by
    have hfun : (fun T : PointwiseConvergenceCLM (RingHom.id ℂ) H H =>
        (sotEquiv (H := H)).symm T x) = fun T => T x := by
      funext T
      change ((ContinuousLinearMap.toUniformConvergenceCLM (RingHom.id ℂ) H
        {s : Set H | Finite s}).symm T) x = T x
      exact ContinuousLinearMap.toUniformConvergenceCLM_symm_apply
    rw [hfun]
    exact h_eval
  have h_const : Continuous (fun (_ : PointwiseConvergenceCLM (RingHom.id ℂ) H H) => y) :=
    continuous_const
  exact (h_comp.inner h_const)

/-- The "identity on underlying operators" map from the SOT type copy to the WOT
type copy: it sends `ι_S T` to `ι_W T`. This is the continuous map `φ` of
`lem:continuous-sot-wot`; concretely it is `ι_W ∘ ι_S⁻¹`. -/
noncomputable def sotToWot (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    : PointwiseConvergenceCLM (RingHom.id ℂ) H H →
      ContinuousLinearMapWOT (RingHom.id ℂ) H H :=
  fun T => wotEquiv (H := H) ((sotEquiv (H := H)).symm T)

/-- `φ ∘ ι_S = ι_W` on underlying operators: the SOT-to-WOT map agrees with the WOT
inclusion after precomposition with the SOT inclusion (`lem:continuous-sot-wot`). -/
theorem sotToWot_sotEquiv (T : H →L[ℂ] H) :
    sotToWot H (sotEquiv (H := H) T) = wotEquiv (H := H) T := by
  simp [sotToWot]

/-- The SOT is finer than the WOT: the identity map `φ = sotToWot` from the SOT
type copy to the WOT type copy is continuous (`lem:continuous-sot-wot`). -/
theorem continuous_sotToWot [CompleteSpace H] :
    Continuous (sotToWot H) := by
  -- The WOT topology on ContinuousLinearMapWOT is induced by the family of
  -- pairings A ↦ y' (A x).  By continuous_of_dual_apply_continuous it suffices
  -- to show each such pairing is SOT-continuous.
  apply ContinuousLinearMapWOT.continuous_of_dual_apply_continuous
  intro x y'
  -- By the Riesz representation theorem every y' : StrongDual ℂ H equals
  -- innerSL ℂ z for some z : H.
  obtain ⟨z, hz⟩ := (InnerProductSpace.toDual (𝕜 := ℂ) (E := H)).surjective y'
  have hy'_apply (v : H) : y' v = inner ℂ z v := by
    calc
      y' v = (InnerProductSpace.toDual ℂ H z) v := by rw [hz]
      _ = (InnerProductSpace.toDualMap ℂ H z) v := rfl
      _ = inner ℂ z v := rfl
  have h_sotToWot_apply (T : PointwiseConvergenceCLM (RingHom.id ℂ) H H) (v : H) :
      (sotToWot H T) v = ((sotEquiv (H := H)).symm T) v := by
    rfl
  have h_inner_conj (T : PointwiseConvergenceCLM (RingHom.id ℂ) H H) :
      y' ((sotToWot H T) x) = starRingEnd ℂ (inner ℂ ((sotEquiv (H := H)).symm T x) z) := by
    calc
      y' ((sotToWot H T) x) = y' (((sotEquiv (H := H)).symm T) x) := by rw [h_sotToWot_apply]
      _ = inner ℂ z (((sotEquiv (H := H)).symm T) x) := hy'_apply _
      _ = (starRingEnd ℂ) (inner ℂ (((sotEquiv (H := H)).symm T) x) z) := by rw [inner_conj_symm]
  -- The function T ↦ y' ((sotToWot H T) x) is continuous
  have h_cont_inner : Continuous (fun T : PointwiseConvergenceCLM (RingHom.id ℂ) H H =>
      inner ℂ ((sotEquiv (H := H)).symm T x) z) :=
    sot_pairing_continuous x z
  have h_cont : Continuous (fun (T : PointwiseConvergenceCLM (RingHom.id ℂ) H H) =>
      y' ((sotToWot H T) x)) := by
    -- rewrite using the equality h_inner_conj
    have : (fun T : PointwiseConvergenceCLM (RingHom.id ℂ) H H => y' ((sotToWot H T) x))
        = (starRingEnd ℂ) ∘ (fun T : PointwiseConvergenceCLM (RingHom.id ℂ) H H =>
            inner ℂ ((sotEquiv (H := H)).symm T x) z) := by
      ext T; exact h_inner_conj T
    rw [this]
    exact (continuous_star : Continuous (starRingEnd ℂ)).comp h_cont_inner
  exact h_cont

/-- The SOT image is a preimage of the WOT image under `φ = sotToWot`: for every
`X ⊆ B(H)`, `ι_S X = φ⁻¹ (ι_W X)` (`lem:sot-image-eq-preimage`). -/
theorem sot_image_eq_preimage (X : Set (H →L[ℂ] H)) :
    (sotEquiv (H := H)) '' X =
      (sotToWot H) ⁻¹' ((wotEquiv (H := H)) '' X) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp [sotToWot_sotEquiv, hx]
  · intro hz
    rcases hz with ⟨x, hx, h⟩
    set y := (sotEquiv (H := H)).symm z with hy
    have hz_eq : z = sotEquiv (H := H) y := by
      simp [hy]
    have h_eq : wotEquiv (H := H) y = wotEquiv (H := H) x := by
      calc
        wotEquiv (H := H) y = sotToWot H (sotEquiv (H := H) y) := by
          symm; exact sotToWot_sotEquiv _
        _ = sotToWot H z := by rw [hz_eq]
        _ = wotEquiv (H := H) x := h.symm
    have hyx : y = x := (wotEquiv (H := H)).injective h_eq
    have hy_mem : y ∈ X := by
      rw [hyx]
      exact hx
    exact ⟨y, hy_mem, hz_eq⟩

/-- `(2) ⇒ (3)`: if the WOT image of `S` is closed, then its SOT image is closed
(`lem:wot-closed-imp-sot-closed`). -/
theorem wot_closed_imp_sot_closed (S : Set (H →L[ℂ] H))
    [CompleteSpace H]
    (hS : IsClosed ((wotEquiv (H := H)) '' S)) :
    IsClosed ((sotEquiv (H := H)) '' S) := by
  rw [sot_image_eq_preimage]
  exact hS.preimage (continuous_sotToWot (H := H))

end Analysis
end LeanEval
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

omit [CompleteSpace H] in
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

omit [CompleteSpace H] in
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
          simp
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
        simp
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
        simp
      _ = C v := by
        rw [h_sum_id, ContinuousLinearMap.id_apply]

omit [CompleteSpace H] in
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

omit [CompleteSpace H] in
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

omit [CompleteSpace H] in
/-- The identity `(ampSingle j) x = PiLp.single 2 j x`, pointwise. -/
lemma ampSingle_apply_eq (j : Fin n) (x : H) : (ampSingle j) x = PiLp.single 2 j x := by
  calc
    (ampSingle j) x = ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm
      (ContinuousLinearMap.single ℂ (fun _ : Fin n => H) j x)) := rfl
    _ = (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm (Pi.single j x) := by
      simp
    _ = PiLp.single 2 j x := by
      rw [PiLp.continuousLinearEquiv_symm_apply, PiLp.single]

omit [CompleteSpace H] in
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

omit [CompleteSpace H] in
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

omit [CompleteSpace H] in
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
/-!
# Finite-family approximation and the SOT closure

This file completes the hard implication of von Neumann's double commutant
theorem. It bridges the single-vector approximation (`single_vector_approx` in
`Orbit.lean`) to a finite-family statement via the diagonal amplification
(`Amplification.lean`, `Blocks.lean`), and then translates the approximation
property into membership in the strong operator topology (SOT) closure.

Blueprint labels: `lem:coord-norm-le` through `lem:sot-closed-mem`.
-/

namespace LeanEval
namespace Analysis

open scoped ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {n : ℕ}

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
/-- `lem:coord-norm-le`: for `v ∈ H^n = PiLp 2 (fun _ : Fin n => H)` and any index
`i`, the coordinate norm is bounded by the `ℓ²` norm, `‖v_i‖ ≤ ‖v‖`. -/
theorem coord_norm_le (v : PiLp 2 (fun _ : Fin n => H)) (i : Fin n) :
    ‖v.ofLp i‖ ≤ ‖v‖ :=
  PiLp.norm_apply_le v i

/-- `lem:closure-coord-approx`: if the vector `(T x_i)_i ∈ H^n` lies in the closure
of `{(A x_i)_i : A ∈ S}`, then for every `ε > 0` there is `A ∈ S` with
`‖T x_i - A x_i‖ < ε` for all `i`. -/
theorem closure_coord_approx (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (T : H →L[ℂ] H) (x : Fin n → H)
    (hmem : (WithLp.toLp 2 (fun i => T (x i)) : PiLp 2 (fun _ : Fin n => H)) ∈
      closure {y : PiLp 2 (fun _ : Fin n => H) |
        ∃ A ∈ S, (WithLp.toLp 2 (fun i => A (x i))) = y})
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A ∈ S, ∀ i : Fin n, ‖T (x i) - A (x i)‖ < ε := by
  have hm_iff := (Metric.mem_closure_iff).mp hmem
  have h_ex := hm_iff ε hε
  rcases h_ex with ⟨y, hy, hdist⟩
  rcases hy with ⟨A, hA, hy_eq⟩
  refine ⟨A, hA, λ i => ?_⟩
  have h_norm : ‖(WithLp.toLp 2 (fun i => T (x i)) - WithLp.toLp 2 (fun i => A (x i)))‖ < ε := by
    simpa [hy_eq, dist_eq_norm] using hdist
  have h_coord : ‖((WithLp.toLp 2 (fun i => T (x i)) - WithLp.toLp 2 (fun i => A (x i))).ofLp i)‖ < ε :=
    lt_of_le_of_lt (coord_norm_le _ i) h_norm
  simpa using h_coord

/-- `lem:double-commutant-approx`: for `T ∈ S''`, a finite family `x : Fin n → H`
and `ε > 0`, there exists `A ∈ S` with `‖T x_i - A x_i‖ < ε` for all `i`. This is
the key bridge from the single-vector approximation to finitely many vectors,
obtained by amplification. -/
theorem double_commutant_approx (S : StarSubalgebra ℂ (H →L[ℂ] H))
    {T : H →L[ℂ] H}
    (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (x : Fin n → H) {ε : ℝ} (hε : 0 < ε) :
    ∃ A ∈ S, ∀ i : Fin n, ‖T (x i) - A (x i)‖ < ε := by
  -- ξ = (x_i)_i in H^n
  set ξ : PiLp 2 (fun _ : Fin n => H) := WithLp.toLp 2 (fun i : Fin n => x i) with hξ
  -- R := Δ(S)
  set R := amplificationSubalgebra (n := n) S with hR
  -- Show Δ(T) ∈ R''
  have hT_amp : amplificationMap (n := n) T ∈ Set.centralizer (Set.centralizer (R : Set _)) := by
    exact amplification_double_commutant (n := n) S T hT
  -- Apply single_vector_approx: Δ(T) ξ ∈ closure {A ξ | A ∈ R}
  have h_sva : amplificationMap (n := n) T ξ ∈
      closure {y : PiLp 2 (fun _ : Fin n => H) | ∃ A ∈ R, A ξ = y} :=
    single_vector_approx R hT_amp ξ
  -- Lemma: amplificationMap A ξ = WithLp.toLp (A (x i))_i
  have h_amp_eq (A : H →L[ℂ] H) : amplificationMap A ξ = (WithLp.toLp 2 (fun i : Fin n => A (x i)) : PiLp 2 (fun _ : Fin n => H)) := by
    apply (PiLp.ext_iff (p := 2) (ι := Fin n) (α := fun _ : Fin n => H)).mpr
    intro i
    simp [amplificationMap_apply, ξ, hξ]
  -- The closure set in h_sva equals the closure set needed for closure_coord_approx
  have h_set_eq : {y : PiLp 2 (fun _ : Fin n => H) | ∃ A ∈ R, A ξ = y} =
      {y : PiLp 2 (fun _ : Fin n => H) | ∃ A₀ ∈ S, (WithLp.toLp 2 (fun i : Fin n => A₀ (x i))) = y} := by
    ext y
    constructor
    · intro ⟨A, hA, hAy⟩
      rw [hR, amplificationSubalgebra, StarSubalgebra.mem_map] at hA
      rcases hA with ⟨A₀, hA₀S, hA_eq⟩
      have hA_eq' : amplificationMap A₀ = A := by
        change amplificationMap A₀ = A at hA_eq
        exact hA_eq
      refine ⟨A₀, hA₀S, ?_⟩
      rw [← hA_eq'] at hAy
      rw [h_amp_eq A₀] at hAy
      exact hAy
    · intro ⟨A₀, hA₀S, hy⟩
      have hA₀R : amplificationMap A₀ ∈ R := by
        rw [hR, amplificationSubalgebra]
        apply StarSubalgebra.mem_map.mpr
        exact ⟨A₀, hA₀S, rfl⟩
      refine ⟨amplificationMap A₀, hA₀R, ?_⟩
      calc
        amplificationMap A₀ ξ = (WithLp.toLp 2 (fun i : Fin n => A₀ (x i)) : PiLp 2 (fun _ : Fin n => H)) := h_amp_eq A₀
        _ = y := hy
  -- Combine to get the membership needed by closure_coord_approx
  rw [h_set_eq] at h_sva
  have h_mem : (WithLp.toLp 2 (fun i => T (x i)) : PiLp 2 (fun _ : Fin n => H)) ∈
      closure {y : PiLp 2 (fun _ : Fin n => H) | ∃ A ∈ S, (WithLp.toLp 2 (fun i => A (x i))) = y} := by
    rw [← h_amp_eq T]
    exact h_sva
  -- Apply the coordinate-wise approximation lemma
  exact closure_coord_approx S T x h_mem hε

omit [CompleteSpace H] in
/-- `lem:sot-nhds-zero-basis`: in the SOT type copy `PointwiseConvergenceCLM`, the
neighbourhood filter of `0` has a basis given by the sets
`W_{x, ε} = {U | ∀ i, ‖U (x i)‖ < ε}`, indexed by finite families
`x : Fin n → H` and reals `ε > 0`. -/
theorem sot_hasBasis_nhds_zero :
    (nhds (0 : PointwiseConvergenceCLM (RingHom.id ℂ) H H)).HasBasis
      (fun p : Σ n : ℕ, (Fin n → H) × ℝ => 0 < p.2.2)
      (fun p : Σ n : ℕ, (Fin n → H) × ℝ =>
        {U : PointwiseConvergenceCLM (RingHom.id ℂ) H H | ∀ i, ‖U (p.2.1 i)‖ < p.2.2}) := by
  have hbasis := PointwiseConvergenceCLM.hasBasis_nhds_zero (E := H) (F := H) (σ := RingHom.id ℂ)
  apply Filter.HasBasis.mk
  intro t
  constructor
  · intro ht
    rcases hbasis.mem_iff.mp ht with ⟨⟨F, V⟩, ⟨hFfin, hV0⟩, hsub⟩
    rcases Metric.mem_nhds_iff.mp hV0 with ⟨ε, hε, hball⟩
    haveI : Fintype (F : Set H) := Set.Finite.fintype hFfin
    let n := Fintype.card (F : Set H)
    let e : (F : Set H) ≃ Fin n := Fintype.equivFin (F : Set H)
    let x : Fin n → H := λ i => ((e.symm i : (F : Set H)).val : H)
    refine ⟨⟨n, (x, ε)⟩, hε, ?_⟩
    intro U hU
    apply hsub
    intro y hy
    have hy' : U y ∈ Metric.ball (0 : H) ε := by
      have hy_range : y ∈ Set.range x := by
        let y' : (F : Set H) := ⟨y, hy⟩
        let i : Fin n := e y'
        refine ⟨i, ?_⟩
        dsimp [x, i, y']
        have : e.symm (e ⟨y, hy⟩) = ⟨y, hy⟩ := Equiv.symm_apply_apply e ⟨y, hy⟩
        simp
      rcases hy_range with ⟨i, hi⟩
      have hUi : ‖U (x i)‖ < ε := hU i
      have hUy : U y = U (x i) := by rw [hi]
      rw [hUy]
      apply Metric.mem_ball.mpr
      simpa [dist_eq_norm] using hUi
    exact hball hy'
  · intro h
    rcases h with ⟨p, hp, hsub⟩
    rcases p with ⟨n, xε⟩
    rcases xε with ⟨x, ε⟩
    have hε : 0 < ε := hp
    have hfin : Finite (Set.range x) := Set.finite_range x
    have hball_mem : Metric.ball (0 : H) ε ∈ nhds (0 : H) := Metric.ball_mem_nhds (0 : H) hε
    have hmem : {U : PointwiseConvergenceCLM (RingHom.id ℂ) H H |
      ∀ y ∈ Set.range x, U y ∈ Metric.ball (0 : H) ε} ∈ nhds (0 : _) :=
      hbasis.mem_iff.mpr ⟨(Set.range x, Metric.ball 0 ε), ⟨hfin, hball_mem⟩, Set.Subset.refl _⟩
    have h_eq : {U : PointwiseConvergenceCLM (RingHom.id ℂ) H H |
      ∀ y ∈ Set.range x, U y ∈ Metric.ball (0 : H) ε} =
      {U : PointwiseConvergenceCLM (RingHom.id ℂ) H H | ∀ i, ‖U (x i)‖ < ε} := by
      ext U
      constructor
      · intro hU i
        have hball : U (x i) ∈ Metric.ball (0 : H) ε := hU (x i) ⟨i, rfl⟩
        simpa [dist_eq_norm] using Metric.mem_ball.mp hball
      · intro hU y hy
        rcases hy with ⟨i, rfl⟩
        simpa [dist_eq_norm] using hU i
    rw [h_eq] at hmem
    exact Filter.mem_of_superset hmem hsub

omit [CompleteSpace H] in
/-- `lem:sot-nhds-basis`: for `T₀` in the SOT type copy, the neighbourhood filter of
`T₀` has a basis given by the sets `V_{x, ε} = {U | ∀ i, ‖U (x i) - T₀ (x i)‖ < ε}`,
indexed by finite families `x : Fin n → H` and reals `ε > 0`. -/
theorem sot_hasBasis_nhds (T₀ : PointwiseConvergenceCLM (RingHom.id ℂ) H H) :
    (nhds T₀).HasBasis
      (fun p : Σ n : ℕ, (Fin n → H) × ℝ => 0 < p.2.2)
      (fun p : Σ n : ℕ, (Fin n → H) × ℝ =>
        {U : PointwiseConvergenceCLM (RingHom.id ℂ) H H |
          ∀ i, ‖U (p.2.1 i) - T₀ (p.2.1 i)‖ < p.2.2}) := by
  have hzero : (nhds (0 : PointwiseConvergenceCLM (RingHom.id ℂ) H H)).HasBasis
    (fun p : Σ n : ℕ, (Fin n → H) × ℝ => 0 < p.2.2)
    (fun p : Σ n : ℕ, (Fin n → H) × ℝ =>
      {U : PointwiseConvergenceCLM (RingHom.id ℂ) H H | ∀ i, ‖U (p.2.1 i)‖ < p.2.2}) :=
    sot_hasBasis_nhds_zero
  have h_trans : Filter.map (T₀ + ·) (nhds (0 : PointwiseConvergenceCLM (RingHom.id ℂ) H H)) = nhds T₀ := by
    calc
      Filter.map (T₀ + ·) (nhds (0 : PointwiseConvergenceCLM (RingHom.id ℂ) H H)) = nhds ((T₀ + ·) (0 : _)) :=
        (Homeomorph.addLeft T₀).map_nhds_eq 0
      _ = nhds T₀ := by simp
  have hbasis' : (nhds T₀).HasBasis
    (fun p : Σ n : ℕ, (Fin n → H) × ℝ => 0 < p.2.2)
    (fun p => (T₀ + ·) '' {U : PointwiseConvergenceCLM (RingHom.id ℂ) H H |
      ∀ i, ‖U (p.2.1 i)‖ < p.2.2}) := by
    simpa [h_trans] using hzero.map (T₀ + ·)
  have hs_eq : ∀ p, (fun p' : Σ n : ℕ, (Fin n → H) × ℝ => 0 < p'.2.2) p →
    ((T₀ + ·) '' {U : PointwiseConvergenceCLM (RingHom.id ℂ) H H | ∀ i, ‖U (p.2.1 i)‖ < p.2.2}) =
    {U : PointwiseConvergenceCLM (RingHom.id ℂ) H H | ∀ i, ‖U (p.2.1 i) - T₀ (p.2.1 i)‖ < p.2.2} := by
    intro p hp
    ext V
    constructor
    · rintro ⟨U, hU, rfl⟩
      intro i
      have hUi := hU i
      simpa [sub_self, add_sub_cancel_right] using hUi
    · intro hV
      refine ⟨V - T₀, ?_, ?_⟩
      · intro i
        simpa [sub_eq_add_neg] using hV i
      · simp
  exact hbasis'.congr (fun i => Iff.rfl) hs_eq

/-- `lem:sot-closure-membership`: an operator `T` satisfies
`ι_S T ∈ closure (ι_S '' S)` in the SOT type copy iff for every finite family
`x : Fin n → H` and every `ε > 0` there is `A ∈ S` with `‖T x_i - A x_i‖ < ε` for
all `i`. Here `ι_S = ContinuousLinearMap.toPointwiseConvergenceCLM`. -/
theorem sot_closure_membership (S : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H) :
    ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H T ∈
        closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
          (S : Set (H →L[ℂ] H))) ↔
      ∀ (n : ℕ) (x : Fin n → H) {ε : ℝ}, 0 < ε →
        ∃ A ∈ S, ∀ i : Fin n, ‖T (x i) - A (x i)‖ < ε := by
  let ι := ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
  have hι_apply (f : H →L[ℂ] H) (v : H) : (ι f) v = f v :=
    congrArg (· v) (ContinuousLinearMap.toPointwiseConvergenceCLM_apply ℂ (RingHom.id ℂ) H H f)
  have hbasis : (nhds (ι T)).HasBasis (fun p : Σ n : ℕ, (Fin n → H) × ℝ => 0 < p.2.2)
      (fun p : Σ n : ℕ, (Fin n → H) × ℝ => {U | ∀ i, ‖U (p.2.1 i) - (ι T) (p.2.1 i)‖ < p.2.2}) :=
    sot_hasBasis_nhds (ι T)
  rw [mem_closure_iff_nhds_basis' hbasis]
  constructor
  · intro h n x ε hε
    have h_nonempty : ({U | ∀ i, ‖U (x i) - (ι T) (x i)‖ < ε} ∩ (ι '' (S : Set (H →L[ℂ] H)))).Nonempty :=
      h ⟨n, (x, ε)⟩ hε
    rcases h_nonempty with ⟨U, hUmn⟩
    have hUV : U ∈ {U | ∀ i, ‖U (x i) - (ι T) (x i)‖ < ε} := hUmn.1
    have hUimg : U ∈ ι '' (S : Set (H →L[ℂ] H)) := hUmn.2
    rcases hUimg with ⟨A, hA, hA_eq⟩
    refine ⟨A, hA, λ i => ?_⟩
    have hU_V_i : ‖U (x i) - (ι T) (x i)‖ < ε := hUV i
    have h_inner : ‖A (x i) - T (x i)‖ = ‖(ι A) (x i) - (ι T) (x i)‖ := by
      simp [hι_apply]
    have h_eq : ‖T (x i) - A (x i)‖ = ‖U (x i) - (ι T) (x i)‖ := by
      rw [norm_sub_rev, h_inner, hA_eq]
    rw [h_eq]
    exact hU_V_i
  · intro h p hp
    rcases p with ⟨n, xε⟩
    rcases xε with ⟨x, ε⟩
    have hε_pos : 0 < ε := hp
    have h_ex : ∃ A ∈ S, ∀ i : Fin n, ‖T (x i) - A (x i)‖ < ε := h n x (ε := ε) hε_pos
    rcases h_ex with ⟨A, hA, h_approx⟩
    refine ⟨ι A, λ i => ?_, ⟨A, hA, rfl⟩⟩
    have h_eq : ‖(ι A) (x i) - (ι T) (x i)‖ = ‖T (x i) - A (x i)‖ := by
      simp [hι_apply, norm_sub_rev]
    rw [h_eq]
    exact h_approx i

/-- `lem:sot-closed-mem`: if the SOT image `ι_S '' S` is closed and `T` satisfies the
finite-family approximation property, then `T ∈ S`. -/
theorem sot_closed_mem (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (hclosed : IsClosed (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
      (S : Set (H →L[ℂ] H))))
    (T : H →L[ℂ] H)
    (happrox : ∀ (n : ℕ) (x : Fin n → H) {ε : ℝ}, 0 < ε →
      ∃ A ∈ S, ∀ i : Fin n, ‖T (x i) - A (x i)‖ < ε) :
    T ∈ S := by
  let f := ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
  have hmemsot : f T ∈ closure (f '' (S : Set (H →L[ℂ] H))) :=
    ((sot_closure_membership S T).mpr happrox)
  have hsubset : closure (f '' (S : Set (H →L[ℂ] H))) ⊆ f '' (S : Set (H →L[ℂ] H)) :=
    IsClosed.closure_subset hclosed
  rcases hsubset hmemsot with ⟨A, hA, h_eq⟩
  have h_inj : Function.Injective (f : (H →L[ℂ] H) → PointwiseConvergenceCLM (RingHom.id ℂ) H H) := by
    intro x y h
    apply (ContinuousLinearMap.toUniformConvergenceCLM (RingHom.id ℂ) H
      {s : Set H | Finite s}).injective
    exact h
  have hTA : T = A := h_inj h_eq.symm
  rw [hTA]
  exact hA

end Analysis
end LeanEval
namespace LeanEval
namespace Analysis

/-!
Von Neumann's double commutant theorem.

For a unital *-subalgebra `S` of bounded operators on a complex Hilbert space `H`, the
following are equivalent:

1. `S` equals its double commutant `S''`.
2. `S` is closed in the weak operator topology.
3. `S` is closed in the strong operator topology (in Mathlib, the topology of pointwise
   convergence on continuous linear maps).

The WOT and SOT live on irreducible type copies of `H →L[ℂ] H`, so each closed-ness
condition is stated as the closedness of the image of `S` under the canonical inclusion
into the corresponding type copy.
-/

/-- `(3) ⇒ (1)`: if the SOT image of `S` (the image under
`ContinuousLinearMap.toPointwiseConvergenceCLM`) is closed, then `S` equals its
double commutant, `S'' = S`. Blueprint label `thm:sot-imp-dct`. -/
theorem sot_imp_dct
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (hS : IsClosed
      (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        (S : Set (H →L[ℂ] H)))) :
    Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) = (S : Set (H →L[ℂ] H)) := by
  apply Set.Subset.antisymm
  · -- S'' ⊆ S
    intro T hT
    apply sot_closed_mem S hS T
    intro n x ε hε
    exact double_commutant_approx S hT x hε
  · -- S ⊆ S''
    exact Set.subset_centralizer_centralizer (S := (S : Set (H →L[ℂ] H)))



end Analysis
end LeanEval
