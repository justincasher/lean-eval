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
  let d := Module.finrank R M
  let b := Module.finBasis R M
  haveI : FiniteDimensional R (⨂[R]^k M) :=
    Module.Finite.of_basis (Basis.piTensorProduct (fun _ : Fin k => b))
  haveI : FiniteDimensional R (Module.End R (⨂[R]^k M)) :=
    Module.Finite.of_basis (Module.Basis.end (Basis.piTensorProduct (fun _ : Fin k => b)))
  haveI : FiniteDimensional R (Module.End R M) :=
    Module.Finite.of_basis (Module.Basis.end b)
  haveI : FiniteDimensional R (⨂[R]^k (Module.End R M)) :=
    Module.Finite.of_basis (Basis.piTensorProduct (fun _ : Fin k => (Module.Basis.end b)))
  -- finrank R (⨂[R]^k M) = d ^ k
  have hdimVk : Module.finrank R (⨂[R]^k M) = d ^ k := by
    let bVk := Basis.piTensorProduct (fun _ : Fin k => b)
    have hcard : Fintype.card (Π _ : Fin k, Fin d) = d ^ k := by
      simp
    calc
      Module.finrank R (⨂[R]^k M) = Fintype.card (Π _ : Fin k, Fin d) :=
        Module.finrank_eq_card_basis bVk
      _ = d ^ k := hcard
  -- finrank R (End R (⨂[R]^k M)) = (d ^ k) ^ 2 = d ^ (2 * k)
  have hdimEndVk : Module.finrank R (Module.End R (⨂[R]^k M)) = d ^ (2 * k) := by
    calc
      Module.finrank R (Module.End R (⨂[R]^k M)) =
        Module.finrank R (⨂[R]^k M) * Module.finrank R (⨂[R]^k M) := by
        simpa using Module.finrank_linearMap R R (⨂[R]^k M) (⨂[R]^k M)
      _ = (d ^ k) * (d ^ k) := by rw [hdimVk]
      _ = d ^ (2 * k) := by ring
  -- finrank R (End R M) = d ^ 2
  have hdimEndM : Module.finrank R (Module.End R M) = d ^ 2 := by
    calc
      Module.finrank R (Module.End R M) =
        Module.finrank R M * Module.finrank R M := by
        simpa using Module.finrank_linearMap R R M M
      _ = d * d := by rfl
      _ = d ^ 2 := by ring
  -- finrank R (⨂[R]^k (End R M)) = (d ^ 2) ^ k = d ^ (2 * k)
  have hdimTensorEnd : Module.finrank R (⨂[R]^k (Module.End R M)) = d ^ (2 * k) := by
    let bEnd := Module.finBasis R (Module.End R M)
    let bEndTensor := Basis.piTensorProduct (fun _ : Fin k => bEnd)
    have hcardEnd : Fintype.card (Π _ : Fin k, Fin (Module.finrank R (Module.End R M))) =
      (Module.finrank R (Module.End R M)) ^ k := by
      simp
    calc
      Module.finrank R (⨂[R]^k (Module.End R M)) =
        Fintype.card (Π _ : Fin k, Fin (Module.finrank R (Module.End R M))) :=
        Module.finrank_eq_card_basis bEndTensor
      _ = (Module.finrank R (Module.End R M)) ^ k := hcardEnd
      _ = (d ^ 2) ^ k := by rw [hdimEndM]
      _ = d ^ (2 * k) := by ring
  -- combine
  calc
    Module.finrank R (⨂[R]^k (Module.End R M)) = d ^ (2 * k) := hdimTensorEnd
    _ = Module.finrank R (Module.End R (⨂[R]^k M)) := by symm; exact hdimEndVk

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
  classical
  haveI : Module.Finite R M := inferInstance
  haveI : Module.Free R M := Module.Free.of_basis (Module.Free.chooseBasis R M)
  set S := {t : R | ¬ IsUnit (m + t • (1 : Module.End R M))} with hS
  let p := m.charpoly
  have hp_monic : p.Monic := m.charpoly_monic
  have hp_ne_zero : p ≠ 0 := hp_monic.ne_zero
  have h_natDegree : Polynomial.natDegree p = Module.finrank R M := m.charpoly_natDegree
  -- The equivalence: t ∈ S ↔ p.eval (-t) = 0
  have h_mem_iff (t : R) : t ∈ S ↔ p.eval (-t) = 0 := by
    rw [hS, Set.mem_setOf_eq]
    have hdet_eq_zero_iff : LinearMap.det (m + t • (1 : Module.End R M)) = 0 ↔ p.eval (-t) = 0 := by
      have h_eval : p.eval (-t) = LinearMap.det ((algebraMap R (Module.End R M) (-t)) - m) := by
        rw [LinearMap.eval_charpoly m (-t)]
      have h_eq : (algebraMap R (Module.End R M) (-t)) - m = -(m + t • (1 : Module.End R M)) := by
        ext x; simp [sub_eq_add_neg, smul_neg]
      have h_det_neg : LinearMap.det (-(m + t • (1 : Module.End R M))) =
        (-1 : R) ^ Module.finrank R M * LinearMap.det (m + t • (1 : Module.End R M)) := by
        simpa [add_comm, add_left_comm, add_assoc] using
          LinearMap.det_smul (-1 : R) (m + t • (1 : Module.End R M))
      constructor
      · intro hdet0
        calc
          p.eval (-t) = LinearMap.det ((algebraMap R (Module.End R M) (-t)) - m) := h_eval
          _ = LinearMap.det (-(m + t • (1 : Module.End R M))) := by rw [h_eq]
          _ = (-1 : R) ^ Module.finrank R M * LinearMap.det (m + t • (1 : Module.End R M)) := h_det_neg
          _ = (-1 : R) ^ Module.finrank R M * 0 := by rw [hdet0]
          _ = 0 := by ring
      · intro hpeval0
        have h_det_neg_zero : LinearMap.det (-(m + t • (1 : Module.End R M))) = 0 := by
          calc
            LinearMap.det (-(m + t • (1 : Module.End R M))) =
              LinearMap.det ((algebraMap R (Module.End R M) (-t)) - m) := by rw [h_eq]
            _ = p.eval (-t) := h_eval.symm
            _ = 0 := hpeval0
        rw [h_det_neg] at h_det_neg_zero
        have h_pow_ne_zero : (-1 : R) ^ Module.finrank R M ≠ 0 :=
          pow_ne_zero (Module.finrank R M) (by norm_num : (-1 : R) ≠ 0)
        apply mul_eq_zero.mp at h_det_neg_zero
        rcases h_det_neg_zero with (h_pow | hdet')
        · exact absurd h_pow h_pow_ne_zero
        · exact hdet'
    -- ¬ IsUnit f ↔ det f = 0 (since R is a field)
    have h_nonunit_iff_det_zero : ¬ IsUnit (m + t • (1 : Module.End R M)) ↔
      LinearMap.det (m + t • (1 : Module.End R M)) = 0 := by
      rw [LinearMap.isUnit_iff_isUnit_det (m + t • (1 : Module.End R M)), isUnit_iff_ne_zero, not_ne_iff]
    rw [h_nonunit_iff_det_zero, hdet_eq_zero_iff]
  -- S = {t | p.eval (-t) = 0} by the above equivalence
  have hS_eq : S = {t | p.eval (-t) = 0} := by
    ext t; rw [h_mem_iff t, Set.mem_setOf_eq]
  -- S is finite because the set of roots of p is finite and negation is a bijection
  let Rset : Set R := {r | p.eval r = 0}
  have hRset_finite : Rset.Finite := Polynomial.finite_setOf_isRoot hp_ne_zero
  have hS_eq_image : {t | p.eval (-t) = 0} = (-·) '' Rset := by
    ext t; simp [Rset, Set.mem_image, eq_comm]
  have hfinite : S.Finite := by
    rw [hS_eq, hS_eq_image]
    exact hRset_finite.image (fun x : R => -x)
  -- The cardinality bound
  have hcard : S.ncard ≤ Module.finrank R M := by
    rw [hS_eq, hS_eq_image]
    -- Since negation is injective, ncard of image = ncard of original set
    have h_image_ncard : ((-·) '' Rset).ncard = Rset.ncard :=
      Set.ncard_image_of_injective Rset (fun x y h => by simpa using h)
    rw [h_image_ncard]
    -- Rset.ncard = |roots(p).toFinset| ≤ Multiset.card (roots p) ≤ natDegree p = finrank
    have hRset_ncard_eq : Rset.ncard = (p.roots.toFinset).card := by
      have hRset_toFinset : hRset_finite.toFinset = p.roots.toFinset := by
        ext r; simp [Rset, Polynomial.mem_roots hp_ne_zero]
      rw [Set.ncard_eq_toFinset_card Rset hRset_finite, hRset_toFinset]
    rw [hRset_ncard_eq]
    calc
      (p.roots.toFinset).card ≤ Multiset.card p.roots :=
        Multiset.toFinset_card_le (m := p.roots)
      _ ≤ Polynomial.natDegree p := Polynomial.card_roots' p
      _ = Module.finrank R M := h_natDegree
  exact And.intro hfinite hcard

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
  ext x
  constructor
  · intro hx
    rw [Subalgebra.mem_centralizer_iff] at hx ⊢
    intro y hy
    refine Submodule.span_induction (p := fun y _ => y * x = x * y) ?_ ?_ ?_ ?_ hy
    · intro y hyS
      exact hx y hyS
    · simp
    · intro y z hy' hz' hy hz
      calc
        (y + z) * x = y * x + z * x := by rw [add_mul]
        _ = x * y + x * z := by rw [hy, hz]
        _ = x * (y + z) := by rw [mul_add]
    · intro r y _ hy
      calc
        (r • y) * x = r • (y * x) := by rw [smul_mul_assoc]
        _ = r • (x * y) := by rw [hy]
        _ = x * (r • y) := by rw [mul_smul_comm]
  · intro hx
    rw [Subalgebra.mem_centralizer_iff] at hx ⊢
    intro y hyS
    apply hx y
    exact Submodule.subset_span hyS

end RepresentationTheory
end LeanEval
