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
    (by
      rw [PiTensorProduct.one_def, PiTensorProduct.lift.tprod,
        PiTensorProduct.mapMultilinear_apply]
      exact PiTensorProduct.map_one)
    (by
      intro x y
      refine PiTensorProduct.induction_on x ?_ ?_
      · intro r a
        refine PiTensorProduct.induction_on y ?_ ?_
        · intro s b
          rw [PiTensorProduct.smul_tprod_mul_smul_tprod, map_smul, map_smul, map_smul,
            PiTensorProduct.lift.tprod, PiTensorProduct.lift.tprod, PiTensorProduct.lift.tprod,
            PiTensorProduct.mapMultilinear_apply, PiTensorProduct.mapMultilinear_apply,
            PiTensorProduct.mapMultilinear_apply, smul_mul_smul_comm]
          congr 1
          have hab : (a * b) = (fun i => a i ∘ₗ b i) := rfl
          rw [hab, PiTensorProduct.map_comp]
          rfl
        · intro y₁ y₂ hy₁ hy₂
          rw [mul_add, map_add, map_add, hy₁, hy₂, mul_add]
      · intro x₁ x₂ hx₁ hx₂
        rw [add_mul, map_add, map_add, hx₁, hx₂, add_mul])

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
  -- Lemma: endTensorHom on a pure tensor equals PiTensorProduct.map
  have h_tprod (m : Fin k → Module.End R M) : endTensorHom R M k (PiTensorProduct.tprod R m) =
      PiTensorProduct.map (fun i : Fin k => (m i : M →ₗ[R] M)) := by
    unfold endTensorHom
    simp [PiTensorProduct.lift.tprod, PiTensorProduct.mapMultilinear_apply]
  -- Lemma: on a pure tensor, the intertwining identity holds
  have h_tprod_intertwine (σ : Equiv.Perm (Fin k)) (m : Fin k → Module.End R M) :
      endTensorHom R M k (symAction R (Module.End R M) k σ (PiTensorProduct.tprod R m)) =
        symAction R M k σ * endTensorHom R M k (PiTensorProduct.tprod R m) * symAction R M k σ⁻¹ := by
    calc
      endTensorHom R M k (symAction R (Module.End R M) k σ (PiTensorProduct.tprod R m))
          = endTensorHom R M k (PiTensorProduct.tprod R (fun i => m (σ.symm i))) := by
            simp [symAction, PiTensorProduct.reindex_tprod]
      _ = PiTensorProduct.map (fun i : Fin k => (m (σ.symm i) : M →ₗ[R] M)) := by
        rw [h_tprod]
      _ = (PiTensorProduct.reindex R (fun _ : Fin k => M) σ).toLinearMap
          * PiTensorProduct.map (fun i : Fin k => (m i : M →ₗ[R] M))
          * (PiTensorProduct.reindex R (fun _ : Fin k => M) (σ⁻¹)).toLinearMap := by
        calc
          PiTensorProduct.map (fun i : Fin k => (m (σ.symm i) : M →ₗ[R] M))
              = PiTensorProduct.map (fun i : Fin k => (m (σ.symm i) : M →ₗ[R] M)) ∘ₗ .id := by
                simp
          _ = PiTensorProduct.map (fun i : Fin k => (m (σ.symm i) : M →ₗ[R] M))
              ∘ₗ ((PiTensorProduct.reindex R (fun _ : Fin k => M) σ).toLinearMap
                ∘ₗ (PiTensorProduct.reindex R (fun _ : Fin k => M) (σ⁻¹)).toLinearMap) := by
            have h_comp_id : (PiTensorProduct.reindex R (fun _ : Fin k => M) σ).toLinearMap
                ∘ₗ (PiTensorProduct.reindex R (fun _ : Fin k => M) (σ⁻¹)).toLinearMap = .id := by
              have h_symm : (PiTensorProduct.reindex R (fun _ : Fin k => M) (σ⁻¹)).toLinearMap =
                  (PiTensorProduct.reindex R (fun _ : Fin k => M) σ).symm.toLinearMap := by
                calc
                  (PiTensorProduct.reindex R (fun _ : Fin k => M) (σ⁻¹)).toLinearMap
                      = (PiTensorProduct.reindex R (fun _ : Fin k => M) (σ.symm)).toLinearMap := rfl
                  _ = ((PiTensorProduct.reindex R (fun _ : Fin k => M) σ).symm).toLinearMap := by
                    simp [PiTensorProduct.reindex_symm]
              rw [h_symm]
              simp
            rw [h_comp_id]
          _ = ((PiTensorProduct.map (fun i : Fin k => (m (σ.symm i) : M →ₗ[R] M)))
              ∘ₗ (PiTensorProduct.reindex R (fun _ : Fin k => M) σ).toLinearMap)
              ∘ₗ (PiTensorProduct.reindex R (fun _ : Fin k => M) (σ⁻¹)).toLinearMap := by
            simp [LinearMap.comp_assoc]
          _ = ((PiTensorProduct.reindex R (fun _ : Fin k => M) σ).toLinearMap
              ∘ₗ PiTensorProduct.map (fun i : Fin k => (m i : M →ₗ[R] M)))
              ∘ₗ (PiTensorProduct.reindex R (fun _ : Fin k => M) (σ⁻¹)).toLinearMap := by
            rw [PiTensorProduct.map_comp_reindex_eq (fun i : Fin k => (m i : M →ₗ[R] M)) σ]
          _ = (PiTensorProduct.reindex R (fun _ : Fin k => M) σ).toLinearMap
              ∘ₗ PiTensorProduct.map (fun i : Fin k => (m i : M →ₗ[R] M))
              ∘ₗ (PiTensorProduct.reindex R (fun _ : Fin k => M) (σ⁻¹)).toLinearMap := by
            simp [LinearMap.comp_assoc]
      _ = symAction R M k σ * PiTensorProduct.map (fun i : Fin k => (m i : M →ₗ[R] M))
          * symAction R M k σ⁻¹ := by
        simp [symAction]
      _ = symAction R M k σ * endTensorHom R M k (PiTensorProduct.tprod R m)
          * symAction R M k σ⁻¹ := by rw [h_tprod]
  -- Prove the full statement using induction on x
  refine PiTensorProduct.induction_on x ?_ ?_
  · intro r m
    calc
      endTensorHom R M k (symAction R (Module.End R M) k σ (r • PiTensorProduct.tprod R m))
          = endTensorHom R M k (r • symAction R (Module.End R M) k σ (PiTensorProduct.tprod R m)) := by
            rw [LinearMap.map_smul (symAction R (Module.End R M) k σ)]
      _ = r • endTensorHom R M k (symAction R (Module.End R M) k σ (PiTensorProduct.tprod R m)) := by
        rw [map_smul]
      _ = r • (symAction R M k σ * endTensorHom R M k (PiTensorProduct.tprod R m)
                * symAction R M k σ⁻¹) := by
        rw [h_tprod_intertwine σ m]
      _ = symAction R M k σ * (r • endTensorHom R M k (PiTensorProduct.tprod R m))
          * symAction R M k σ⁻¹ := by
        simp
      _ = symAction R M k σ * endTensorHom R M k (r • PiTensorProduct.tprod R m)
          * symAction R M k σ⁻¹ := by
        rw [← map_smul (endTensorHom R M k)]
  · intro x y hx hy
    calc
      endTensorHom R M k (symAction R (Module.End R M) k σ (x + y))
          = endTensorHom R M k (symAction R (Module.End R M) k σ x
              + symAction R (Module.End R M) k σ y) := by
            rw [LinearMap.map_add (symAction R (Module.End R M) k σ)]
      _ = endTensorHom R M k (symAction R (Module.End R M) k σ x)
          + endTensorHom R M k (symAction R (Module.End R M) k σ y) := by
        rw [map_add]
      _ = (symAction R M k σ * endTensorHom R M k x * symAction R M k σ⁻¹)
          + (symAction R M k σ * endTensorHom R M k y * symAction R M k σ⁻¹) := by
        rw [hx, hy]
      _ = symAction R M k σ * (endTensorHom R M k x + endTensorHom R M k y)
          * symAction R M k σ⁻¹ := by
        calc
          (symAction R M k σ * endTensorHom R M k x * symAction R M k σ⁻¹)
              + (symAction R M k σ * endTensorHom R M k y * symAction R M k σ⁻¹)
              = (symAction R M k σ * endTensorHom R M k x
                + symAction R M k σ * endTensorHom R M k y) * symAction R M k σ⁻¹ := by
                rw [add_mul]
          _ = (symAction R M k σ * (endTensorHom R M k x + endTensorHom R M k y))
              * symAction R M k σ⁻¹ := by rw [mul_add]
      _ = symAction R M k σ * endTensorHom R M k (x + y) * symAction R M k σ⁻¹ := by
        rw [map_add]

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
        ext x; simp [sub_eq_add_neg]
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
    ext t; simp [Rset, eq_comm]
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
theorem span_range_glAction_eq_span_map [Infinite R] [FiniteDimensional R M]
    [Invertible (k.factorial : R)] :
    Submodule.span R (Set.range (glAction R M k)) =
      Submodule.span R (Set.range fun m : Module.End R M =>
        PiTensorProduct.map (fun _ : Fin k => m)) := by
  sorry

/-- For `x ∈ End_R(V^⊗k)`, `x` commutes with all `symAction(σ)` iff `(Φ^~)⁻¹(x)` is
`ρ`-invariant, where `ρ` is `symAction` on the tensor power of `End`. -/
private lemma commute_symAction_iff_invariant [FiniteDimensional R M]
    (x : Module.End R (⨂[R]^k M)) :
    x ∈ Subalgebra.centralizer R (Set.range (symAction R M k)) ↔
    (endTensorEquiv R M k).symm x ∈ Representation.invariants (symAction R (Module.End R M) k) := by
  let Φ := endTensorEquiv R M k
  let ρ := symAction R (Module.End R M) k
  let σAct := symAction R M k
  have hΦ_inj : Function.Injective Φ := AlgEquiv.injective Φ
  have hΦ_symm_apply (y) : Φ (Φ.symm y) = y := by simp
  have hΦ_symm_eq (y) : Φ.symm (Φ y) = y := by simp
  constructor
  · intro hx
    rw [Subalgebra.mem_centralizer_iff] at hx
    have hx_all (σ : Equiv.Perm (Fin k)) : σAct σ * x = x * σAct σ :=
      hx (σAct σ) (Set.mem_range_self σ)
    have hx_all' (σ : Equiv.Perm (Fin k)) : σAct σ * x * σAct (σ⁻¹) = x := by
      calc
        σAct σ * x * σAct (σ⁻¹) = (x * σAct σ) * σAct (σ⁻¹) := by rw [hx_all σ]
        _ = x * (σAct σ * σAct (σ⁻¹)) := by ring
        _ = x * σAct (σ * σ⁻¹) := by rw [MonoidHom.map_mul (σAct : _ →* _)]
        _ = x * σAct 1 := by simp
        _ = x := by simp
    set ξ := Φ.symm x with hξ_def
    have hx_eq : x = Φ ξ := by dsimp [ξ]; simp
    intro σ
    calc
      ρ σ ξ = Φ.symm (Φ (ρ σ ξ)) := by simp
      _ = Φ.symm (endTensorHom R M k (ρ σ ξ)) := rfl
      _ = Φ.symm (σAct σ * endTensorHom R M k ξ * σAct (σ⁻¹)) := by
        rw [endTensorHom_intertwine σ ξ]
      _ = Φ.symm (σAct σ * Φ ξ * σAct (σ⁻¹)) := rfl
      _ = Φ.symm (σAct σ * x * σAct (σ⁻¹)) := by
        dsimp [ξ]; simp
      _ = Φ.symm x := by
        rw [hx_all' σ]
      _ = ξ := by dsimp [ξ]
  · intro hξ
    have hξ_all : ∀ σ : Equiv.Perm (Fin k), ρ σ (Φ.symm x) = Φ.symm x := by
      rw [Representation.mem_invariants] at hξ
      exact hξ
    rw [Subalgebra.mem_centralizer_iff]
    intro y hy
    rcases hy with ⟨σ, rfl⟩
    have hξ_σ : ρ σ (Φ.symm x) = Φ.symm x := hξ_all σ
    calc
      σAct σ * x = σAct σ * Φ (Φ.symm x) := by simp
      _ = σAct σ * endTensorHom R M k (Φ.symm x) := rfl
      _ = (σAct σ * endTensorHom R M k (Φ.symm x) * σAct (σ⁻¹)) * σAct σ := by
        calc
          σAct σ * endTensorHom R M k (Φ.symm x)
              = (σAct σ * endTensorHom R M k (Φ.symm x) * σAct (σ⁻¹)) * σAct σ := by
            calc
              σAct σ * endTensorHom R M k (Φ.symm x)
                  = (σAct σ * endTensorHom R M k (Φ.symm x) * 1) := by simp
              _ = (σAct σ * endTensorHom R M k (Φ.symm x) * (σAct (σ⁻¹) * σAct σ)) := by simp
              _ = (σAct σ * endTensorHom R M k (Φ.symm x) * σAct (σ⁻¹)) * σAct σ := by ring
          _ = (σAct σ * endTensorHom R M k (Φ.symm x) * σAct (σ⁻¹)) * σAct σ := rfl
      _ = endTensorHom R M k (ρ σ (Φ.symm x)) * σAct σ := by
        rw [← endTensorHom_intertwine σ (Φ.symm x)]
      _ = endTensorHom R M k (Φ.symm x) * σAct σ := by rw [hξ_σ]
      _ = Φ (Φ.symm x) * σAct σ := rfl
      _ = x * σAct σ := by simp

/-- The centralizer of `range symAction` equals (as a set) the span of the diagonal maps
`{ map (fun i => m) : m ∈ End_R V }`, i.e. the symmetric tensors transported by `Φ^~`. -/
theorem centralizer_range_symAction_eq_span_map [FiniteDimensional R M]
    [Invertible (k.factorial : R)] :
    (Subalgebra.centralizer R (Set.range (symAction R M k)) :
        Set (Module.End R (⨂[R]^k M))) =
      (Submodule.span R (Set.range fun m : Module.End R M =>
        PiTensorProduct.map (fun _ : Fin k => m)) : Set (Module.End R (⨂[R]^k M))) := by
  let Φ := endTensorEquiv R M k
  have h_tprod_map (m : Module.End R M) :
      Φ (PiTensorProduct.tprod R (fun _ : Fin k => m)) =
      PiTensorProduct.map (fun _ : Fin k => m) := by
    calc
      Φ (PiTensorProduct.tprod R (fun _ : Fin k => m)) =
          endTensorHom R M k (PiTensorProduct.tprod R (fun _ : Fin k => m)) := rfl
      _ = PiTensorProduct.map (fun _ : Fin k => (m : M →ₗ[R] M)) := by
        unfold endTensorHom
        simp [PiTensorProduct.lift.tprod, PiTensorProduct.mapMultilinear_apply]
      _ = PiTensorProduct.map (fun _ : Fin k => m) := by simp
  ext x
  constructor
  · intro hx
    have hξ : Φ.symm x ∈ Representation.invariants (symAction R (Module.End R M) k) :=
      (commute_symAction_iff_invariant x).mp hx
    have hξ_range : Φ.symm x ∈ LinearMap.range (symmetriser R M k) := by
      rw [symmetriser_idempotent.2]
      exact hξ
    have hξ_span : Φ.symm x ∈ Submodule.span R (Set.range fun m : Module.End R M =>
        PiTensorProduct.tprod R (fun _ : Fin k => m)) := by
      rw [span_tprod_const_eq_range_symmetriser]
      exact hξ_range
    let Φₗ : (⨂[R]^k (Module.End R M)) →ₗ[R] Module.End R (⨂[R]^k M) := Φ.toLinearMap
    have hx_mem : x ∈ Submodule.map Φₗ
        (Submodule.span R (Set.range fun m : Module.End R M =>
          PiTensorProduct.tprod R (fun _ : Fin k => m))) := by
      refine Submodule.mem_map.mpr ⟨Φ.symm x, hξ_span, ?_⟩
      simp [Φₗ]
    have hmap_span_eq : Submodule.map Φₗ
        (Submodule.span R (Set.range fun m : Module.End R M =>
          PiTensorProduct.tprod R (fun _ : Fin k => m))) =
      Submodule.span R (Set.range fun m : Module.End R M =>
        PiTensorProduct.map (fun _ : Fin k => m)) := by
      calc
        Submodule.map Φₗ (Submodule.span R (Set.range fun m : Module.End R M =>
          PiTensorProduct.tprod R (fun _ : Fin k => m))) =
          Submodule.span R (Φₗ '' (Set.range fun m : Module.End R M =>
            PiTensorProduct.tprod R (fun _ : Fin k => m))) := by
          rw [Submodule.map_span]
        _ = Submodule.span R (Set.range (Φₗ ∘ fun m : Module.End R M =>
            PiTensorProduct.tprod R (fun _ : Fin k => m))) := by
          have h_image_range : Φₗ '' (Set.range fun m : Module.End R M =>
              PiTensorProduct.tprod R (fun _ : Fin k => m)) =
            Set.range (Φₗ ∘ fun m : Module.End R M =>
              PiTensorProduct.tprod R (fun _ : Fin k => m)) := by
            ext y; simp
          rw [h_image_range]
        _ = Submodule.span R (Set.range fun m : Module.End R M =>
            PiTensorProduct.map (fun _ : Fin k => m)) := by
          apply Submodule.span_eq_span
          · rintro _ ⟨m, rfl⟩
            refine Submodule.subset_span ⟨m, ?_⟩
            simp [h_tprod_map m, Φₗ]
          · rintro _ ⟨m, rfl⟩
            refine Submodule.subset_span ⟨m, ?_⟩
            simp [h_tprod_map m, Φₗ]
    rw [hmap_span_eq] at hx_mem
    exact hx_mem
  · intro hx
    have h_gen (m : Module.End R M) : PiTensorProduct.map (fun _ : Fin k => m) ∈
        Subalgebra.centralizer R (Set.range (symAction R M k)) := by
      have hmem : PiTensorProduct.tprod R (fun _ : Fin k => m) ∈
          Representation.invariants (symAction R (Module.End R M) k) := by
        have hrange : PiTensorProduct.tprod R (fun _ : Fin k => m) ∈
            LinearMap.range (symmetriser R M k) :=
          tprod_const_mem_range_symmetriser m
        rw [← symmetriser_idempotent.2]
        exact hrange
      have hΦ_symm_map : Φ.symm (PiTensorProduct.map (fun _ : Fin k => m)) =
          PiTensorProduct.tprod R (fun _ : Fin k => m) := by
        calc
          Φ.symm (PiTensorProduct.map (fun _ : Fin k => m)) =
              Φ.symm (Φ (PiTensorProduct.tprod R (fun _ : Fin k => m))) := by
            rw [h_tprod_map m]
          _ = PiTensorProduct.tprod R (fun _ : Fin k => m) := by simp
      have hcomm := (commute_symAction_iff_invariant
        (PiTensorProduct.map (fun _ : Fin k => m))).mpr (by
          rw [hΦ_symm_map]
          exact hmem)
      exact hcomm
    have h_submodule_span_le : Submodule.span R (Set.range fun m : Module.End R M =>
        PiTensorProduct.map (fun _ : Fin k => m)) ≤
      Subalgebra.toSubmodule (Subalgebra.centralizer R (Set.range (symAction R M k))) := by
      apply Submodule.span_le.mpr
      rintro y ⟨m, rfl⟩
      exact h_gen m
    have hx' : x ∈ Submodule.span R (Set.range fun m : Module.End R M =>
        PiTensorProduct.map (fun _ : Fin k => m)) := hx
    have hx_centralizer : x ∈ Subalgebra.toSubmodule (Subalgebra.centralizer R
        (Set.range (symAction R M k))) := h_submodule_span_le hx'
    exact hx_centralizer

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
