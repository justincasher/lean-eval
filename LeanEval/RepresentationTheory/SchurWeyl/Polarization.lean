import Mathlib
import LeanEval.RepresentationTheory.SchurWeyl.Defs

/-!
Polarization toolkit for Schur–Weyl duality: the symmetriser `e` on `(End_R V)^⊗k`, and the
fact that pure powers `m^⊗k` span the symmetric tensors `range e`.

These declarations support the blueprint
`schur-weyl-duality-s-k-image-equals-centralizer-of-glv-image`.
-/

namespace LeanEval
namespace RepresentationTheory

open scoped TensorProduct

/-- Coefficients of a univariate polynomial map lie in the span of its values.
If `p(t) = ∑_{l} t^l • c_l` and `t₀, …, t_d` are pairwise distinct (Vandermonde is invertible),
then every coefficient `c_i` is an `R`-linear combination of the values `p(t_j)`. -/
theorem coeff_mem_span_values_one {R : Type*} [Field R] {N : Type*} [AddCommGroup N] [Module R N]
    {d : ℕ} (c : Fin (d + 1) → N) {t : Fin (d + 1) → R} (ht : Function.Injective t)
    (i : Fin (d + 1)) :
    c i ∈ Submodule.span R
      (Set.range fun j : Fin (d + 1) => ∑ l : Fin (d + 1), (t j) ^ (l : ℕ) • c l) := by
  let A : Matrix (Fin (d + 1)) (Fin (d + 1)) R := Matrix.vandermonde t
  have hdet_ne_zero : Matrix.det A ≠ 0 := by
    rw [Matrix.det_vandermonde_ne_zero_iff]
    exact ht
  have hA_isUnit : IsUnit A := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact (Units.mk0 (Matrix.det A) hdet_ne_zero).isUnit
  haveI : Invertible A := hA_isUnit.invertible
  have h_inv_mul : A⁻¹ * A = 1 := Matrix.inv_mul_of_invertible A
  have h_sum_ident : ∀ i l : Fin (d + 1), ∑ j : Fin (d + 1), (A⁻¹) i j * A j l = if i = l then 1 else 0 := by
    intro i l
    calc
      ∑ j : Fin (d + 1), (A⁻¹) i j * A j l = (A⁻¹ * A) i l := by
        simp [Matrix.mul_apply]
      _ = (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) R) i l := by
        simp [h_inv_mul]
      _ = if i = l then 1 else 0 := by simp [Matrix.one_apply]
  have hc_expr : c i = ∑ j : Fin (d + 1), (A⁻¹) i j • (∑ l : Fin (d + 1), A j l • c l) := by
    calc
      c i = ∑ l : Fin (d + 1), (if i = l then (1 : R) else 0) • c l := by
        simp
      _ = ∑ l : Fin (d + 1), (∑ j : Fin (d + 1), (A⁻¹) i j * A j l) • c l := by
        simp [h_sum_ident]
      _ = ∑ j : Fin (d + 1), (A⁻¹) i j • (∑ l : Fin (d + 1), A j l • c l) := by
        calc
          ∑ l : Fin (d + 1), (∑ j : Fin (d + 1), (A⁻¹) i j * A j l) • c l
              = ∑ l : Fin (d + 1), ∑ j : Fin (d + 1), ((A⁻¹) i j * A j l) • c l := by
            simp [Finset.sum_smul]
          _ = ∑ l : Fin (d + 1), ∑ j : Fin (d + 1), (A⁻¹) i j • (A j l • c l) := by
            simp [mul_smul]
          _ = ∑ j : Fin (d + 1), ∑ l : Fin (d + 1), (A⁻¹) i j • (A j l • c l) := by
            rw [Finset.sum_comm]
          _ = ∑ j : Fin (d + 1), (A⁻¹) i j • (∑ l : Fin (d + 1), A j l • c l) := by
            simp [Finset.smul_sum]
      _ = ∑ j : Fin (d + 1), (A⁻¹) i j • (∑ l : Fin (d + 1), (t j) ^ (l : ℕ) • c l) := by
        simp [A, Matrix.vandermonde]
  rw [hc_expr]
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem _ ((A⁻¹) i j)
  apply Submodule.subset_span
  simp [A, Matrix.vandermonde]

/-- Multilinear coefficient extraction by iterated interpolation. If `P : Rⁿ → N` is, in monomial
form, `P t = ∑_f (∏ i, (t i)^(f i)) • c f` with multidegrees bounded by `k` in each variable, and
the scalars `0, 1, …, k` are pairwise distinct in `R`, then every coefficient `c f₀` (in particular
the multilinear one) is an `R`-linear combination of values of `P` on the grid `{0, …, k}ⁿ`. -/
theorem coeff_mem_span_values {R : Type*} [Field R] {N : Type*} [AddCommGroup N] [Module R N]
    {n k : ℕ} (hk : Set.InjOn (fun m : ℕ => (m : R)) (Set.Iic k))
    (c : (Fin n → Fin (k + 1)) → N) (P : (Fin n → R) → N)
    (hP : ∀ t : Fin n → R, P t = ∑ f : Fin n → Fin (k + 1), (∏ i, (t i) ^ (f i : ℕ)) • c f)
    (f₀ : Fin n → Fin (k + 1)) :
    c f₀ ∈ Submodule.span R
      (Set.range fun g : Fin n → Fin (k + 1) => P (fun i => ((g i : ℕ) : R))) := by
  sorry

variable {R : Type*} [Field R] {M : Type*} [AddCommGroup M] [Module R M] {k : ℕ}

/-- The symmetriser `e = (1/k!) ∑_{σ ∈ S_k} ρ(σ)` on `(End_R V)^⊗k`, where `ρ` is the
factor-permuting representation. -/
noncomputable def symmetriser (R M : Type*) [Field R] [AddCommGroup M] [Module R M] (k : ℕ)
    [Invertible (k.factorial : R)] : Module.End R (⨂[R]^k (Module.End R M)) :=
  ⅟(k.factorial : R) • ∑ σ : Equiv.Perm (Fin k), symAction R (Module.End R M) k σ

/-- The symmetriser is idempotent and its range is the subspace of permutation-invariant tensors. -/
theorem symmetriser_idempotent [Invertible (k.factorial : R)] :
    IsIdempotentElem (symmetriser R M k) ∧
      LinearMap.range (symmetriser R M k) =
        Representation.invariants (symAction R (Module.End R M) k) := by
  let ρ : Representation R (Equiv.Perm (Fin k)) (⨂[R]^k (Module.End R M)) :=
    symAction R (Module.End R M) k
  have hcard : (Fintype.card (Equiv.Perm (Fin k)) : R) = (k.factorial : R) := by
    simp [Fintype.card_perm, Fintype.card_fin]
  haveI : Invertible (Fintype.card (Equiv.Perm (Fin k)) : R) := by
    rw [hcard]; infer_instance
  have heq : symmetriser R M k = Representation.averageMap ρ := by
    apply LinearMap.ext
    intro x
    calc
      symmetriser R M k x
          = (⅟(k.factorial : R) • ∑ σ : Equiv.Perm (Fin k), symAction R (Module.End R M) k σ) x := rfl
      _ = (Representation.averageMap ρ) x := by
        dsimp [Representation.averageMap, GroupAlgebra.average, ρ]
        simp [map_sum, map_smul]
        rw [hcard]
  have hproj : LinearMap.IsProj (Representation.invariants ρ) (Representation.averageMap ρ) :=
    Representation.isProj_averageMap ρ
  have hproj_e : LinearMap.IsProj (Representation.invariants ρ) (symmetriser R M k) := by
    rw [heq]
    exact hproj
  refine ⟨?_, ?_⟩
  · -- IsIdempotentElem (symmetriser R M k)
    rw [IsIdempotentElem, LinearMap.ext_iff]
    intro x
    calc
      (symmetriser R M k * symmetriser R M k) x
          = symmetriser R M k (symmetriser R M k x) := rfl
      _ = symmetriser R M k x :=
        hproj_e.map_id (symmetriser R M k x) (hproj_e.map_mem x)
  · -- LinearMap.range (symmetriser R M k) = Representation.invariants ρ
    apply le_antisymm
    · intro y hy
      rcases hy with ⟨x, rfl⟩
      exact hproj_e.map_mem x
    · intro y hy
      refine ⟨y, ?_⟩
      exact hproj_e.map_id y hy

/-- The range of `e` is spanned by the symmetrised pure tensors `e (m₁ ⊗ ⋯ ⊗ m_k)`. -/
theorem range_symmetriser_eq_span [Invertible (k.factorial : R)] :
    LinearMap.range (symmetriser R M k) =
      Submodule.span R (Set.range fun m : Fin k → Module.End R M =>
        symmetriser R M k (PiTensorProduct.tprod R m)) := by
  calc
    LinearMap.range (symmetriser R M k) = Submodule.map (symmetriser R M k) ⊤ := by
      rw [LinearMap.range_eq_map]
    _ = Submodule.map (symmetriser R M k) (Submodule.span R (Set.range (PiTensorProduct.tprod R))) := by
      rw [PiTensorProduct.span_tprod_eq_top]
    _ = Submodule.span R ((symmetriser R M k) '' (Set.range (PiTensorProduct.tprod R))) := by
      rw [Submodule.map_span]
    _ = Submodule.span R (Set.range ((symmetriser R M k) ∘ (PiTensorProduct.tprod R))) := by
      rw [Set.range_comp]
    _ = Submodule.span R (Set.range fun m : Fin k → Module.End R M =>
        symmetriser R M k (PiTensorProduct.tprod R m)) := rfl

/-- Pure powers are symmetric: `m^⊗k` lies in `range e` for every `m ∈ End_R V`. -/
theorem tprod_const_mem_range_symmetriser [Invertible (k.factorial : R)] (m : Module.End R M) :
    PiTensorProduct.tprod R (fun _ : Fin k => m) ∈ LinearMap.range (symmetriser R M k) := by
  -- Each permutation fixes the constant pure tensor
  have h_sym_fix (σ : Equiv.Perm (Fin k)) : symAction R (Module.End R M) k σ (PiTensorProduct.tprod R (fun _ : Fin k => m)) =
      PiTensorProduct.tprod R (fun _ : Fin k => m) := by
    simp [symAction, PiTensorProduct.reindex_tprod]
  -- Sum of symAction σ applied to constant tprod is (k! : R) • tprod (since each term is tprod)
  have h_sum_eq : (∑ σ : Equiv.Perm (Fin k), symAction R (Module.End R M) k σ (PiTensorProduct.tprod R (fun _ : Fin k => m))) =
      ((k.factorial : R) • PiTensorProduct.tprod R (fun _ : Fin k => m)) := by
    calc
      (∑ σ : Equiv.Perm (Fin k), symAction R (Module.End R M) k σ (PiTensorProduct.tprod R (fun _ : Fin k => m)))
          = (∑ σ : Equiv.Perm (Fin k), PiTensorProduct.tprod R (fun _ : Fin k => m)) := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [h_sym_fix σ]
      _ = (Fintype.card (Equiv.Perm (Fin k))) • (PiTensorProduct.tprod R (fun _ : Fin k => m)) := by
        simp
      _ = ((Fintype.card (Equiv.Perm (Fin k)) : R) • PiTensorProduct.tprod R (fun _ : Fin k => m)) := by
        rw [Nat.cast_smul_eq_nsmul]
      _ = ((k.factorial : R) • PiTensorProduct.tprod R (fun _ : Fin k => m)) := by
        simp [Fintype.card_perm, Fintype.card_fin]
  -- Compute symmetriser applied to constant tprod
  have h_sym_eq : symmetriser R M k (PiTensorProduct.tprod R (fun _ : Fin k => m)) =
      PiTensorProduct.tprod R (fun _ : Fin k => m) := by
    calc
      symmetriser R M k (PiTensorProduct.tprod R (fun _ : Fin k => m)) =
          (⅟(k.factorial : R) • ∑ σ : Equiv.Perm (Fin k), symAction R (Module.End R M) k σ)
            (PiTensorProduct.tprod R (fun _ : Fin k => m)) := rfl
      _ = (⅟(k.factorial : R)) • (∑ σ : Equiv.Perm (Fin k),
          symAction R (Module.End R M) k σ (PiTensorProduct.tprod R (fun _ : Fin k => m))) := by
        simp
      _ = (⅟(k.factorial : R)) • ((k.factorial : R) • PiTensorProduct.tprod R (fun _ : Fin k => m)) := by
        rw [h_sum_eq]
      _ = ((⅟(k.factorial : R)) * (k.factorial : R)) • PiTensorProduct.tprod R (fun _ : Fin k => m) := by
        rw [smul_smul]
      _ = (1 : R) • PiTensorProduct.tprod R (fun _ : Fin k => m) := by
        simp
      _ = PiTensorProduct.tprod R (fun _ : Fin k => m) := by simp
  -- Therefore tprod = symmetriser(tprod) ∈ range symmetriser
  refine ⟨PiTensorProduct.tprod R (fun _ : Fin k => m), ?_⟩
  rw [h_sym_eq]

/-- Multilinear component of a power: the symmetrisation of `m₁ ⊗ ⋯ ⊗ m_k`, i.e.
`∑_{σ ∈ S_k} m_{σ 0} ⊗ ⋯ ⊗ m_{σ (k-1)} = k! · e (m₁ ⊗ ⋯ ⊗ m_k)`. -/
theorem sum_perm_tprod_eq [Invertible (k.factorial : R)] (m : Fin k → Module.End R M) :
    (∑ σ : Equiv.Perm (Fin k), PiTensorProduct.tprod R (fun i => m (σ i))) =
      (k.factorial : R) • symmetriser R M k (PiTensorProduct.tprod R m) := by
  -- Rewrite symmetriser and simplify the scalar factor.
  unfold symmetriser
  rw [LinearMap.smul_apply, ← mul_smul, mul_invOf_self, one_smul, LinearMap.sum_apply]
  -- Lemma: symAction σ (tprod R m) = tprod R (m ∘ σ.symm)
  have h_action (σ : Equiv.Perm (Fin k)) : (symAction R (Module.End R M) k σ) (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R (fun i : Fin k => m (σ.symm i)) := by
    simp [symAction, PiTensorProduct.reindex_tprod]
  have h_sum_action : (∑ σ : Equiv.Perm (Fin k), (symAction R (Module.End R M) k σ) (PiTensorProduct.tprod R m)) =
      (∑ σ : Equiv.Perm (Fin k), PiTensorProduct.tprod R (fun i : Fin k => m (σ.symm i))) := by
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [h_action σ]
  rw [h_sum_action]
  -- Goal: (∑ σ, tprod R (m ∘ σ)) = (∑ σ, tprod R (m ∘ σ.symm))
  -- The map σ ↦ σ.symm is a bijection on S_k, so reindex.
  let perm_symm_equiv : (Equiv.Perm (Fin k)) ≃ (Equiv.Perm (Fin k)) :=
    { toFun := fun σ => σ.symm
      invFun := fun σ => σ.symm
      left_inv := fun σ => by simp
      right_inv := fun σ => by simp }
  simpa using (Equiv.sum_comp perm_symm_equiv
    (fun σ : Equiv.Perm (Fin k) => PiTensorProduct.tprod R (fun i : Fin k => m (σ i)))).symm

/-- Pure powers span the symmetric tensors: the span of `{ m^⊗k : m ∈ End_R V }` equals
`range e`. -/
theorem span_tprod_const_eq_range_symmetriser [Invertible (k.factorial : R)] :
    Submodule.span R (Set.range fun m : Module.End R M =>
        PiTensorProduct.tprod R (fun _ : Fin k => m)) =
      LinearMap.range (symmetriser R M k) := by
  sorry

end RepresentationTheory
end LeanEval
