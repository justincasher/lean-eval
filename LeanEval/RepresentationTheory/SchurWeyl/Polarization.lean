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
  sorry

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
  sorry

/-- The range of `e` is spanned by the symmetrised pure tensors `e (m₁ ⊗ ⋯ ⊗ m_k)`. -/
theorem range_symmetriser_eq_span [Invertible (k.factorial : R)] :
    LinearMap.range (symmetriser R M k) =
      Submodule.span R (Set.range fun m : Fin k → Module.End R M =>
        symmetriser R M k (PiTensorProduct.tprod R m)) := by
  sorry

/-- Pure powers are symmetric: `m^⊗k` lies in `range e` for every `m ∈ End_R V`. -/
theorem tprod_const_mem_range_symmetriser [Invertible (k.factorial : R)] (m : Module.End R M) :
    PiTensorProduct.tprod R (fun _ : Fin k => m) ∈ LinearMap.range (symmetriser R M k) := by
  sorry

/-- Multilinear component of a power: the symmetrisation of `m₁ ⊗ ⋯ ⊗ m_k`, i.e.
`∑_{σ ∈ S_k} m_{σ 0} ⊗ ⋯ ⊗ m_{σ (k-1)} = k! · e (m₁ ⊗ ⋯ ⊗ m_k)`. -/
theorem sum_perm_tprod_eq [Invertible (k.factorial : R)] (m : Fin k → Module.End R M) :
    (∑ σ : Equiv.Perm (Fin k), PiTensorProduct.tprod R (fun i => m (σ i))) =
      (k.factorial : R) • symmetriser R M k (PiTensorProduct.tprod R m) := by
  sorry

/-- Pure powers span the symmetric tensors: the span of `{ m^⊗k : m ∈ End_R V }` equals
`range e`. -/
theorem span_tprod_const_eq_range_symmetriser [Invertible (k.factorial : R)] :
    Submodule.span R (Set.range fun m : Module.End R M =>
        PiTensorProduct.tprod R (fun _ : Fin k => m)) =
      LinearMap.range (symmetriser R M k) := by
  sorry

end RepresentationTheory
end LeanEval
