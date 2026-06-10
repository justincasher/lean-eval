import Mathlib
import EvalTools.Markers

namespace LeanEval
namespace RepresentationTheory

/-!
Brauer's theorem on character values.

For a finite group `G` of exponent `n`, every value of every complex
character of `G` lies in (the image of) the cyclotomic field `ℚ(ζₙ)`.
Concretely: there is a ring embedding `φ : ℚ(ζₙ) →+* ℂ` whose range
contains `tr ρ(g)` for every finite-dimensional complex representation
`ρ` of `G` and every `g ∈ G`.

This is a consequence of Brauer's induction theorem (every character is a
ℤ-combination of characters induced from elementary subgroups, whose values
are visibly cyclotomic).

The full Brauer "splitting field" theorem says more — that `ℚ(ζₙ)` is in fact
a *splitting field* for the group algebra, i.e. every irreducible complex
representation admits a `ℚ(ζₙ)`-form. The character-value statement below
is implied by the splitting-field statement and is the part most cleanly
expressible in Mathlib's current API; the full splitting-field statement
would additionally require scalar-extension scaffolding around
`CyclotomicField n ℚ → ℂ`.
-/

/-- For any representation `ρ` of a group `G` on a `ℂ`-module `V`, the value
`ρ g` raised to the exponent of `G` is the identity. -/
theorem rho_pow_eq_one
    {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    (ρ g) ^ (Monoid.exponent G) = 1 := by
  calc
    (ρ g) ^ (Monoid.exponent G) = ρ (g ^ (Monoid.exponent G)) := by
      rw [map_pow]
    _ = ρ 1 := by rw [Monoid.pow_exponent_eq_one g]
    _ = 1 := by rw [map_one]

/-- The polynomial `X ^ n - 1` (with `n = exponent G`) annihilates `ρ g`. -/
theorem annihilating_polynomial
    {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    (Polynomial.aeval (ρ g))
        (Polynomial.X ^ (Monoid.exponent G) - 1 : Polynomial ℂ) = 0 := by
  rw [map_sub, Polynomial.aeval_X_pow, Polynomial.aeval_one, rho_pow_eq_one ρ g, sub_self]

/-- The characteristic polynomial of any endomorphism of a finite-dimensional
`ℂ`-vector space splits over `ℂ`. -/
theorem charpoly_splits
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) :
    f.charpoly.Splits := by
  simpa using IsAlgClosed.splits (k := ℂ) (f.charpoly)

/-- Every root of the characteristic polynomial of `ρ g` is an
`(exponent G)`-th root of unity in `ℂ`. -/
theorem charpoly_roots_roots_of_unity
    {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) {lam : ℂ}
    (h : (ρ g).charpoly.IsRoot lam) :
    lam ^ (Monoid.exponent G) = 1 := by
  set n := Monoid.exponent G with hn
  -- lam is an eigenvalue of (ρ g)
  have h_eigen : Module.End.HasEigenvalue (ρ g) lam :=
    ((Module.End.hasEigenvalue_iff_isRoot_charpoly (ρ g) lam).mpr h)
  -- therefore lam is a root of the minimal polynomial of (ρ g)
  have h_minpoly_root : (minpoly ℂ (ρ g)).IsRoot lam :=
    Module.End.isRoot_of_hasEigenvalue h_eigen
  have h_ann : (Polynomial.aeval (ρ g)) (Polynomial.X ^ n - 1 : Polynomial ℂ) = 0 :=
    annihilating_polynomial ρ g
  have h_minpoly_dvd : minpoly ℂ (ρ g) ∣ (Polynomial.X ^ n - 1 : Polynomial ℂ) := by
    apply minpoly.dvd (A := ℂ) (x := ρ g)
    exact h_ann
  have h_eval : ((Polynomial.X ^ n - 1 : Polynomial ℂ)).eval lam = 0 :=
    Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero h_minpoly_dvd h_minpoly_root
  have h_eval_calc : ((Polynomial.X ^ n - 1 : Polynomial ℂ)).eval lam = lam ^ n - 1 := by
    simp
  rw [h_eval_calc] at h_eval
  exact sub_eq_zero.mp h_eval

/-- The trace of an endomorphism of a finite-dimensional `ℂ`-vector space
equals the sum (with multiplicity) of the roots of its characteristic
polynomial. -/
theorem trace_eq_sum_charpoly_roots
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) :
    LinearMap.trace ℂ V f = f.charpoly.roots.sum := by
  simpa using Module.End.trace_eq_sum_roots_charpoly_of_splits (charpoly_splits f)

/-- For every positive natural number `n`, there is a primitive `n`-th root
of unity in `ℂ`. -/
theorem complex_primitive_root (n : ℕ) (hn : 0 < n) :
    ∃ ζ : ℂ, IsPrimitiveRoot ζ n := by
  have hn0 : n ≠ 0 := hn.ne'
  refine ⟨Complex.exp (2 * Real.pi * Complex.I / n), Complex.isPrimitiveRoot_exp n hn0⟩

/-- For every positive natural number `n`, there is a ring homomorphism
`φ : CyclotomicField n ℚ →+* ℂ` sending the canonical primitive root
`IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ)` to a primitive
`n`-th root of unity in `ℂ`. -/
theorem cyclotomic_embedding (n : ℕ) [NeZero n] [NeZero ((n : ℕ) : ℚ)]
    [IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ)] :
    ∃ φ : CyclotomicField n ℚ →+* ℂ,
      IsPrimitiveRoot
        (φ (IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ))) n := by
  -- Pick a primitive n-th root ζ in ℂ.
  obtain ⟨ζ, hζ⟩ := complex_primitive_root n (NeZero.pos n)
  -- The canonical primitive root in the cyclotomic field.
  set ζ₀ : CyclotomicField n ℚ := IsCyclotomicExtension.zeta n ℚ _ with hζ₀
  have hζ₀_prim : IsPrimitiveRoot ζ₀ n := IsCyclotomicExtension.zeta_spec n ℚ _
  -- Irreducibility of the n-th cyclotomic polynomial over ℚ.
  have hirr : Irreducible (Polynomial.cyclotomic n ℚ) :=
    Polynomial.cyclotomic.irreducible_rat (NeZero.pos n)
  -- The element of `primitiveRoots n ℂ` corresponding to ζ.
  have hζmem : ζ ∈ primitiveRoots n ℂ :=
    (mem_primitiveRoots (NeZero.pos n)).mpr hζ
  -- Use the equivalence between algebra embeddings and primitive roots.
  let ψ : CyclotomicField n ℚ →ₐ[ℚ] ℂ :=
    (hζ₀_prim.embeddingsEquivPrimitiveRoots ℂ hirr).symm ⟨ζ, hζmem⟩
  refine ⟨ψ.toRingHom, ?_⟩
  -- The embedding sends ζ₀ to ζ, which is a primitive root.
  have hψζ : ψ ζ₀ = ζ := by
    have h := hζ₀_prim.embeddingsEquivPrimitiveRoots_apply_coe ℂ hirr ψ
    -- h : ((... .symm ⟨ζ, hζmem⟩) : L →ₐ[K] ℂ) ζ₀ = ζ (via the apply_coe simp lemma).
    -- The LHS reduces by Equiv.apply_symm_apply.
    simpa [ψ] using h.symm
  show IsPrimitiveRoot (ψ.toRingHom ζ₀) n
  rw [show ψ.toRingHom ζ₀ = ψ ζ₀ from rfl, hψζ]
  exact hζ

/-- The range of any ring embedding `φ : CyclotomicField n ℚ →+* ℂ` whose
image of the canonical primitive root is a primitive `n`-th root of unity
contains every `n`-th root of unity in `ℂ`. -/
theorem range_contains_roots_of_unity (n : ℕ) [NeZero n] [NeZero ((n : ℕ) : ℚ)]
    [IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ)]
    (φ : CyclotomicField n ℚ →+* ℂ)
    (hφ : IsPrimitiveRoot
            (φ (IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ))) n)
    {μ : ℂ} (hμ : μ ^ n = 1) :
    μ ∈ φ.range := by
  -- Every n-th root of unity is a power of the primitive root ζ = φ(zeta).
  obtain ⟨k, _, hk⟩ := hφ.eq_pow_of_pow_eq_one hμ
  refine ⟨IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ) ^ k, ?_⟩
  rw [map_pow]
  exact hk

@[eval_problem]
theorem brauer_character_in_cyclotomic
    (G : Type) [Group G] [Fintype G] :
    ∃ φ : CyclotomicField (Monoid.exponent G) ℚ →+* ℂ,
      ∀ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
        (ρ : Representation ℂ G V) (g : G),
        LinearMap.trace ℂ V (ρ g) ∈ φ.range := by
  set n := Monoid.exponent G with hn
  -- n > 0 because G is finite
  have hnpos : 0 < n := by
    have hExp : Monoid.ExponentExists G :=
      Monoid.ExponentExists.of_finite
    rw [Monoid.exponent_pos]
    exact hExp
  have hnz : n ≠ 0 := by exact Nat.pos_iff_ne_zero.mp hnpos
  have hNeZero_n : NeZero n := ⟨hnz⟩
  have hnzq : NeZero ((n : ℕ) : ℚ) :=
    ⟨by
      have : (n : ℚ) ≠ 0 := by exact mod_cast hnz
      exact this⟩
  -- Provide the NeZero instances as typeclass arguments
  haveI : NeZero n := hNeZero_n
  haveI : NeZero ((n : ℕ) : ℚ) := hnzq
  -- The CyclotomicField is a cyclotomic extension (uses NeZero (n : ℚ)).
  haveI : IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ) :=
    CyclotomicField.isCyclotomicExtension n ℚ
  -- Get the cyclotomic embedding
  rcases cyclotomic_embedding n with ⟨φ, hφ⟩
  refine ⟨φ, λ V _ _ _ ρ g => ?_⟩
  -- Rewrite the trace as a sum of roots of the characteristic polynomial
  rw [trace_eq_sum_charpoly_roots (ρ g)]
  -- Every root of the characteristic polynomial is an n-th root of unity
  have hroots : ∀ a ∈ ((ρ g).charpoly).roots, a ∈ φ.range := by
    intro a ha
    have hp_ne_zero : (ρ g).charpoly ≠ 0 := by
      have hm : (ρ g).charpoly.Monic := LinearMap.charpoly_monic _
      exact hm.ne_zero
    have hIsRoot : ((ρ g).charpoly).IsRoot a :=
      ((Polynomial.mem_roots hp_ne_zero).mp ha)
    have hpower : a ^ n = 1 := by
      simpa [hn] using charpoly_roots_roots_of_unity ρ g hIsRoot
    -- By range_contains_roots_of_unity, every n-th root of unity is in φ.range
    exact range_contains_roots_of_unity n φ hφ hpower
  -- The multiset sum of elements of φ.range is in φ.range
  exact Subring.multiset_sum_mem φ.range ((ρ g).charpoly).roots hroots

end RepresentationTheory
end LeanEval
