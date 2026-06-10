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
  sorry

/-- The polynomial `X ^ n - 1` (with `n = exponent G`) annihilates `ρ g`. -/
theorem annihilating_polynomial
    {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    (Polynomial.aeval (ρ g))
        (Polynomial.X ^ (Monoid.exponent G) - 1 : Polynomial ℂ) = 0 := by
  sorry

/-- The characteristic polynomial of any endomorphism of a finite-dimensional
`ℂ`-vector space splits over `ℂ`. -/
theorem charpoly_splits
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) :
    f.charpoly.Splits := by
  sorry

/-- Every root of the characteristic polynomial of `ρ g` is an
`(exponent G)`-th root of unity in `ℂ`. -/
theorem charpoly_roots_roots_of_unity
    {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) {lam : ℂ}
    (h : (ρ g).charpoly.IsRoot lam) :
    lam ^ (Monoid.exponent G) = 1 := by
  sorry

/-- The trace of an endomorphism of a finite-dimensional `ℂ`-vector space
equals the sum (with multiplicity) of the roots of its characteristic
polynomial. -/
theorem trace_eq_sum_charpoly_roots
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) :
    LinearMap.trace ℂ V f = f.charpoly.roots.sum := by
  sorry

/-- For every positive natural number `n`, there is a primitive `n`-th root
of unity in `ℂ`. -/
theorem complex_primitive_root (n : ℕ) (hn : 0 < n) :
    ∃ ζ : ℂ, IsPrimitiveRoot ζ n := by
  sorry

/-- For every positive natural number `n`, there is a ring homomorphism
`φ : CyclotomicField n ℚ →+* ℂ` sending the canonical primitive root
`IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ)` to a primitive
`n`-th root of unity in `ℂ`. -/
theorem cyclotomic_embedding (n : ℕ) [NeZero n] [NeZero ((n : ℕ) : ℚ)]
    [IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ)] :
    ∃ φ : CyclotomicField n ℚ →+* ℂ,
      IsPrimitiveRoot
        (φ (IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ))) n := by
  sorry

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
  sorry

@[eval_problem]
theorem brauer_character_in_cyclotomic
    (G : Type) [Group G] [Fintype G] :
    ∃ φ : CyclotomicField (Monoid.exponent G) ℚ →+* ℂ,
      ∀ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
        (ρ : Representation ℂ G V) (g : G),
        LinearMap.trace ℂ V (ρ g) ∈ φ.range := by
  sorry

end RepresentationTheory
end LeanEval
