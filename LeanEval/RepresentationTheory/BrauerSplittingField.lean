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

The argument is elementary and does not use Brauer's induction theorem: since
`gⁿ = 1`, the operator `ρ(g)` satisfies `ρ(g)ⁿ = 1`, so each of its eigenvalues
is an `n`-th root of unity. The trace is the sum of these eigenvalues, and the
range of `φ` is a subring of `ℂ` containing every `n`-th root of unity.
-/

/-- **Injective embedding of the cyclotomic field.**
Let `n ≠ 0`. There is an injective ring homomorphism `ℚ(ζₙ) → ℂ`. -/
theorem cyclotomic_embeds_injective (n : ℕ) [NeZero n] :
    ∃ φ : CyclotomicField n ℚ →+* ℂ, Function.Injective φ := by
  sorry

/-- **Embedding carrying a primitive root.**
Let `n ≠ 0`. There is a ring embedding `φ : ℚ(ζₙ) → ℂ` and an element `ζ ∈ ℂ`
such that `ζ` is a primitive `n`-th root of unity and `ζ` lies in the range of
`φ`. -/
theorem embedding_primitive_root (n : ℕ) [NeZero n] :
    ∃ (φ : CyclotomicField n ℚ →+* ℂ) (ζ : ℂ),
      IsPrimitiveRoot ζ n ∧ ζ ∈ φ.range := by
  sorry

/-- **A complex `n`-th root of unity is a member of `rootsOfUnity`.**
Let `n ≠ 0` and `z ∈ ℂ` with `zⁿ = 1`. Then `z` is a unit `u` of `ℂ`, and that
unit lies in `rootsOfUnity n ℂ`. -/
theorem mem_rootsOfUnity_of_pow_eq_one (n : ℕ) [NeZero n] {z : ℂ} (hz : z ^ n = 1) :
    ∃ u : ℂˣ, (u : ℂ) = z ∧ u ∈ rootsOfUnity n ℂ := by
  sorry

/-- **Roots of unity lie in a subring containing a primitive root.**
Let `n ≠ 0`, let `S ⊆ ℂ` be a subring, and let `ζ ∈ S` be a primitive `n`-th
root of unity. Then every `z ∈ ℂ` with `zⁿ = 1` belongs to `S`. -/
theorem rootsOfUnity_mem (n : ℕ) [NeZero n] (S : Subring ℂ) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ n) (hζS : ζ ∈ S) {z : ℂ} (hz : z ^ n = 1) :
    z ∈ S := by
  sorry

/-- **The image of `g` has finite order.**
Let `ρ` be a complex representation of `G` on `V` and `g ∈ G`. Then
`ρ(g) ^ exp(G) = 1` as an endomorphism of `V`. -/
theorem rho_pow_exponent {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ G V) (g : G) :
    (ρ g) ^ (Monoid.exponent G) = 1 := by
  sorry

/-- **The only eigenvalue of the identity is one.**
If the identity endomorphism `1 : V → V` has eigenvalue `c`, then `c = 1`. -/
theorem eigenvalue_id_eq_one {V : Type*} [AddCommGroup V] [Module ℂ V] {c : ℂ}
    (h : Module.End.HasEigenvalue (1 : Module.End ℂ V) c) : c = 1 := by
  sorry

/-- **Eigenvalues of a finite-order operator are roots of unity.**
Let `V` be finite-dimensional over `ℂ`, let `T : V → V` be linear, and `n ≠ 0`
with `Tⁿ = 1`. Then every root `μ` of the characteristic polynomial of `T`
satisfies `μⁿ = 1`. -/
theorem eigenvalue_root_of_unity {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (T : Module.End ℂ V) {n : ℕ} (hn : n ≠ 0)
    (hT : T ^ n = 1) {μ : ℂ} (hμ : T.charpoly.IsRoot μ) : μ ^ n = 1 := by
  sorry

/-- **Roots of the characteristic polynomial lie in the subring.**
Let `V` be finite-dimensional over `ℂ`, `T : V → V` linear with `Tⁿ = 1` for some
`n ≠ 0`, and `S ⊆ ℂ` a subring containing a primitive `n`-th root of unity `ζ`.
Then every `r` in the multiset of roots of the characteristic polynomial of `T`
lies in `S`. -/
theorem charpoly_roots_mem_range {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (T : Module.End ℂ V) {n : ℕ} (hn : n ≠ 0)
    (hT : T ^ n = 1) (S : Subring ℂ) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n)
    (hζS : ζ ∈ S) {r : ℂ} (hr : r ∈ T.charpoly.roots) : r ∈ S := by
  sorry

/-- **Character values lie in a cyclotomic field.**
Let `G` be a finite group with exponent `n = exp(G)`. There is a ring embedding
`φ : ℚ(ζₙ) → ℂ` such that for every finite-dimensional complex representation `ρ`
of `G` on a space `V` and every `g ∈ G`, the trace `tr_ℂ(ρ(g))` lies in the
range of `φ`. -/
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
