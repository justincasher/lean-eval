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
  have h : Algebra.IsAlgebraic ℚ (CyclotomicField n ℚ) := by
    infer_instance
  have φ_alg : CyclotomicField n ℚ →ₐ[ℚ] ℂ :=
    IsAlgClosed.lift (R := ℚ) (S := CyclotomicField n ℚ) (M := ℂ)
  refine ⟨φ_alg.toRingHom, ?_⟩
  exact (RingHom.injective _)

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
  have hz0 : z ≠ 0 := by
    intro hzero
    have : z ^ n = 0 := by
      rw [hzero, zero_pow (NeZero.ne n)]
    rw [this] at hz
    exact one_ne_zero hz.symm
  let u : ℂˣ := Units.mk0 z hz0
  have hu_val : (u : ℂ) = z := by
    simp [u]
  have hu_root : u ∈ rootsOfUnity n ℂ := by
    rw [mem_rootsOfUnity]
    have h_unit_pow_val : (u ^ n : ℂ) = (1 : ℂ) := by
      calc
        (u ^ n : ℂ) = ((u : ℂ) ^ n) := by simp
        _ = z ^ n := by rw [hu_val]
        _ = 1 := hz
    exact Units.ext h_unit_pow_val
  exact ⟨u, hu_val, hu_root⟩

/-- **Roots of unity lie in a subring containing a primitive root.**
Let `n ≠ 0`, let `S ⊆ ℂ` be a subring, and let `ζ ∈ S` be a primitive `n`-th
root of unity. Then every `z ∈ ℂ` with `zⁿ = 1` belongs to `S`. -/
theorem rootsOfUnity_mem (n : ℕ) [NeZero n] (S : Subring ℂ) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ n) (hζS : ζ ∈ S) {z : ℂ} (hz : z ^ n = 1) :
    z ∈ S := by
  -- from hz, get a unit u with (u : ℂ) = z and u ∈ rootsOfUnity n ℂ
  rcases mem_rootsOfUnity_of_pow_eq_one n hz with ⟨u, hu, huR⟩
  -- lift ζ to a unit
  have hζu : IsUnit ζ := hζ.isUnit (NeZero.ne n)
  let ζu : ℂˣ := hζu.unit
  have hζu_spec : (ζu : ℂ) = ζ := hζu.unit_spec
  have hζu_prim : IsPrimitiveRoot ζu n :=
    (IsPrimitiveRoot.coe_units_iff (ζ := ζu)).mp (by simpa [hζu_spec] using hζ)
  -- ζ^some power = u as units
  rcases hζu_prim.eq_pow_of_mem_rootsOfUnity huR with ⟨i, hi, hpow⟩
  -- convert back to ℂ and use Subring.pow_mem
  have hz_eq : z = ζ ^ i := by
    calc
      z = (u : ℂ) := hu.symm
      _ = ((ζu ^ i : ℂˣ) : ℂ) := by simpa [hpow]
      _ = (ζu : ℂ) ^ i := by simp
      _ = ζ ^ i := by simp [hζu_spec]
  rw [hz_eq]
  exact Subring.pow_mem S hζS i

/-- **The image of `g` has finite order.**
Let `ρ` be a complex representation of `G` on `V` and `g ∈ G`. Then
`ρ(g) ^ exp(G) = 1` as an endomorphism of `V`. -/
theorem rho_pow_exponent {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ G V) (g : G) :
    (ρ g) ^ (Monoid.exponent G) = 1 := by
  rw [← map_pow, Monoid.pow_exponent_eq_one g, map_one]

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
  have h_eig : T.HasEigenvalue μ :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly T μ).mpr hμ
  have h_eig_pow : (T ^ n).HasEigenvalue (μ ^ n) :=
    h_eig.pow n
  rw [hT] at h_eig_pow
  exact eigenvalue_id_eq_one h_eig_pow

/-- **Roots of the characteristic polynomial lie in the subring.**
Let `V` be finite-dimensional over `ℂ`, `T : V → V` linear with `Tⁿ = 1` for some
`n ≠ 0`, and `S ⊆ ℂ` a subring containing a primitive `n`-th root of unity `ζ`.
Then every `r` in the multiset of roots of the characteristic polynomial of `T`
lies in `S`. -/
theorem charpoly_roots_mem_range {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (T : Module.End ℂ V) {n : ℕ} (hn : n ≠ 0)
    (hT : T ^ n = 1) (S : Subring ℂ) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n)
    (hζS : ζ ∈ S) {r : ℂ} (hr : r ∈ T.charpoly.roots) : r ∈ S := by
  have hmonic : T.charpoly.Monic := LinearMap.charpoly_monic T
  have hp_ne_zero : T.charpoly ≠ 0 := hmonic.ne_zero
  have h_is_root : T.charpoly.IsRoot r := ((Polynomial.mem_roots hp_ne_zero).mp hr)
  have h_pow : r ^ n = 1 := eigenvalue_root_of_unity T hn hT h_is_root
  haveI : NeZero n := ⟨hn⟩
  exact rootsOfUnity_mem n S hζ hζS h_pow

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
