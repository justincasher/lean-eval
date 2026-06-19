import Mathlib
import EvalTools.Markers

namespace LeanEval
namespace GroupTheory

/-!
# Brauer–Fowler theorem

Let `G` be a finite simple group with an involution `t`. Then `|G|` is
bounded by a function of `|C_G(t)|` alone. Equivalently: for each `n`,
only finitely many finite nonabelian simple groups have an involution
whose centralizer has order `n`.

Stated by Richard Brauer in 1954 (with Fowler) as a key motivation for
the project of classifying finite simple groups: it reduces the
classification (in principle) to studying involution centralizers, a
much smaller class of groups. The first general involution-centralizer
analyses (Brauer–Suzuki, Brauer–Suzuki–Wall, Janko) used this principle
to discover several sporadic simple groups, and it remained one of the
central organising ideas of the CFSG programme.

The bound `f` is not specified — any concrete bound suffices, the
classical Brauer–Fowler bound being roughly `(n^2)!`. The statement
quantifies over all finite simple groups `G` in a fixed universe.

The proof is short and uses only counting / orbit-counting arguments
together with the observation that any two involutions generate a
dihedral subgroup; no deep machinery is required.
-/

variable {G : Type*} [Group G]

/-! ## Basic definitions -/

open scoped Classical in
/-- **Set of involutions.** The finite set `{g : G | orderOf g = 2}` of
involutions of a finite group `G`, as a `Finset G`. -/
noncomputable def involutionSet (G : Type*) [Group G] [Fintype G] : Finset G :=
  Finset.univ.filter (fun g => orderOf g = 2)

/-- **Number of involutions.** `k = |𝓘|`, the cardinality of the set of
involutions of `G`. -/
noncomputable def numInvolutions (G : Type*) [Group G] [Fintype G] : ℕ :=
  (involutionSet G).card

open scoped Classical in
/-- **Involution-pair count.** For `x : G`, the number of ordered pairs
`(a, b)` of involutions with `a * b = x`. -/
noncomputable def involutionPairCount (G : Type*) [Group G] [Fintype G] (x : G) : ℕ :=
  ((involutionSet G ×ˢ involutionSet G).filter (fun p => p.1 * p.2 = x)).card

/-! ## Group-theoretic preliminaries -/

/-- **Conjugates of an involution are involutions.** If `orderOf a = 2`
then `orderOf (g * a * g⁻¹) = 2`. -/
theorem orderOf_conj_eq_two {g a : G} (ha : orderOf a = 2) :
    orderOf (g * a * g⁻¹) = 2 := by
  sorry

/-- **An involution is its own inverse.** If `orderOf a = 2` then
`a⁻¹ = a` and consequently `a * a = 1`. -/
theorem inv_eq_and_mul_self_eq_one {a : G} (ha : orderOf a = 2) :
    a⁻¹ = a ∧ a * a = 1 := by
  sorry

/-- **The center of a nonabelian simple group is trivial.** -/
theorem center_eq_bot [IsSimpleGroup G] (h : ∃ a b : G, a * b ≠ b * a) :
    Subgroup.center G = ⊥ := by
  sorry

/-- **Centralizers of non-identity elements are proper.** In a nonabelian
simple group, for `x ≠ 1` the centralizer `C_G(x)` is a proper subgroup and
has order strictly less than `|G|`. -/
theorem centralizer_lt_top_of_ne_one [IsSimpleGroup G] [Finite G]
    (h : ∃ a b : G, a * b ≠ b * a) {x : G} (hx : x ≠ 1) :
    Subgroup.centralizer ({x} : Set G) < ⊤ ∧
      Nat.card (Subgroup.centralizer ({x} : Set G)) < Nat.card G := by
  sorry

/-! ## Embedding a simple group via a proper subgroup -/

/-- **Trivial normal core of a proper subgroup.** In a simple group, the
normal core of a proper subgroup is trivial. -/
theorem normalCore_eq_bot [IsSimpleGroup G] {H : Subgroup G} (hH : H < ⊤) :
    H.normalCore = ⊥ := by
  sorry

/-- **The coset permutation representation is injective.** In a simple group,
the action of `G` on the coset space `G ⧸ H` of a proper subgroup `H` gives an
injective permutation representation. -/
theorem toPermHom_injective [IsSimpleGroup G] {H : Subgroup G} (hH : H < ⊤) :
    Function.Injective (MulAction.toPermHom G (G ⧸ H)) := by
  sorry

/-- **Order bound from a proper subgroup.** A finite simple group embeds into
the symmetric group on the cosets of a proper subgroup, so `|G| ≤ [G : H]!`. -/
theorem card_le_index_factorial [IsSimpleGroup G] [Finite G] {H : Subgroup G}
    (hH : H < ⊤) : Nat.card G ≤ Nat.factorial H.index := by
  sorry

/-! ## Counting involutions -/

/-- **Conjugacy class size times centralizer order.** For any `g : G`, the
orbit of `g` under the conjugation action of `G` times the order of its
centralizer equals `|G|`. -/
theorem card_orbit_mul_card_centralizer [Finite G] (g : G) :
    Nat.card (MulAction.orbit (ConjAct G) g) *
      Nat.card (Subgroup.centralizer ({g} : Set G)) = Nat.card G := by
  sorry

/-- **Many involutions.** With `t` an involution, `n ≤ k * c` where
`k = numInvolutions G` and `c = |C_G(t)|`. -/
theorem card_le_numInvolutions_mul_centralizer [Fintype G] {t : G}
    (ht : orderOf t = 2) :
    Nat.card G ≤
      numInvolutions G * Nat.card (Subgroup.centralizer ({t} : Set G)) := by
  sorry

/-- **At least two involutions.** A nonabelian simple group with an involution
has at least two involutions. -/
theorem two_le_numInvolutions [IsSimpleGroup G] [Fintype G]
    (h : ∃ a b : G, a * b ≠ b * a) {t : G} (ht : orderOf t = 2) :
    2 ≤ numInvolutions G := by
  sorry

/-- **Pairs with product `1` are the diagonal.** `r(1) = k`. -/
theorem involutionPairCount_one [Fintype G] :
    involutionPairCount G 1 = numInvolutions G := by
  sorry

/-- **Total number of involution pairs.** `∑ x, r(x) = k²`. -/
theorem sum_involutionPairCount [Fintype G] :
    ∑ x : G, involutionPairCount G x = numInvolutions G ^ 2 := by
  sorry

open scoped Classical in
/-- **Counting involution pairs by their product.** `∑_{x ≠ 1} r(x) = k² - k`. -/
theorem sum_involutionPairCount_erase_one [Fintype G] :
    ∑ x ∈ Finset.univ.erase (1 : G), involutionPairCount G x =
      numInvolutions G ^ 2 - numInvolutions G := by
  sorry

/-- **An involution factor inverts the product.** If `a, b` are involutions
and `a * b = x`, then `a * x * a⁻¹ = x⁻¹`. -/
theorem inverts_of_mul_eq {a b x : G} (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hab : a * b = x) : a * x * a⁻¹ = x⁻¹ := by
  sorry

open scoped Classical in
/-- **Factorizations are indexed by their first factor.** For every `x`,
`r(x)` equals the number of involutions `a` with `a * x` also an involution. -/
theorem involutionPairCount_eq_filter [Fintype G] (x : G) :
    involutionPairCount G x =
      ((involutionSet G).filter (fun a => a * x ∈ involutionSet G)).card := by
  sorry

/-- **Common inverters differ by a centralizing element.** If both `a` and `a₀`
invert `x`, then `a₀⁻¹ * a` centralizes `x`. -/
theorem inv_mul_mem_centralizer {x a a₀ : G} (ha : a * x * a⁻¹ = x⁻¹)
    (ha₀ : a₀ * x * a₀⁻¹ = x⁻¹) :
    a₀⁻¹ * a ∈ Subgroup.centralizer ({x} : Set G) := by
  sorry

/-- **The inverter map injects into the centralizer.** With `a₀` inverting `x`
and `S` a set of inverters of `x`, the map `a ↦ a₀⁻¹ * a` is injective on `S`
and lands in `C_G(x)`. -/
theorem inverter_map_injOn_centralizer {x a₀ : G} (S : Set G)
    (ha₀ : a₀ * x * a₀⁻¹ = x⁻¹) (hS : ∀ a ∈ S, a * x * a⁻¹ = x⁻¹) :
    Set.InjOn (fun a => a₀⁻¹ * a) S ∧
      ∀ a ∈ S, a₀⁻¹ * a ∈ Subgroup.centralizer ({x} : Set G) := by
  sorry

/-- **Few factorizations of a fixed product.** For every `x`,
`r(x) ≤ |C_G(x)|`. -/
theorem involutionPairCount_le_centralizer [Fintype G] (x : G) :
    involutionPairCount G x ≤ Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  sorry

open scoped Classical in
/-- **Averaging over the non-identity elements.** For a nontrivial group there
is some `x ≠ 1` with `(n - 1) * r(x) ≥ ∑_{x ≠ 1} r(x)`. -/
theorem exists_averaging [Fintype G] (hG : Nontrivial G) :
    ∃ x : G, x ≠ 1 ∧
      ∑ y ∈ Finset.univ.erase (1 : G), involutionPairCount G y ≤
        (Nat.card G - 1) * involutionPairCount G x := by
  sorry

/-- **Some element has a large centralizer.** There is `x ≠ 1` with
`(n - 1) * |C_G(x)| ≥ k² - k`. -/
theorem exists_big_centralizer [IsSimpleGroup G] [Fintype G] :
    ∃ x : G, x ≠ 1 ∧
      numInvolutions G ^ 2 - numInvolutions G ≤
        (Nat.card G - 1) * Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  sorry

/-! ## The bound -/

/-- **Arithmetic of the index bound.** A purely arithmetic inequality packaging
the final counting estimate: it yields `m ≤ 2 c²`. -/
theorem index_arith {n k c d m : ℕ} (hn : 2 ≤ n) (hk : 2 ≤ k) (hd : 1 ≤ d)
    (hnkc : n ≤ k * c) (hk2 : k ^ 2 ≤ (n - 1) * d + k) (hmd : m * d = n) :
    m ≤ 2 * c ^ 2 := by
  sorry

/-- **Explicit order bound.** For a finite nonabelian simple group `G` and an
involution `t`, `|G| ≤ (2 c²)!` where `c = |C_G(t)|`. -/
theorem order_bound [IsSimpleGroup G] [Fintype G] (h : ∃ a b : G, a * b ≠ b * a)
    {t : G} (ht : orderOf t = 2) :
    Nat.card G ≤
      Nat.factorial (2 * Nat.card (Subgroup.centralizer ({t} : Set G)) ^ 2) := by
  sorry

/-- **Brauer–Fowler theorem.** There is a function bounding the order
of a finite nonabelian simple group by the order of any involution
centralizer. -/
@[eval_problem]
theorem brauer_fowler :
    ∃ f : ℕ → ℕ, ∀ (G : Type) [Group G] [Finite G],
      IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
      ∀ t : G, orderOf t = 2 →
        Nat.card G ≤ f (Nat.card (Subgroup.centralizer ({t} : Set G))) := by
  sorry

end GroupTheory
end LeanEval
