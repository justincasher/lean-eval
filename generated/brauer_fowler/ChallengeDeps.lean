import Mathlib

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
  have hsc : SemiconjBy g a (g * a * g⁻¹) := by
    calc
      g * a = g * a * 1 := by simp
      _ = g * a * (g⁻¹ * g) := by simp
      _ = (g * a * g⁻¹) * g := by group
  have h_eq := (SemiconjBy.orderOf_eq g hsc).symm
  rw [h_eq, ha]

/-- **An involution is its own inverse.** If `orderOf a = 2` then
`a⁻¹ = a` and consequently `a * a = 1`. -/
theorem inv_eq_and_mul_self_eq_one {a : G} (ha : orderOf a = 2) :
    a⁻¹ = a ∧ a * a = 1 := by
  have hinv : a⁻¹ = a := inv_eq_self_of_orderOf_eq_two ha
  have hmul : a * a = 1 :=
    calc
      a * a = a * a⁻¹ := congrArg (a * ·) hinv.symm
      _ = 1 := mul_inv_cancel a
  exact ⟨hinv, hmul⟩

/-- **The center of a nonabelian simple group is trivial.** -/
theorem center_eq_bot [IsSimpleGroup G] (h : ∃ a b : G, a * b ≠ b * a) :
    Subgroup.center G = ⊥ := by
  have hn : (Subgroup.center G).Normal := inferInstance
  rcases hn.eq_bot_or_eq_top with hbot | htop
  · exact hbot
  · have hcomm : IsMulCommutative G := (Subgroup.center_eq_top_iff.mp htop)
    rcases h with ⟨a, b, hneq⟩
    have h_eq : a * b = b * a := hcomm.is_comm.comm a b
    exact absurd h_eq hneq

/-- **Centralizers of non-identity elements are proper.** In a nonabelian
simple group, for `x ≠ 1` the centralizer `C_G(x)` is a proper subgroup and
has order strictly less than `|G|`. -/
theorem centralizer_lt_top_of_ne_one [IsSimpleGroup G] [Finite G]
    (h : ∃ a b : G, a * b ≠ b * a) {x : G} (hx : x ≠ 1) :
    Subgroup.centralizer ({x} : Set G) < ⊤ ∧
      Nat.card (Subgroup.centralizer ({x} : Set G)) < Nat.card G := by
  have h_ne_top : Subgroup.centralizer ({x} : Set G) ≠ ⊤ := by
    intro h_eq
    have hx_mem_center : x ∈ Subgroup.center G := by
      have h_subset : ({x} : Set G) ⊆ Subgroup.center G :=
        (Subgroup.centralizer_eq_top_iff_subset.mp h_eq)
      simpa using h_subset
    have hZ : Subgroup.center G = ⊥ := center_eq_bot h
    have hx_one : x = 1 := Subgroup.mem_bot.mp (by
      rw [← hZ]
      exact hx_mem_center)
    exact hx hx_one
  have hCx : Subgroup.centralizer ({x} : Set G) < ⊤ :=
    lt_of_le_of_ne (le_top : Subgroup.centralizer ({x} : Set G) ≤ ⊤) h_ne_top
  have h_card : Nat.card (Subgroup.centralizer ({x} : Set G)) < Nat.card G := by
    have h_card_le : Nat.card (Subgroup.centralizer ({x} : Set G)) ≤ Nat.card G :=
      Subgroup.card_le_card_group (Subgroup.centralizer ({x} : Set G))
    by_contra! h_not_lt
    have h_card_eq : Nat.card (Subgroup.centralizer ({x} : Set G)) = Nat.card G := by
      omega
    have h_top : Subgroup.centralizer ({x} : Set G) = ⊤ :=
      Subgroup.eq_top_of_card_eq (Subgroup.centralizer ({x} : Set G)) h_card_eq
    exact h_ne_top h_top
  exact ⟨hCx, h_card⟩

/-! ## Embedding a simple group via a proper subgroup -/

/-- **Trivial normal core of a proper subgroup.** In a simple group, the
normal core of a proper subgroup is trivial. -/
theorem normalCore_eq_bot [IsSimpleGroup G] {H : Subgroup G} (hH : H < ⊤) :
    H.normalCore = ⊥ := by
  have hcore_normal : (H.normalCore).Normal := Subgroup.normalCore_normal H
  rcases hcore_normal.eq_bot_or_eq_top with h | h
  · exact h
  · have hle : H.normalCore ≤ H := Subgroup.normalCore_le H
    have htop : H = ⊤ := le_antisymm (le_of_lt hH) (h.symm ▸ hle)
    exact absurd htop hH.ne

/-- **The coset permutation representation is injective.** In a simple group,
the action of `G` on the coset space `G ⧸ H` of a proper subgroup `H` gives an
injective permutation representation. -/
theorem toPermHom_injective [IsSimpleGroup G] {H : Subgroup G} (hH : H < ⊤) :
    Function.Injective (MulAction.toPermHom G (G ⧸ H)) := by
  have hker : (MulAction.toPermHom G (G ⧸ H)).ker = ⊥ := by
    calc
      (MulAction.toPermHom G (G ⧸ H)).ker = H.normalCore := by
        rw [Subgroup.normalCore_eq_ker]
      _ = ⊥ := normalCore_eq_bot hH
  exact ((MonoidHom.ker_eq_bot_iff (MulAction.toPermHom G (G ⧸ H))).mp hker)

/-- **Order bound from a proper subgroup.** A finite simple group embeds into
the symmetric group on the cosets of a proper subgroup, so `|G| ≤ [G : H]!`. -/
theorem card_le_index_factorial [IsSimpleGroup G] [Finite G] {H : Subgroup G}
    (hH : H < ⊤) : Nat.card G ≤ Nat.factorial H.index := by
  have hinj : Function.Injective (MulAction.toPermHom G (G ⧸ H)) :=
    toPermHom_injective hH
  have hcard : Nat.card G ≤ Nat.card (Equiv.Perm (G ⧸ H)) :=
    Nat.card_le_card_of_injective (MulAction.toPermHom G (G ⧸ H)) hinj
  calc
    Nat.card G ≤ Nat.card (Equiv.Perm (G ⧸ H)) := hcard
    _ = Nat.factorial (Nat.card (G ⧸ H)) := Nat.card_perm
    _ = Nat.factorial H.index := by rfl

/-! ## Counting involutions -/

/-- **Conjugacy class size times centralizer order.** For any `g : G`, the
orbit of `g` under the conjugation action of `G` times the order of its
centralizer equals `|G|`. -/
theorem card_orbit_mul_card_centralizer [Finite G] (g : G) :
    Nat.card (MulAction.orbit (ConjAct G) g) *
      Nat.card (Subgroup.centralizer ({g} : Set G)) = Nat.card G := by
  haveI : Fintype G := Fintype.ofFinite _
  haveI : Fintype (ConjAct G) := inferInstance
  haveI : Fintype (MulAction.orbit (ConjAct G) g) := Fintype.ofFinite _
  haveI : Fintype (MulAction.stabilizer (ConjAct G) g) := Fintype.ofFinite _
  calc
    Nat.card (MulAction.orbit (ConjAct G) g) * Nat.card (Subgroup.centralizer ({g} : Set G))
        = Fintype.card (MulAction.orbit (ConjAct G) g) * Nat.card (Subgroup.centralizer ({g} : Set G)) := by
          rw [Nat.card_eq_fintype_card]
    _ = Fintype.card (MulAction.orbit (ConjAct G) g) * Nat.card (MulAction.stabilizer (ConjAct G) g) := by
      rw [Subgroup.nat_card_centralizer_nat_card_stabilizer g]
    _ = Fintype.card (MulAction.orbit (ConjAct G) g) * Fintype.card (MulAction.stabilizer (ConjAct G) g) := by
      rw [Nat.card_eq_fintype_card]
    _ = Fintype.card (ConjAct G) :=
      MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) g
    _ = Fintype.card G := by
      convert ConjAct.card
    _ = Nat.card G := by simp

/-- **Many involutions.** With `t` an involution, `n ≤ k * c` where
`k = numInvolutions G` and `c = |C_G(t)|`. -/
theorem card_le_numInvolutions_mul_centralizer [Fintype G] {t : G}
    (ht : orderOf t = 2) :
    Nat.card G ≤
      numInvolutions G * Nat.card (Subgroup.centralizer ({t} : Set G)) := by
  -- orbit-stabilizer: |G| = |t^G| * |C_G(t)|
  have horbit_mul_c : Nat.card (MulAction.orbit (ConjAct G) t) *
      Nat.card (Subgroup.centralizer ({t} : Set G)) = Nat.card G :=
    card_orbit_mul_card_centralizer t
  -- conjugates of t are involutions
  have horbit_subset : MulAction.orbit (ConjAct G) t ⊆ (involutionSet G : Set G) := by
    intro x hx
    rcases MulAction.mem_orbit_iff.mp hx with ⟨g, hg⟩
    -- hg : g • t = x  (where g : ConjAct G)
    have hx_order : orderOf (g • t) = 2 := by
      simpa [ConjAct.smul_def] using orderOf_conj_eq_two ht
    have hx_order_x : orderOf x = 2 := by
      simpa [hg] using hx_order
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx_order_x⟩
  -- So |t^G| ≤ |I| = k
  have h_card_orbit_le_k : Nat.card (MulAction.orbit (ConjAct G) t) ≤ numInvolutions G := by
    have h_finite_inv : ((involutionSet G : Set G)).Finite := by
      exact Finset.finite_toSet _
    have h_card_orbit_le_card_inv :
      Nat.card (MulAction.orbit (ConjAct G) t) ≤ Nat.card ((involutionSet G : Set G)) :=
      Nat.card_mono h_finite_inv horbit_subset
    have h_card_inv_eq_num : Nat.card ((involutionSet G : Set G)) = numInvolutions G := by
      calc
        Nat.card ((involutionSet G : Set G)) = (involutionSet G).card := by simp
        _ = numInvolutions G := rfl
    calc
      Nat.card (MulAction.orbit (ConjAct G) t) ≤ Nat.card ((involutionSet G : Set G)) :=
        h_card_orbit_le_card_inv
      _ = numInvolutions G := h_card_inv_eq_num
  -- Combine: n = |t^G| * c ≤ k * c
  calc
    Nat.card G = Nat.card (MulAction.orbit (ConjAct G) t) *
      Nat.card (Subgroup.centralizer ({t} : Set G)) := by
      symm; exact horbit_mul_c
    _ ≤ numInvolutions G * Nat.card (Subgroup.centralizer ({t} : Set G)) :=
      Nat.mul_le_mul h_card_orbit_le_k (le_refl _)

/-- **At least two involutions.** A nonabelian simple group with an involution
has at least two involutions. -/
theorem two_le_numInvolutions [IsSimpleGroup G] [Fintype G]
    (h : ∃ a b : G, a * b ≠ b * a) {t : G} (ht : orderOf t = 2) :
    2 ≤ numInvolutions G := by
  have hx : t ≠ 1 := by
    intro h_eq
    rw [h_eq, orderOf_one] at ht
    omega
  have hc_lt_n : Nat.card (Subgroup.centralizer ({t} : Set G)) < Nat.card G :=
    (centralizer_lt_top_of_ne_one h hx).2
  have h_orbit_mul : Nat.card (MulAction.orbit (ConjAct G) t) *
    Nat.card (Subgroup.centralizer ({t} : Set G)) = Nat.card G :=
    card_orbit_mul_card_centralizer t
  have h_orb_ge_two : 2 ≤ Nat.card (MulAction.orbit (ConjAct G) t) := by
    by_contra! h
    have h_orb_le_one : Nat.card (MulAction.orbit (ConjAct G) t) ≤ 1 := by omega
    have h_mul_le' : Nat.card (MulAction.orbit (ConjAct G) t) *
      Nat.card (Subgroup.centralizer ({t} : Set G)) ≤
      Nat.card (Subgroup.centralizer ({t} : Set G)) := by
      calc
        Nat.card (MulAction.orbit (ConjAct G) t) *
          Nat.card (Subgroup.centralizer ({t} : Set G)) ≤
          1 * Nat.card (Subgroup.centralizer ({t} : Set G)) :=
          Nat.mul_le_mul h_orb_le_one (le_refl _)
        _ = Nat.card (Subgroup.centralizer ({t} : Set G)) := by simp
    rw [h_orbit_mul] at h_mul_le'
    omega
  have h_finite_orbit : Set.Finite (MulAction.orbit (ConjAct G) t) := Set.toFinite _
  haveI : Fintype (MulAction.orbit (ConjAct G) t) := h_finite_orbit.fintype
  have h_orbit_sub_inv : (MulAction.orbit (ConjAct G) t) ⊆ {g | orderOf g = 2} := by
    intro g hg
    rcases MulAction.mem_orbit_iff.mp hg with ⟨a, rfl⟩
    simpa [ConjAct.smul_def] using orderOf_conj_eq_two ht
  have h_orbit_finset_sub : Set.toFinset (MulAction.orbit (ConjAct G) t) ⊆ involutionSet G := by
    intro g hg
    have hg_orbit : g ∈ MulAction.orbit (ConjAct G) t := Set.mem_toFinset.mp hg
    have hg_order : orderOf g = 2 := h_orbit_sub_inv hg_orbit
    dsimp [involutionSet]
    simp [hg_order]
  have h_orbit_finset_card : (Set.toFinset (MulAction.orbit (ConjAct G) t)).card =
    Nat.card (MulAction.orbit (ConjAct G) t) := by
    simp
  have h_finset_orb_ge_two : 2 ≤ (Set.toFinset (MulAction.orbit (ConjAct G) t)).card := by
    rw [h_orbit_finset_card]
    exact h_orb_ge_two
  have h_card_le : (Set.toFinset (MulAction.orbit (ConjAct G) t)).card ≤ (involutionSet G).card :=
    Finset.card_le_card h_orbit_finset_sub
  have h_numInvolutions_eq : numInvolutions G = (involutionSet G).card := rfl
  omega

/-- **Pairs with product `1` are the diagonal.** `r(1) = k`. -/
theorem involutionPairCount_one [Fintype G] :
    involutionPairCount G 1 = numInvolutions G := by
  classical
  dsimp [involutionPairCount, numInvolutions]
  symm
  apply Finset.card_bij (fun a ha => (a, a))
  · intro a ha
    have ha_sq : a * a = 1 := (inv_eq_and_mul_self_eq_one
      ((Finset.mem_filter.mp ha).2)).2
    have hmem : (a, a) ∈ involutionSet G ×ˢ involutionSet G :=
      Finset.mem_product.mpr ⟨ha, ha⟩
    exact Finset.mem_filter.mpr ⟨hmem, ha_sq⟩
  · intro a ha b hb h
    exact congr_arg Prod.fst h
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp_mem, hp_prod⟩
    rcases Finset.mem_product.mp hp_mem with ⟨ha, hb⟩
    have ha_order : orderOf p.1 = 2 := (Finset.mem_filter.mp ha).2
    have ha_sq : p.1 * p.1 = 1 := (inv_eq_and_mul_self_eq_one ha_order).2
    have h_eq : p.1 = p.2 := mul_left_cancel (ha_sq.trans hp_prod.symm)
    refine ⟨p.1, ha, ?_⟩
    ext <;> simp [h_eq]

/-- **Total number of involution pairs.** `∑ x, r(x) = k²`. -/
theorem sum_involutionPairCount [Fintype G] :
    ∑ x : G, involutionPairCount G x = numInvolutions G ^ 2 := by
  classical
    let s : Finset (G × G) := involutionSet G ×ˢ involutionSet G
    have hMapsTo : (s : Set (G × G)).MapsTo (fun (p : G × G) => p.1 * p.2) (Finset.univ : Finset G) := by
      intro p hp
      simp
    have h_fiber : s.card = ∑ x : G, ((s.filter (fun (p : G × G) => p.1 * p.2 = x)).card) := by
      calc
        s.card = ∑ x ∈ (Finset.univ : Finset G), ((s.filter (fun (p : G × G) => p.1 * p.2 = x)).card) := by
          simpa using Finset.card_eq_sum_card_fiberwise hMapsTo
        _ = ∑ x : G, ((s.filter (fun (p : G × G) => p.1 * p.2 = x)).card) := by simp
    calc
      ∑ x : G, involutionPairCount G x = ∑ x : G, ((s.filter (fun (p : G × G) => p.1 * p.2 = x)).card) := rfl
      _ = s.card := by rw [h_fiber]
      _ = (involutionSet G).card * (involutionSet G).card := by
        rw [Finset.card_product]
      _ = numInvolutions G ^ 2 := by
        rw [numInvolutions, pow_two]

open scoped Classical in
/-- **Counting involution pairs by their product.** `∑_{x ≠ 1} r(x) = k² - k`. -/
theorem sum_involutionPairCount_erase_one [Fintype G] :
    ∑ x ∈ Finset.univ.erase (1 : G), involutionPairCount G x =
      numInvolutions G ^ 2 - numInvolutions G := by
  have h1 : (1 : G) ∈ Finset.univ := Finset.mem_univ _
  have h_add := Finset.add_sum_erase (Finset.univ : Finset G) (involutionPairCount G) h1
  have h_one : involutionPairCount G 1 = numInvolutions G := involutionPairCount_one
  have h_total : ∑ x : G, involutionPairCount G x = numInvolutions G ^ 2 := sum_involutionPairCount
  rw [h_one, h_total] at h_add
  omega

/-- **An involution factor inverts the product.** If `a, b` are involutions
and `a * b = x`, then `a * x * a⁻¹ = x⁻¹`. -/
theorem inverts_of_mul_eq {a b x : G} (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hab : a * b = x) : a * x * a⁻¹ = x⁻¹ := by
  have ha_sq : a * a = 1 := (inv_eq_and_mul_self_eq_one ha).2
  have ha_inv : a⁻¹ = a := inv_eq_self_of_orderOf_eq_two ha
  have hb_inv : b⁻¹ = b := inv_eq_self_of_orderOf_eq_two hb
  calc
    a * x * a⁻¹ = a * (a * b) * a⁻¹ := by rw [hab]
    _ = (a * a) * b * a⁻¹ := by simp [mul_assoc]
    _ = 1 * b * a⁻¹ := by rw [ha_sq]
    _ = b * a⁻¹ := by simp
    _ = b * a := by rw [ha_inv]
    _ = b⁻¹ * a⁻¹ := by rw [hb_inv, ha_inv]
    _ = (a * b)⁻¹ := by rw [mul_inv_rev a b]
    _ = x⁻¹ := by rw [hab]

open scoped Classical in
/-- **Factorizations are indexed by their first factor.** For every `x`,
`r(x)` equals the number of involutions `a` with `a * x` also an involution. -/
theorem involutionPairCount_eq_filter [Fintype G] (x : G) :
    involutionPairCount G x =
      ((involutionSet G).filter (fun a => a * x ∈ involutionSet G)).card := by
  unfold involutionPairCount
  set s := (involutionSet G ×ˢ involutionSet G).filter (fun p => p.1 * p.2 = x) with hs
  set t := (involutionSet G).filter (fun a => a * x ∈ involutionSet G) with ht
  have hst : s.card = t.card := by
    apply Finset.card_bij' (fun p hp => p.1) (fun a ha => (a, a * x))
    · -- hi: if p ∈ s, then p.1 ∈ t
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hp_mem, hp_eq⟩
      rcases Finset.mem_product.mp hp_mem with ⟨ha_mem, hb_mem⟩
      have ha_order : orderOf p.1 = 2 := by
        simpa [involutionSet] using ha_mem
      have ha_inv : p.1⁻¹ = p.1 := (inv_eq_and_mul_self_eq_one ha_order).1
      have hp2_eq : p.2 = p.1 * x := by
        calc
          p.2 = 1 * p.2 := by simp
          _ = (p.1⁻¹ * p.1) * p.2 := by simp
          _ = p.1⁻¹ * (p.1 * p.2) := by rw [mul_assoc]
          _ = p.1⁻¹ * x := by rw [hp_eq]
          _ = p.1 * x := by rw [ha_inv]
      have hax_mem : p.1 * x ∈ involutionSet G := by
        rw [← hp2_eq]
        exact hb_mem
      exact Finset.mem_filter.mpr ⟨ha_mem, hax_mem⟩
    · -- hj: if a ∈ t, then (a, a*x) ∈ s
      intro a ha
      rcases Finset.mem_filter.mp ha with ⟨ha_mem, hax_mem⟩
      have ha_order : orderOf a = 2 := by
        simpa [involutionSet] using ha_mem
      have ha_mul_self : a * a = 1 := (inv_eq_and_mul_self_eq_one ha_order).2
      have h_product : a * (a * x) = x := by
        calc
          a * (a * x) = (a * a) * x := by rw [mul_assoc]
          _ = 1 * x := by rw [ha_mul_self]
          _ = x := by simp
      have h_mem_product : (a, a * x) ∈ involutionSet G ×ˢ involutionSet G :=
        Finset.mem_product.mpr ⟨ha_mem, hax_mem⟩
      exact Finset.mem_filter.mpr ⟨h_mem_product, h_product⟩
    · -- left_inv: j(i(p)) = p
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hp_mem, hp_eq⟩
      rcases Finset.mem_product.mp hp_mem with ⟨ha_mem, hb_mem⟩
      have ha_order : orderOf p.1 = 2 := by
        simpa [involutionSet] using ha_mem
      have ha_inv : p.1⁻¹ = p.1 := (inv_eq_and_mul_self_eq_one ha_order).1
      have hp2_eq : p.2 = p.1 * x := by
        calc
          p.2 = 1 * p.2 := by simp
          _ = (p.1⁻¹ * p.1) * p.2 := by simp
          _ = p.1⁻¹ * (p.1 * p.2) := by rw [mul_assoc]
          _ = p.1⁻¹ * x := by rw [hp_eq]
          _ = p.1 * x := by rw [ha_inv]
      ext <;> simp [hp2_eq]
    · -- right_inv: i(j(a)) = a
      intro a ha
      rfl
  exact hst

/-- **Common inverters differ by a centralizing element.** If both `a` and `a₀`
invert `x`, then `a₀⁻¹ * a` centralizes `x`. -/
theorem inv_mul_mem_centralizer {x a a₀ : G} (ha : a * x * a⁻¹ = x⁻¹)
    (ha₀ : a₀ * x * a₀⁻¹ = x⁻¹) :
    a₀⁻¹ * a ∈ Subgroup.centralizer ({x} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc
    (a₀⁻¹ * a) * x = a₀⁻¹ * (a * x) := by group
    _ = a₀⁻¹ * ((a * x * a⁻¹) * a) := by group
    _ = a₀⁻¹ * (x⁻¹ * a) := by rw [ha]
    _ = (a₀⁻¹ * x⁻¹) * a := by group
    _ = (x * a₀⁻¹) * a := by
      have hxeq : a₀⁻¹ * x⁻¹ = x * a₀⁻¹ := by
        calc
          a₀⁻¹ * x⁻¹ = a₀⁻¹ * (a₀ * x * a₀⁻¹) := by rw [ha₀]
          _ = (a₀⁻¹ * a₀) * x * a₀⁻¹ := by group
          _ = 1 * x * a₀⁻¹ := by group
          _ = x * a₀⁻¹ := by simp
      rw [hxeq]
    _ = x * (a₀⁻¹ * a) := by group

/-- **The inverter map injects into the centralizer.** With `a₀` inverting `x`
and `S` a set of inverters of `x`, the map `a ↦ a₀⁻¹ * a` is injective on `S`
and lands in `C_G(x)`. -/
theorem inverter_map_injOn_centralizer {x a₀ : G} (S : Set G)
    (ha₀ : a₀ * x * a₀⁻¹ = x⁻¹) (hS : ∀ a ∈ S, a * x * a⁻¹ = x⁻¹) :
    Set.InjOn (fun a => a₀⁻¹ * a) S ∧
      ∀ a ∈ S, a₀⁻¹ * a ∈ Subgroup.centralizer ({x} : Set G) := by
  constructor
  · intro a haS b hbS h
    -- h : (fun a => a₀⁻¹ * a) a = (fun a => a₀⁻¹ * a) b, i.e. a₀⁻¹ * a = a₀⁻¹ * b
    exact mul_left_cancel h
  · intro a haS
    exact inv_mul_mem_centralizer (hS a haS) ha₀

/-- **Few factorizations of a fixed product.** For every `x`,
`r(x) ≤ |C_G(x)|`. -/
theorem involutionPairCount_le_centralizer [Fintype G] (x : G) :
    involutionPairCount G x ≤ Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  classical
  have h_eq : involutionPairCount G x = ((involutionSet G).filter (fun a => a * x ∈ involutionSet G)).card :=
    involutionPairCount_eq_filter x
  set S := (involutionSet G).filter (fun a => a * x ∈ involutionSet G) with hS_def
  by_cases hcard : S.card = 0
  · rw [h_eq, hcard]
    exact Nat.zero_le _
  · have hpos : 0 < S.card := Nat.pos_of_ne_zero hcard
    have hS_nonempty : S.Nonempty := (Finset.card_pos.mp hpos)
    rcases hS_nonempty with ⟨a₀, ha₀S⟩
    have ha₀_mem : a₀ ∈ involutionSet G := (Finset.mem_filter.mp ha₀S).1
    have ha₀x_mem : a₀ * x ∈ involutionSet G := (Finset.mem_filter.mp ha₀S).2
    have ha₀_inv : orderOf a₀ = 2 := by
      simpa [involutionSet] using ha₀_mem
    have ha₀x_inv : orderOf (a₀ * x) = 2 := by
      simpa [involutionSet] using ha₀x_mem
    have ha₀_sq : a₀ * a₀ = 1 := (inv_eq_and_mul_self_eq_one ha₀_inv).2
    have ha₀_mul_ax : a₀ * (a₀ * x) = x := by
      calc
        a₀ * (a₀ * x) = (a₀ * a₀) * x := by group
        _ = 1 * x := by rw [ha₀_sq]
        _ = x := by simp
    have ha₀_inverts : a₀ * x * a₀⁻¹ = x⁻¹ :=
      inverts_of_mul_eq ha₀_inv ha₀x_inv ha₀_mul_ax
    have hS_inverts : ∀ a ∈ S, a * x * a⁻¹ = x⁻¹ := by
      intro a ha
      rcases Finset.mem_filter.mp ha with ⟨ha_mem, hax_mem⟩
      have ha_inv : orderOf a = 2 := by
        simpa [involutionSet] using ha_mem
      have hax_inv : orderOf (a * x) = 2 := by
        simpa [involutionSet] using hax_mem
      have ha_sq : a * a = 1 := (inv_eq_and_mul_self_eq_one ha_inv).2
      have ha_mul_ax : a * (a * x) = x := by
        calc
          a * (a * x) = (a * a) * x := by group
          _ = 1 * x := by rw [ha_sq]
          _ = x := by simp
      exact inverts_of_mul_eq ha_inv hax_inv ha_mul_ax
    have hinj_centralizer := inverter_map_injOn_centralizer (S : Set G) ha₀_inverts hS_inverts
    rcases hinj_centralizer with ⟨hinj, hmem⟩
    set H := Subgroup.centralizer ({x} : Set G) with hH_def
    let f : S → H := fun a => ⟨a₀⁻¹ * a.1, hmem a.1 a.2⟩
    have hf_inj : Function.Injective f := by
      intro a b h
      apply Subtype.ext
      have hval : (f a).val = (f b).val := congrArg Subtype.val h
      have h_eq_ab : a₀⁻¹ * a.1 = a₀⁻¹ * b.1 := hval
      exact hinj a.2 b.2 h_eq_ab
    have h_card_S : Nat.card S = S.card := Nat.card_eq_finsetCard S
    have h_card_le : Nat.card S ≤ Nat.card H :=
      Nat.card_le_card_of_injective f hf_inj
    calc
      involutionPairCount G x = S.card := h_eq
      _ = Nat.card S := by symm; exact h_card_S
      _ ≤ Nat.card H := h_card_le
      _ = Nat.card (Subgroup.centralizer ({x} : Set G)) := rfl

open scoped Classical in
/-- **Averaging over the non-identity elements.** For a nontrivial group there
is some `x ≠ 1` with `(n - 1) * r(x) ≥ ∑_{x ≠ 1} r(x)`. -/
theorem exists_averaging [Fintype G] (hG : Nontrivial G) :
    ∃ x : G, x ≠ 1 ∧
      ∑ y ∈ Finset.univ.erase (1 : G), involutionPairCount G y ≤
        (Nat.card G - 1) * involutionPairCount G x := by
  -- The set of non-identity elements is nonempty because G is nontrivial
  have h_nonempty : (Finset.univ.erase (1 : G)).Nonempty := by
    rcases hG.exists_pair_ne with ⟨x, y, hxy⟩
    by_cases hx1 : x = 1
    · have hy1 : y ≠ 1 := by
        intro hy1
        apply hxy
        rw [hx1, hy1]
      refine ⟨y, Finset.mem_erase.mpr ⟨hy1, Finset.mem_univ y⟩⟩
    · refine ⟨x, Finset.mem_erase.mpr ⟨hx1, Finset.mem_univ x⟩⟩
  -- Apply Finset.exists_max_image to find x where r(y) is maximized
  have h_max := Finset.exists_max_image (Finset.univ.erase (1 : G)) (involutionPairCount G) h_nonempty
  rcases h_max with ⟨x, hx_mem, hx_max⟩
  have hx_ne_one : x ≠ 1 := (Finset.mem_erase.mp hx_mem).1
  -- Bound the sum: each term is ≤ r(x), so sum ≤ |erase 1| * r(x)
  have h_sum_le : ∑ y ∈ Finset.univ.erase (1 : G), involutionPairCount G y ≤
      (Finset.univ.erase (1 : G)).card * involutionPairCount G x :=
    Finset.sum_le_card_nsmul (Finset.univ.erase (1 : G)) (involutionPairCount G) (involutionPairCount G x) hx_max
  -- The cardinality of (univ.erase 1) equals Nat.card G - 1
  have h_card_erase : (Finset.univ.erase (1 : G)).card = Nat.card G - 1 := by
    have h_card_univ : (Finset.univ : Finset G).card = Nat.card G := by simp
    have h_one_mem : (1 : G) ∈ Finset.univ := Finset.mem_univ _
    have h_card_erase' : (Finset.univ.erase (1 : G)).card = (Finset.univ : Finset G).card - 1 :=
      Finset.card_erase_of_mem h_one_mem
    rw [h_card_erase', h_card_univ]
  -- Combine
  rw [h_card_erase] at h_sum_le
  exact ⟨x, hx_ne_one, h_sum_le⟩

/-- **Some element has a large centralizer.** There is `x ≠ 1` with
`(n - 1) * |C_G(x)| ≥ k² - k`. -/
theorem exists_big_centralizer [IsSimpleGroup G] [Fintype G] :
    ∃ x : G, x ≠ 1 ∧
      numInvolutions G ^ 2 - numInvolutions G ≤
        (Nat.card G - 1) * Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  classical
  have hG_nontriv : Nontrivial G := inferInstance
  rcases exists_averaging hG_nontriv with ⟨x, hx_ne_one, h_avg⟩
  have h_sum := sum_involutionPairCount_erase_one (G := G)
  have h_rx_centralizer : involutionPairCount G x ≤
    Nat.card (Subgroup.centralizer ({x} : Set G)) :=
    involutionPairCount_le_centralizer x
  refine ⟨x, hx_ne_one, ?_⟩
  calc
    numInvolutions G ^ 2 - numInvolutions G =
      ∑ y ∈ Finset.univ.erase (1 : G), involutionPairCount G y := by
      rw [h_sum]
    _ ≤ (Nat.card G - 1) * involutionPairCount G x := h_avg
    _ ≤ (Nat.card G - 1) * Nat.card (Subgroup.centralizer ({x} : Set G)) :=
      Nat.mul_le_mul_left (Nat.card G - 1) h_rx_centralizer

/-! ## The bound -/

/-- **Arithmetic of the index bound.** A purely arithmetic inequality packaging
the final counting estimate: it yields `m ≤ 2 c²`. -/
theorem index_arith {n k c d m : ℕ} (hn : 2 ≤ n) (hk : 2 ≤ k) (hd : 1 ≤ d)
    (hnkc : n ≤ k * c) (hk2 : k ^ 2 ≤ (n - 1) * d + k) (hmd : m * d = n) :
    m ≤ 2 * c ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hn1' : 1 ≤ n - 1 := by omega
  -- Work in ℤ to avoid truncated subtraction
  have hzn : (2 : ℤ) ≤ n := by exact_mod_cast hn
  have hzk : (2 : ℤ) ≤ k := by exact_mod_cast hk
  have hzd : (1 : ℤ) ≤ d := by exact_mod_cast hd
  have hznkc : (n : ℤ) ≤ (k : ℤ) * (c : ℤ) := by exact_mod_cast hnkc
  have hzk2 : (k : ℤ) ^ 2 ≤ ((n : ℤ) - 1) * (d : ℤ) + (k : ℤ) := by
    simpa [Nat.cast_sub hn1, Nat.cast_add, Nat.cast_mul, Nat.cast_pow] using
      show ((k^2 : ℕ) : ℤ) ≤ (((n-1) * d + k : ℕ) : ℤ) from by exact_mod_cast hk2
  have hzmd : (m : ℤ) * (d : ℤ) = (n : ℤ) := by exact_mod_cast hmd
  -- Chain: 2*c^2*(n-1)*d ≥ 2*c^2*k*(k-1) ≥ c^2*k^2 ≥ n^2 ≥ n*(n-1)
  have hineq1 : ((n : ℤ) - 1) * (d : ℤ) ≥ (k : ℤ) * ((k : ℤ) - 1) := by
    nlinarith
  have hineq2 : 2 * (k : ℤ) * ((k : ℤ) - 1) ≥ (k : ℤ) ^ 2 := by
    nlinarith
  have hineq3 : (n : ℤ) ^ 2 ≤ (k : ℤ) ^ 2 * (c : ℤ) ^ 2 := by
    nlinarith
  have hineq4 : (n : ℤ) ^ 2 ≥ (n : ℤ) * ((n : ℤ) - 1) := by
    nlinarith
  have hchain : 2 * (c : ℤ) ^ 2 * ((n : ℤ) - 1) * (d : ℤ) ≥ (n : ℤ) * ((n : ℤ) - 1) := by
    nlinarith
  have hn1_pos : (0 : ℤ) < (n : ℤ) - 1 := by
    nlinarith
  have hcancel1 : 2 * (c : ℤ) ^ 2 * (d : ℤ) ≥ (n : ℤ) := by
    nlinarith
  have hd_pos : (0 : ℤ) < d := by
    nlinarith
  have hcancel2 : (m : ℤ) ≤ 2 * (c : ℤ) ^ 2 := by
    nlinarith
  exact_mod_cast hcancel2

/-- **Explicit order bound.** For a finite nonabelian simple group `G` and an
involution `t`, `|G| ≤ (2 c²)!` where `c = |C_G(t)|`. -/
theorem order_bound [IsSimpleGroup G] [Fintype G] (h : ∃ a b : G, a * b ≠ b * a)
    {t : G} (ht : orderOf t = 2) :
    Nat.card G ≤
      Nat.factorial (2 * Nat.card (Subgroup.centralizer ({t} : Set G)) ^ 2) := by
  let n := Nat.card G
  let k := numInvolutions G
  let c := Nat.card (Subgroup.centralizer ({t} : Set G))
  have hn2 : 2 ≤ n := by
    have hpos : 0 < n := by
      have : 0 < Fintype.card G := Fintype.card_pos
      simpa [n, Nat.card_eq_fintype_card] using this
    by_contra! h_not
    have hcard1 : n = 1 := by omega
    have hcard_fintype : Fintype.card G = 1 := by
      simpa [n, Nat.card_eq_fintype_card] using hcard1
    rcases (Fintype.card_eq_one_iff.mp hcard_fintype) with ⟨x, hx⟩
    rcases h with ⟨a, b, hneq⟩
    have ha_eq_x : a = x := hx a
    have hb_eq_x : b = x := hx b
    exact hneq (by rw [ha_eq_x, hb_eq_x])
  have hk2 : 2 ≤ k := two_le_numInvolutions h ht
  have hnkc : n ≤ k * c :=
    card_le_numInvolutions_mul_centralizer ht
  rcases exists_big_centralizer (G := G) with ⟨x, hx, h_big⟩
  let H := Subgroup.centralizer ({x} : Set G)
  let d := Nat.card H
  have hd1 : 1 ≤ d := by
    have hpos : 0 < d := by
      have h_fintype_H : Fintype H := Fintype.ofFinite H
      have hcard_pos : 0 < Fintype.card H := Fintype.card_pos (α := H)
      simpa [d, Nat.card_eq_fintype_card] using hcard_pos
    omega
  have hk2_ineq : k ^ 2 ≤ (n - 1) * d + k := by
    have htemp : k ^ 2 - k ≤ (n - 1) * d := h_big
    omega
  have hH_lt_top : H < ⊤ :=
    (centralizer_lt_top_of_ne_one h hx).1
  let m := H.index
  have hm_d_n : m * d = n := by
    calc
      m * d = H.index * Nat.card H := rfl
      _ = Nat.card G := Subgroup.index_mul_card H
      _ = n := rfl
  have hm_le_2c2 : m ≤ 2 * c ^ 2 :=
    index_arith hn2 hk2 hd1 hnkc hk2_ineq hm_d_n
  have hn_le_mfact : n ≤ Nat.factorial m :=
    card_le_index_factorial hH_lt_top
  have hmfact_le_goal : Nat.factorial m ≤ Nat.factorial (2 * c ^ 2) :=
    Nat.factorial_le hm_le_2c2
  calc
    n ≤ Nat.factorial m := hn_le_mfact
    _ ≤ Nat.factorial (2 * c ^ 2) := hmfact_le_goal



end GroupTheory
end LeanEval
