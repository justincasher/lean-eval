import LeanEval.GroupTheory.BooneHigmanSimple.Computability

/-!
# Kuznetsov / Boone–Higman: normal-closure membership via certificates

The group-theoretic half of the argument.  Membership of a free-group word in
the normal closure of a finite list of relators is exactly the existence of a
*certificate* (Lemma `mem_normalClosure_cert`), and the simplicity lemmas needed
for the negative side.
-/

namespace LeanEval.GroupTheory.BooneHigmanSimpleProblem

variable {n : ℕ}

/-- The set of relator elements `{FreeGroup.mk r | r ∈ R}` spelled by a relator
list `R`. -/
def relatorSet (R : List (Word n)) : Set (FreeGroup (Fin n)) :=
  {x | ∃ r ∈ R, FreeGroup.mk r = x}

/-- **Relator set of an extended list.** Appending a word `w` to the relator list
adjoins `FreeGroup.mk w` to the relator set. -/
lemma relatorSet_append (R : List (Word n)) (w : Word n) :
    relatorSet (R ++ [w]) = relatorSet R ∪ {FreeGroup.mk w} := by
  sorry

/-- **A generator as a one-letter word.** -/
lemma of_eq_mk_singleton (i : Fin n) :
    FreeGroup.of i = FreeGroup.mk [(i, true)] := by
  sorry

variable {G : Type*} [Group G]

/-- `y` is a single signed conjugate `g · s^{±1} · g⁻¹` of an element `s ∈ S`. -/
def IsSignedConjugate (S : Set G) (y : G) : Prop :=
  ∃ g s, s ∈ S ∧ (y = g * s * g⁻¹ ∨ y = g * s⁻¹ * g⁻¹)

/-- **Products of signed conjugates form a subgroup.** `prodConjugatesSubgroup S`
is the subgroup of finite products of terms `g · s^{±1} · g⁻¹` with `s ∈ S`. -/
def prodConjugatesSubgroup (S : Set G) : Subgroup G where
  carrier := {x | ∃ l : List G, (∀ y ∈ l, IsSignedConjugate S y) ∧ x = l.prod}
  mul_mem' := by
    intro x y hx hy
    rcases hx with ⟨lx, hlxa, hx⟩
    rcases hy with ⟨ly, hlya, hy⟩
    refine ⟨lx ++ ly, ?_, ?_⟩
    · intro z hz
      rcases List.mem_append.mp hz with (hz | hz)
      · exact hlxa z hz
      · exact hlya z hz
    · simp [hx, hy]
  one_mem' := by
    refine ⟨[], ?_, ?_⟩
    · intro y hy
      exfalso; exact (List.not_mem_nil (a := y)) hy
    · simp
  inv_mem' := by
    intro x hx
    rcases hx with ⟨l, hl, hx⟩
    have h_inv_closure : ∀ a : G, IsSignedConjugate S a → IsSignedConjugate S a⁻¹ := by
      intro a ha
      rcases ha with ⟨g, s, hs, ha | ha⟩
      · refine ⟨g, s, hs, ?_⟩
        right
        calc
          a⁻¹ = (g * s * g⁻¹)⁻¹ := by rw [ha]
          _ = g * s⁻¹ * g⁻¹ := by simp [mul_inv_rev, mul_assoc, inv_inv]
      · refine ⟨g, s, hs, ?_⟩
        left
        calc
          a⁻¹ = (g * s⁻¹ * g⁻¹)⁻¹ := by rw [ha]
          _ = g * s * g⁻¹ := by simp [mul_inv_rev, mul_assoc, inv_inv]
    refine ⟨(l.map (·⁻¹)).reverse, ?_, ?_⟩
    · intro z hz
      have hz_mem : z ∈ (l.map (·⁻¹)).reverse := hz
      rw [List.mem_reverse] at hz_mem
      rcases List.mem_map.mp hz_mem with ⟨y, hy, rfl⟩
      exact h_inv_closure y (hl y hy)
    · calc
      x⁻¹ = (l.prod)⁻¹ := by rw [hx]
      _ = ((l.map (·⁻¹)).reverse).prod := by rw [List.prod_inv_reverse]

/-- **Conjugates lie in the subgroup of products.** -/
lemma conjugates_subset_prod (S : Set G) :
    Group.conjugatesOfSet S ⊆ (prodConjugatesSubgroup S : Set G) := by
  intro x hx
  rcases Group.mem_conjugatesOfSet_iff.mp hx with ⟨a, ha, hconj⟩
  rcases isConj_iff.mp hconj with ⟨g, h_eq⟩
  have hx_signed : IsSignedConjugate S x := by
    refine ⟨g, a, ha, ?_⟩
    left
    rw [h_eq]
  refine ⟨[x], ?_, by simp⟩
  intro y hy
  simp at hy
  rcases hy with (rfl | hy)
  exact hx_signed

/-- **Closure elements are products of signed conjugates.** -/
lemma closure_prod_conjugates (S : Set G) :
    Subgroup.normalClosure S ≤ prodConjugatesSubgroup S := by
  have h : Group.conjugatesOfSet S ⊆ (prodConjugatesSubgroup S : Set G) :=
    conjugates_subset_prod S
  have h' : Subgroup.closure (Group.conjugatesOfSet S) ≤ prodConjugatesSubgroup S :=
    Subgroup.closure_le (k := Group.conjugatesOfSet S) (K := prodConjugatesSubgroup S) |>.mpr h
  calc
    Subgroup.normalClosure S = Subgroup.closure (Group.conjugatesOfSet S) := rfl
    _ ≤ prodConjugatesSubgroup S := h'

/-- **A single conjugacy term under `mk`.** -/
lemma mk_conjTerm (R : List (Word n)) (t : Word n × Bool × ℕ) :
    FreeGroup.mk (conjTerm R t) =
      FreeGroup.mk t.1 *
        (FreeGroup.mk (R.getD t.2.2 [])) ^ (if t.2.1 then (1 : ℤ) else -1) *
        (FreeGroup.mk t.1)⁻¹ := by
  unfold conjTerm signedRelator
  split
  · case isTrue h =>
    simp [h]
  · case isFalse h =>
    simp [h]

/-- **The value word spells a product of conjugates.** -/
lemma mk_eval_eq_prod (R : List (Word n)) (c : Certificate n) :
    FreeGroup.mk (evalCert R c) =
      (c.map fun t =>
        FreeGroup.mk t.1 *
          (FreeGroup.mk (R.getD t.2.2 [])) ^ (if t.2.1 then (1 : ℤ) else -1) *
          (FreeGroup.mk t.1)⁻¹).prod := by
  unfold evalCert
  have h_flatten : ∀ (l : List (Word n)), FreeGroup.mk (l.flatten) = (l.map FreeGroup.mk).prod := by
    intro l
    induction' l with hd tl ih
    · simp [FreeGroup.one_eq_mk]
    · calc
      FreeGroup.mk ((hd :: tl).flatten) = FreeGroup.mk (hd ++ tl.flatten) := rfl
      _ = FreeGroup.mk hd * FreeGroup.mk (tl.flatten) := by rw [FreeGroup.mul_mk]
      _ = FreeGroup.mk hd * (tl.map FreeGroup.mk).prod := by rw [ih]
      _ = ((hd :: tl).map FreeGroup.mk).prod := rfl
  rw [h_flatten, List.map_map]
  have h_map : (c.map (FreeGroup.mk ∘ conjTerm R)) =
      (c.map fun t => (FreeGroup.mk t.1 *
        (FreeGroup.mk (R.getD t.2.2 [])) ^ (if t.2.1 then (1 : ℤ) else -1) *
        (FreeGroup.mk t.1)⁻¹)) := by
    refine List.map_congr_left ?_
    intro t ht
    calc
      (FreeGroup.mk ∘ conjTerm R) t = FreeGroup.mk (conjTerm R t) := rfl
      _ = FreeGroup.mk t.1 *
          (FreeGroup.mk (R.getD t.2.2 [])) ^ (if t.2.1 then (1 : ℤ) else -1) *
          (FreeGroup.mk t.1)⁻¹ := by rw [mk_conjTerm R t]
  rw [h_map]

/-- **Relator elements are indexed.** Every element of `relatorSet R` is
`FreeGroup.mk` of some `R_k`. -/
lemma relator_index (R : List (Word n)) {s : FreeGroup (Fin n)}
    (hs : s ∈ relatorSet R) :
    ∃ k, FreeGroup.mk (R.getD k []) = s := by
  dsimp [relatorSet] at hs
  rcases hs with ⟨r, hr, h⟩
  rcases (List.mem_iff_getElem.mp hr) with ⟨k, hk, hmem⟩
  have hget : R.getD k [] = r := by
    calc
      R.getD k [] = R.get ⟨k, hk⟩ := by
        simpa using List.getD_eq_get (i := ⟨k, hk⟩) (d := [])
      _ = R[k]'hk := by simp
      _ = r := hmem
  refine ⟨k, ?_⟩
  rw [hget]
  exact h

/-- **Certificate from a product of conjugates.** If `FreeGroup.mk w` is a finite
product of signed conjugates of relator elements, a certificate spells it. -/
lemma cert_of_prod (R : List (Word n)) (w : Word n)
    (hw : FreeGroup.mk w ∈ prodConjugatesSubgroup (relatorSet R)) :
    ∃ c : Certificate n, FreeGroup.mk (evalCert R c) = FreeGroup.mk w := by
  rcases hw with ⟨l, hl, hprod⟩
  have hforall : ∀ y ∈ l, ∃ (g' : Word n) (ε : Bool) (k : ℕ),
    FreeGroup.mk g' * (FreeGroup.mk (R.getD k [])) ^ (if ε then (1 : ℤ) else -1) * (FreeGroup.mk g')⁻¹ = y := by
    intro y hy
    have hys := hl y hy
    rcases hys with ⟨g, s, hs, (h | h)⟩
    · rcases relator_index R hs with ⟨k, hk⟩
      refine ⟨g.toWord, true, k, ?_⟩
      calc
        FreeGroup.mk g.toWord * (FreeGroup.mk (R.getD k [])) ^ (if true then (1 : ℤ) else -1) * (FreeGroup.mk g.toWord)⁻¹
            = g * (FreeGroup.mk (R.getD k [])) ^ (1 : ℤ) * g⁻¹ := by simp [FreeGroup.mk_toWord]
        _ = g * FreeGroup.mk (R.getD k []) * g⁻¹ := by simp
        _ = g * s * g⁻¹ := by rw [hk]
        _ = y := h.symm
    · rcases relator_index R hs with ⟨k, hk⟩
      refine ⟨g.toWord, false, k, ?_⟩
      calc
        FreeGroup.mk g.toWord * (FreeGroup.mk (R.getD k [])) ^ (if false then (1 : ℤ) else -1) * (FreeGroup.mk g.toWord)⁻¹
            = g * (FreeGroup.mk (R.getD k [])) ^ (-1 : ℤ) * g⁻¹ := by simp [FreeGroup.mk_toWord]
        _ = g * ((FreeGroup.mk (R.getD k []))⁻¹) * g⁻¹ := by simp
        _ = g * s⁻¹ * g⁻¹ := by rw [hk]
        _ = y := h.symm
  choose g' ε k h_eq using hforall
  let c : Certificate n := l.attach.map fun ⟨y, hy⟩ => (g' y hy, ε y hy, k y hy)
  have hc_prod : (c.map fun t : Word n × Bool × ℕ =>
    FreeGroup.mk t.1 * (FreeGroup.mk (R.getD t.2.2 [])) ^ (if t.2.1 then (1 : ℤ) else -1) * (FreeGroup.mk t.1)⁻¹).prod = l.prod := by
    dsimp [c]
    calc
      ((l.attach.map fun ⟨y, hy⟩ => (g' y hy, ε y hy, k y hy)).map fun t : Word n × Bool × ℕ =>
        FreeGroup.mk t.1 * (FreeGroup.mk (R.getD t.2.2 [])) ^ (if t.2.1 then (1 : ℤ) else -1) * (FreeGroup.mk t.1)⁻¹).prod
          = (l.attach.map (fun (x : {x // x ∈ l}) =>
              FreeGroup.mk (g' x.val x.property) * (FreeGroup.mk (R.getD (k x.val x.property) [])) ^
                (if ε x.val x.property then (1 : ℤ) else -1) * (FreeGroup.mk (g' x.val x.property))⁻¹)).prod := by
        rw [List.map_map]; apply congrArg List.prod; ext x; dsimp; rfl
        
      _ = (l.attach.map (fun (x : {x // x ∈ l}) => x.val)).prod := by
        refine congrArg List.prod (List.map_congr_left fun x hx => ?_)
        rcases x with ⟨y, hy⟩
        exact h_eq y hy
      _ = l.prod := by simp
  refine ⟨c, ?_⟩
  rw [mk_eval_eq_prod]
  calc
    (c.map fun t : Word n × Bool × ℕ =>
      FreeGroup.mk t.1 * (FreeGroup.mk (R.getD t.2.2 [])) ^ (if t.2.1 then (1 : ℤ) else -1) * (FreeGroup.mk t.1)⁻¹).prod
        = l.prod := hc_prod
    _ = FreeGroup.mk w := hprod.symm

/-- **A certificate witnesses normal-closure membership.** -/
lemma mem_of_cert (R : List (Word n)) (w : Word n) {c : Certificate n}
    (hc : FreeGroup.mk (evalCert R c) = FreeGroup.mk w) :
    FreeGroup.mk w ∈ Subgroup.normalClosure (relatorSet R) := by
  -- rewrite the goal using hc: we show mk(evalCert) ∈ normalClosure instead
  rw [← hc]
  -- express mk(evalCert) as a product of signed conjugates
  rw [mk_eval_eq_prod R c]
  -- the normal closure is a subgroup, so list_prod_mem applies
  apply Subgroup.list_prod_mem
  intro x hx
  -- each factor comes from a certificate entry t
  rcases List.mem_map.mp hx with ⟨t, ht, rfl⟩
  -- x = (FreeGroup.mk t.1 * (FreeGroup.mk (R.getD t.2.2 [])) ^ (if t.2.1 then (1 : ℤ) else -1)) * (FreeGroup.mk t.1)⁻¹
  set g := FreeGroup.mk t.1 with hg
  set r := FreeGroup.mk (R.getD t.2.2 []) with hr
  set ε := t.2.1 with hε
  have hN : (Subgroup.normalClosure (relatorSet R)).Normal := inferInstance
  have h_mem_r : r ∈ Subgroup.normalClosure (relatorSet R) := by
    by_cases hpos : t.2.2 < R.length
    · have hr_mem_RS : r ∈ relatorSet R := by
        dsimp [r, relatorSet]
        refine ⟨R.get ⟨t.2.2, hpos⟩, ?_, ?_⟩
        · exact List.get_mem R ⟨t.2.2, hpos⟩
        · simpa using (congrArg FreeGroup.mk (List.getD_eq_get R [] ⟨t.2.2, hpos⟩)).symm
      exact Subgroup.subset_normalClosure hr_mem_RS
    · have hout : R.length ≤ t.2.2 := Nat.not_lt.mp hpos
      have h_default : R.getD t.2.2 [] = [] :=
        List.getD_eq_default R [] hout
      have h_r_one : r = 1 := by
        dsimp [r]
        rw [h_default, FreeGroup.one_eq_mk]
      rw [h_r_one]
      exact Subgroup.one_mem _
  have h_mem_r_pow : r ^ (if ε then (1 : ℤ) else -1) ∈ Subgroup.normalClosure (relatorSet R) :=
    Subgroup.zpow_mem (Subgroup.normalClosure (relatorSet R)) h_mem_r (if ε then (1 : ℤ) else -1)
  have h_mem_conj : g * (r ^ (if ε then (1 : ℤ) else -1)) * g⁻¹ ∈ Subgroup.normalClosure (relatorSet R) :=
    hN.conj_mem _ h_mem_r_pow g
  -- the factor is exactly this conjugate
  have h_factor : (g * (FreeGroup.mk (R.getD t.2.2 [])) ^ (if t.2.1 then (1 : ℤ) else -1)) * (FreeGroup.mk t.1)⁻¹ =
      g * (r ^ (if ε then (1 : ℤ) else -1)) * g⁻¹ := by
    simp [hε, hg, hr]
  rw [h_factor]
  exact h_mem_conj

/-- **Membership in a normal closure via certificates.** -/
lemma mem_normalClosure_cert (R : List (Word n)) (w : Word n) :
    FreeGroup.mk w ∈ Subgroup.normalClosure (relatorSet R) ↔
      ∃ c : Certificate n, FreeGroup.mk (evalCert R c) = FreeGroup.mk w := by
  constructor
  · intro h
    have h' : FreeGroup.mk w ∈ prodConjugatesSubgroup (relatorSet R) :=
      closure_prod_conjugates (relatorSet R) h
    exact cert_of_prod R w h'
  · intro h
    rcases h with ⟨c, hc⟩
    exact mem_of_cert R w hc

/-- **A finite set of free-group elements is spelled by a word list.** -/
lemma finset_to_word_list {T : Set (FreeGroup (Fin n))} (hT : T.Finite) :
    ∃ R : List (Word n), relatorSet R = T := by
  let R : List (Word n) := (hT.toFinset).toList.map (fun t : FreeGroup (Fin n) => t.toWord)
  refine ⟨R, ?_⟩
  ext x
  constructor
  · intro hx
    rcases hx with ⟨r, hr, hx⟩
    rcases List.mem_map.mp hr with ⟨t, ht, hr⟩
    have htF : t ∈ hT.toFinset := Finset.mem_toList.mp ht
    have htT : t ∈ T := (hT.mem_toFinset).mp htF
    have hx_t : x = t := by
      calc
        x = FreeGroup.mk r := Eq.symm hx
        _ = FreeGroup.mk (t.toWord) := by rw [hr]
        _ = t := FreeGroup.mk_toWord
    rwa [hx_t]
  · intro hx
    have hxF : x ∈ hT.toFinset := (hT.mem_toFinset).mpr hx
    have hxL : x.toWord ∈ R := by
      apply List.mem_map.mpr
      refine ⟨x, Finset.mem_toList.mpr hxF, rfl⟩
    refine ⟨x.toWord, hxL, FreeGroup.mk_toWord⟩

/-- **Normal closure of a nontrivial element in a simple group is everything.** -/
lemma normalClosure_singleton_top [IsSimpleGroup G] {g : G} (hg : g ≠ 1) :
    Subgroup.normalClosure ({g} : Set G) = ⊤ := by
  have hN_normal : (Subgroup.normalClosure ({g} : Set G)).Normal := by
    infer_instance
  rcases hN_normal.eq_bot_or_eq_top with (h | h)
  · exfalso
    have hsubset : ({g} : Set G) ⊆ (⊥ : Subgroup G) :=
      ((Subgroup.normalClosure_subset_iff (s := ({g} : Set G)) (N := ⊥)).mpr h.le)
    have hg1 : g ∈ (⊥ : Subgroup G) := by
      apply hsubset
      simp
    have hg1_eq : g = 1 := (Subgroup.mem_bot.mp hg1)
    exact hg hg1_eq
  · exact h

/-- **A subgroup is everything iff it contains all generators.** -/
lemma top_iff_generators (N : Subgroup (FreeGroup (Fin n))) :
    N = ⊤ ↔ ∀ i : Fin n, FreeGroup.of i ∈ N := by
  constructor
  · intro hN i
    rw [hN]
    exact Subgroup.mem_top _
  · intro hN
    have h_gen : Set.range (FreeGroup.of : Fin n → FreeGroup (Fin n)) ⊆ N := by
      rintro _ ⟨i, rfl⟩
      exact hN i
    have h_closure : Subgroup.closure (Set.range (FreeGroup.of : Fin n → FreeGroup (Fin n))) ≤ N :=
      ((Subgroup.closure_le N).mpr h_gen)
    have h_top : Subgroup.closure (Set.range (FreeGroup.of : Fin n → FreeGroup (Fin n))) = ⊤ :=
      FreeGroup.closure_range_of (Fin n)
    rw [h_top] at h_closure
    exact le_antisymm (le_top (a := N)) h_closure

/-- **Surjective image criterion for being everything.** -/
lemma top_iff_map_top {H : Type*} [Group H] (φ : G →* H)
    (hφ : Function.Surjective φ) {N : Subgroup G} (hN : MonoidHom.ker φ ≤ N) :
    N = ⊤ ↔ Subgroup.map φ N = ⊤ := by
  constructor
  · intro hn
    rw [hn]
    exact Subgroup.map_top_of_surjective φ hφ
  · intro hmap
    have h := Subgroup.comap_map_eq_self hN
    rw [hmap, Subgroup.comap_top] at h
    exact h.symm

/-- **Image of the extended normal closure.** -/
lemma map_normalClosure_insert {H : Type*} [Group H] (φ : G →* H)
    (hφ : Function.Surjective φ) {S : Set G}
    (hS : Subgroup.normalClosure S = MonoidHom.ker φ) (x : G) :
    Subgroup.map φ (Subgroup.normalClosure (S ∪ {x})) =
      Subgroup.normalClosure {φ x} := by
  -- Every s ∈ S lies in ker φ, so φ(s) = 1.
  have h_phi_S_sub_one : φ '' S ⊆ ({1} : Set H) := by
    rintro y ⟨s, hs, rfl⟩
    have hs_ker : s ∈ MonoidHom.ker φ := by
      rw [← hS]
      exact Subgroup.subset_normalClosure hs
    simpa using hs_ker
  calc
    Subgroup.map φ (Subgroup.normalClosure (S ∪ {x}))
        = Subgroup.normalClosure (φ '' (S ∪ {x})) := by
      rw [Subgroup.map_normalClosure (S ∪ {x}) φ hφ]
    _ = Subgroup.normalClosure ((φ '' S) ∪ {φ x}) := by
      rw [Set.image_union, Set.image_singleton]
    _ = Subgroup.normalClosure {φ x} := by
      apply le_antisymm
      · apply Subgroup.normalClosure_le_normal
        intro y hy
        rcases hy with (hy | hy)
        · -- y ∈ φ '' S, hence y = 1
          have hy_one : y = (1 : H) := by
            simpa using h_phi_S_sub_one hy
          rw [hy_one]
          exact Subgroup.one_mem _
        · -- y = φ x
          rw [Set.mem_singleton_iff.mp hy]
          exact Subgroup.subset_normalClosure (by simp)
      · apply Subgroup.normalClosure_mono
        exact Set.subset_union_right (s := φ '' S) (t := {φ x})

end LeanEval.GroupTheory.BooneHigmanSimpleProblem
