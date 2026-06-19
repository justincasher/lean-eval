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

variable {G : Type*} [Group G]

/-- `y` is a single signed conjugate `g · s^{±1} · g⁻¹` of an element `s ∈ S`. -/
def IsSignedConjugate (S : Set G) (y : G) : Prop :=
  ∃ g s, s ∈ S ∧ (y = g * s * g⁻¹ ∨ y = g * s⁻¹ * g⁻¹)

/-- **Products of signed conjugates form a subgroup.** `prodConjugatesSubgroup S`
is the subgroup of finite products of terms `g · s^{±1} · g⁻¹` with `s ∈ S`. -/
def prodConjugatesSubgroup (S : Set G) : Subgroup G where
  carrier := {x | ∃ l : List G, (∀ y ∈ l, IsSignedConjugate S y) ∧ x = l.prod}
  mul_mem' := by sorry
  one_mem' := by sorry
  inv_mem' := by sorry

/-- **Conjugates lie in the subgroup of products.** -/
lemma conjugates_subset_prod (S : Set G) :
    Group.conjugatesOfSet S ⊆ (prodConjugatesSubgroup S : Set G) := by
  sorry

/-- **Closure elements are products of signed conjugates.** -/
lemma closure_prod_conjugates (S : Set G) :
    Subgroup.normalClosure S ≤ prodConjugatesSubgroup S := by
  sorry

/-- **A single conjugacy term under `mk`.** -/
lemma mk_conjTerm (R : List (Word n)) (t : Word n × Bool × ℕ) :
    FreeGroup.mk (conjTerm R t) =
      FreeGroup.mk t.1 *
        (FreeGroup.mk (R.getD t.2.2 [])) ^ (if t.2.1 then (1 : ℤ) else -1) *
        (FreeGroup.mk t.1)⁻¹ := by
  sorry

/-- **The value word spells a product of conjugates.** -/
lemma mk_eval_eq_prod (R : List (Word n)) (c : Certificate n) :
    FreeGroup.mk (evalCert R c) =
      (c.map fun t =>
        FreeGroup.mk t.1 *
          (FreeGroup.mk (R.getD t.2.2 [])) ^ (if t.2.1 then (1 : ℤ) else -1) *
          (FreeGroup.mk t.1)⁻¹).prod := by
  sorry

/-- **Relator elements are indexed.** Every element of `relatorSet R` is
`FreeGroup.mk` of some `R_k`. -/
lemma relator_index (R : List (Word n)) {s : FreeGroup (Fin n)}
    (hs : s ∈ relatorSet R) :
    ∃ k, FreeGroup.mk (R.getD k []) = s := by
  sorry

/-- **Certificate from a product of conjugates.** If `FreeGroup.mk w` is a finite
product of signed conjugates of relator elements, a certificate spells it. -/
lemma cert_of_prod (R : List (Word n)) (w : Word n)
    (hw : FreeGroup.mk w ∈ prodConjugatesSubgroup (relatorSet R)) :
    ∃ c : Certificate n, FreeGroup.mk (evalCert R c) = FreeGroup.mk w := by
  sorry

/-- **A certificate witnesses normal-closure membership.** -/
lemma mem_of_cert (R : List (Word n)) (w : Word n) {c : Certificate n}
    (hc : FreeGroup.mk (evalCert R c) = FreeGroup.mk w) :
    FreeGroup.mk w ∈ Subgroup.normalClosure (relatorSet R) := by
  sorry

/-- **Membership in a normal closure via certificates.** -/
lemma mem_normalClosure_cert (R : List (Word n)) (w : Word n) :
    FreeGroup.mk w ∈ Subgroup.normalClosure (relatorSet R) ↔
      ∃ c : Certificate n, FreeGroup.mk (evalCert R c) = FreeGroup.mk w := by
  sorry

/-- **A finite set of free-group elements is spelled by a word list.** -/
lemma finset_to_word_list {T : Set (FreeGroup (Fin n))} (hT : T.Finite) :
    ∃ R : List (Word n), relatorSet R = T := by
  sorry

/-- **Normal closure of a nontrivial element in a simple group is everything.** -/
lemma normalClosure_singleton_top [IsSimpleGroup G] {g : G} (hg : g ≠ 1) :
    Subgroup.normalClosure ({g} : Set G) = ⊤ := by
  sorry

/-- **A subgroup is everything iff it contains all generators.** -/
lemma top_iff_generators (N : Subgroup (FreeGroup (Fin n))) :
    N = ⊤ ↔ ∀ i : Fin n, FreeGroup.of i ∈ N := by
  sorry

/-- **Surjective image criterion for being everything.** -/
lemma top_iff_map_top {H : Type*} [Group H] (φ : G →* H)
    (hφ : Function.Surjective φ) {N : Subgroup G} (hN : MonoidHom.ker φ ≤ N) :
    N = ⊤ ↔ Subgroup.map φ N = ⊤ := by
  sorry

/-- **Image of the extended normal closure.** -/
lemma map_normalClosure_insert {H : Type*} [Group H] (φ : G →* H)
    (hφ : Function.Surjective φ) {S : Set G}
    (hS : Subgroup.normalClosure S = MonoidHom.ker φ) (x : G) :
    Subgroup.map φ (Subgroup.normalClosure (S ∪ {x})) =
      Subgroup.normalClosure {φ x} := by
  sorry

end LeanEval.GroupTheory.BooneHigmanSimpleProblem
