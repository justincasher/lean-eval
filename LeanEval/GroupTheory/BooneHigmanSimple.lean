import LeanEval.GroupTheory.BooneHigmanSimple.NormalClosure
import EvalTools.Markers

namespace LeanEval
namespace GroupTheory
namespace BooneHigmanSimpleProblem

/-!
# Kuznetsov / Boone–Higman: simple finitely presented groups have
solvable word problem

A finitely presented *simple* group has a decidable word problem.  This is
Kuznetsov's theorem (A.V. Kuznetsov, 1958); the later Boone–Higman
characterisation (W.W. Boone and G. Higman, 1974) gives the full iff statement
situating Kuznetsov's result.  §122 in Knill's *Some Fundamental Theorems in
Mathematics*.

A word in the generators `g₁, …, gₙ` and their inverses is encoded as
`List (Fin n × Bool)`, which is `Primcodable`.  The word problem predicate of a
finite presentation `φ : FreeGroup (Fin n) →* G` is `P w := φ (mk w) = 1`; it is
**solvable** when `P` is decidable by an algorithm, captured by mathlib's
`ComputablePred`.  The hypotheses `hsurj` + `hker` unpack
`Group.IsFinitelyPresented G` for this particular presentation `φ`.

The strategy is Kuznetsov's r.e.-from-both-sides argument: `P` is recursively
enumerable, its complement is recursively enumerable (here simplicity is used),
and a predicate that is r.e. with r.e. complement is computable (Post's theorem,
`ComputablePred.computable_iff_re_compl_re`).
-/

variable {G : Type*} [Group G] {n : ℕ}

/-- **The word problem predicate** of a presentation `φ`: the predicate
`P w := φ (FreeGroup.mk w) = 1` that the word `w` represents the identity. -/
def wordProblemPred (φ : FreeGroup (Fin n) →* G) : List (Fin n × Bool) → Prop :=
  fun w => φ (FreeGroup.mk w) = 1

/-- The word problem of a finite presentation `φ` is **solvable** when the word
problem predicate is decidable by an algorithm. -/
def WordProblemSolvable (φ : FreeGroup (Fin n) →* G) : Prop :=
  ComputablePred (wordProblemPred φ)

/-- **Word problem via the kernel.** `P w` holds iff `FreeGroup.mk w ∈ ker φ`. -/
lemma pred_iff_mem_ker (φ : FreeGroup (Fin n) →* G) (w : List (Fin n × Bool)) :
    wordProblemPred φ w ↔ FreeGroup.mk w ∈ MonoidHom.ker φ := by
  rw [MonoidHom.mem_ker, wordProblemPred]

/-- **The kernel is a normal closure of relators.** There is a finite relator
list `R` with `ker φ = normalClosure (relatorSet R)`. -/
lemma ker_eq_normalClosure (φ : FreeGroup (Fin n) →* G)
    (hker : (MonoidHom.ker φ).IsNormalClosureFG) :
    ∃ R : List (Word n),
      MonoidHom.ker φ = Subgroup.normalClosure (relatorSet R) := by
  rcases hker with ⟨T, hT_fin, hT⟩
  rcases finset_to_word_list hT_fin with ⟨R, hR⟩
  refine ⟨R, ?_⟩
  calc
    MonoidHom.ker φ = Subgroup.normalClosure T := by rw [← hT]
    _ = Subgroup.normalClosure (relatorSet R) := by rw [hR]

/-- **Normal-closure membership is r.e.** -/
lemma re_mem_normalClosure (R : List (Word n)) :
    REPred (fun w : Word n =>
      FreeGroup.mk w ∈ Subgroup.normalClosure (relatorSet R)) := by
  have h_mem_eqv : ∀ w, (FreeGroup.mk w ∈ Subgroup.normalClosure (relatorSet R)) ↔
      ∃ c : Certificate n, FreeGroup.reduce (evalCert R c) = FreeGroup.reduce w := by
    intro w
    rw [mem_normalClosure_cert R w]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      rw [← mk_eq_iff_reduce]
      exact hc
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      rw [mk_eq_iff_reduce]
      exact hc
  have h_repred : REPred (fun w : Word n => ∃ c : Certificate n,
      FreeGroup.reduce (evalCert R c) = FreeGroup.reduce w) := by
    have hQ : ComputablePred fun (p : Word n × Certificate n) =>
      FreeGroup.reduce (evalCert R p.2) = FreeGroup.reduce p.1 :=
      check_computablePred R
    exact re_projection hQ
  exact REPred.of_eq h_repred (fun w => (h_mem_eqv w).symm)

/-- **Positive side is r.e.**  The word problem predicate `P` is recursively
enumerable. -/
lemma re_positive (φ : FreeGroup (Fin n) →* G)
    (hker : (MonoidHom.ker φ).IsNormalClosureFG) :
    REPred (wordProblemPred φ) := by
  rcases ker_eq_normalClosure φ hker with ⟨R, hR⟩
  refine REPred.of_eq (re_mem_normalClosure R) (fun w => ?_)
  simpa [hR] using (pred_iff_mem_ker φ w).symm

/-- **The kernel is not everything.** -/
lemma ker_ne_top [IsSimpleGroup G] (φ : FreeGroup (Fin n) →* G)
    (hsurj : Function.Surjective φ) :
    MonoidHom.ker φ ≠ ⊤ := by
  intro h
  have hφ1 : φ = 1 := (MonoidHom.ker_eq_top_iff.mp h)
  have htriv : ∀ g : G, g = 1 := by
    intro g
    obtain ⟨x, hx⟩ := hsurj g
    calc
      g = φ x := by symm; exact hx
      _ = (1 : FreeGroup (Fin n) →* G) x := by rw [hφ1]
      _ = 1 := by simp
  obtain ⟨x, y, hne⟩ := exists_pair_ne G
  exact hne (by
    calc
      x = 1 := htriv x
      _ = y := by symm; exact htriv y)

/-- **Collapse criterion.** With `S = relatorSet R` and
`normalClosure S = ker φ`, for every word `w`,
`φ (mk w) ≠ 1 ↔ normalClosure (S ∪ {mk w}) = ⊤`. -/
lemma collapse [IsSimpleGroup G] (φ : FreeGroup (Fin n) →* G)
    (hsurj : Function.Surjective φ) (R : List (Word n))
    (hR : Subgroup.normalClosure (relatorSet R) = MonoidHom.ker φ)
    (w : Word n) :
    φ (FreeGroup.mk w) ≠ 1 ↔
      Subgroup.normalClosure (relatorSet R ∪ {FreeGroup.mk w}) = ⊤ := by
  let S := relatorSet R
  let N := Subgroup.normalClosure (S ∪ {FreeGroup.mk w})
  have hN_ker : MonoidHom.ker φ ≤ N := by
    rw [← hR]
    apply Subgroup.normalClosure_mono
    intro x hx
    exact Set.mem_union_left {FreeGroup.mk w} hx
  constructor
  · intro hphi
    have h_map : Subgroup.map φ N = Subgroup.normalClosure {φ (FreeGroup.mk w)} :=
      map_normalClosure_insert φ hsurj hR (FreeGroup.mk w)
    have h_map_eq_top : Subgroup.map φ N = ⊤ := by
      rw [h_map]
      exact normalClosure_singleton_top hphi
    exact (top_iff_map_top φ hsurj hN_ker).mpr h_map_eq_top
  · intro hN_top
    by_contra! hphi
    -- hphi : φ (FreeGroup.mk w) = 1
    have h_mem : FreeGroup.mk w ∈ MonoidHom.ker φ := by
      rw [MonoidHom.mem_ker]
      exact hphi
    have h_mem' : FreeGroup.mk w ∈ Subgroup.normalClosure S := by
      rw [hR]
      exact h_mem
    have h_sub : S ∪ {FreeGroup.mk w} ⊆ (Subgroup.normalClosure S : Set (FreeGroup (Fin n))) := by
      intro x hx
      rcases hx with (hx | hx)
      · exact Subgroup.subset_normalClosure hx
      · rw [Set.mem_singleton_iff.mp hx]
        exact h_mem'
    have hN_le_ker : N ≤ Subgroup.normalClosure S := by
      calc
        N = Subgroup.normalClosure (S ∪ {FreeGroup.mk w}) := rfl
        _ ≤ Subgroup.normalClosure ((Subgroup.normalClosure S : Set (FreeGroup (Fin n)))) :=
          Subgroup.normalClosure_mono h_sub
        _ = Subgroup.normalClosure S := Subgroup.normalClosure_idempotent (s := S)
    have hN_eq_ker : N = MonoidHom.ker φ := by
      apply le_antisymm
      · calc
          N ≤ Subgroup.normalClosure S := hN_le_ker
          _ = MonoidHom.ker φ := hR
      · exact hN_ker
    have hker_ne_top : MonoidHom.ker φ ≠ ⊤ := ker_ne_top φ hsurj
    have hN_top' : N = ⊤ := by
      dsimp [N, S]
      exact hN_top
    rw [hN_eq_ker] at hN_top'
    exact hker_ne_top hN_top'

/-- **Generator membership in the extended closure is r.e.** -/
lemma re_generator_mem (R : List (Word n)) (i : Fin n) :
    REPred (fun w : Word n =>
      FreeGroup.of i ∈
        Subgroup.normalClosure (relatorSet R ∪ {FreeGroup.mk w})) := by
  sorry

/-- **Negation as a universal over generators.** With `S = relatorSet R` and
`normalClosure S = ker φ`, `φ (mk w) ≠ 1` iff every generator lies in the
extended normal closure. -/
lemma neg_iff_forall_gen [IsSimpleGroup G] (φ : FreeGroup (Fin n) →* G)
    (hsurj : Function.Surjective φ) (R : List (Word n))
    (hR : Subgroup.normalClosure (relatorSet R) = MonoidHom.ker φ)
    (w : Word n) :
    ¬ wordProblemPred φ w ↔
      ∀ i : Fin n, FreeGroup.of i ∈
        Subgroup.normalClosure (relatorSet R ∪ {FreeGroup.mk w}) := by
  sorry

/-- **Negative side is r.e.**  The complement `w ↦ φ (mk w) ≠ 1` is recursively
enumerable. -/
lemma re_negative [IsSimpleGroup G] (φ : FreeGroup (Fin n) →* G)
    (hsurj : Function.Surjective φ)
    (hker : (MonoidHom.ker φ).IsNormalClosureFG) :
    REPred (fun w : Word n => ¬ wordProblemPred φ w) := by
  rcases ker_eq_normalClosure φ hker with ⟨R, hR⟩
  have hR_symm : Subgroup.normalClosure (relatorSet R) = MonoidHom.ker φ := hR.symm
  have h_forall_re : REPred (fun w : Word n =>
      ∀ i : Fin n, FreeGroup.of i ∈ Subgroup.normalClosure (relatorSet R ∪ {FreeGroup.mk w})) := by
    refine re_forall_fin ?_
    intro i
    exact re_generator_mem R i
  refine REPred.of_eq h_forall_re fun w => ?_
  rw [neg_iff_forall_gen φ hsurj R hR_symm w]

/-- **Post's theorem packaged for the word problem.** If `wordProblemPred φ` is
r.e. and its complement is r.e., then it is a `ComputablePred`. -/
lemma post_re_compl (φ : FreeGroup (Fin n) →* G)
    [DecidablePred (wordProblemPred φ)]
    (hpos : REPred (wordProblemPred φ))
    (hneg : REPred (fun w : Word n => ¬ wordProblemPred φ w)) :
    ComputablePred (wordProblemPred φ) := by
  rw [ComputablePred.computable_iff_re_compl_re]
  exact ⟨hpos, hneg⟩

/-- **Kuznetsov's theorem** (A.V. Kuznetsov, 1958). A finitely presented simple
group has a solvable word problem. -/
@[eval_problem]
theorem boone_higman_simple
    {G : Type*} [Group G] [IsSimpleGroup G]
    {n : ℕ} (φ : FreeGroup (Fin n) →* G)
    (_hsurj : Function.Surjective φ)
    (_hker : (MonoidHom.ker φ).IsNormalClosureFG) :
    WordProblemSolvable φ := by
  -- Equip the predicate with classical decidability
  haveI : DecidablePred (wordProblemPred φ) := Classical.decPred _
  -- By Post's theorem, a decidable-instance predicate is computable iff both it
  -- and its complement are recursively enumerable.
  rw [WordProblemSolvable, ComputablePred.computable_iff_re_compl_re]
  refine ⟨?_, ?_⟩
  · exact re_positive φ _hker
  · exact re_negative φ _hsurj _hker

end BooneHigmanSimpleProblem
end GroupTheory
end LeanEval
