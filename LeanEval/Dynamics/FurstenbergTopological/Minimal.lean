import Mathlib
import EvalTools.Markers

/-!
# Minimal subsystems and ω-limit sets

For a homeomorphism `T` of a compact metric space `X` we develop the structural
input to the Furstenberg–Weiss recurrence theorem: the existence of a minimal
subsystem (a nonempty closed invariant set with no proper nonempty closed
invariant subset), and the basic properties of forward ω-limit sets.

A set `M` is *invariant* when `T '' M = M` (the two-sided / `ℤ`-action
convention).  We deliberately phrase minimality directly as a property of closed
invariant sets rather than via Mathlib's one-sided `MulAction`/`IsMinimal`
notions.
-/

namespace LeanEval
namespace Dynamics

open scoped Topology

variable {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]

/-- **The iteration system of `T`.** For an invariant set `M` (`∀ x, x ∈ M ↔ T x ∈ M`)
the homeomorphism `T` restricts to a self-homeomorphism `T|_M : M ≃ₜ M` of the
compact subspace `M`, given on representatives by `(T|_M) x = T x`. -/
def restrict (T : X ≃ₜ X) (M : Set X) (hM : ∀ x, x ∈ M ↔ T x ∈ M) : M ≃ₜ M :=
  @Homeomorph.subtype X X _ _ (· ∈ M) (· ∈ M) T hM

/-- A self-map `S` of a space is *minimal* when the only nonempty closed invariant
subset is the whole space. -/
def IsMinimal {Y : Type*} [TopologicalSpace Y] (S : Y → Y) : Prop :=
  ∀ C : Set Y, IsClosed C → S '' C = C → C.Nonempty → C = Set.univ

/-- The forward `ω`-limit set of `x` under `f`: `ω(x) = ⋂_N closure {f^[k] x : k ≥ N}`,
expressed via Mathlib's `omegaLimit` of the singleton `{x}` along `atTop`. -/
def omegaFwd (f : X → X) (x : X) : Set X :=
  omegaLimit Filter.atTop (fun n : ℕ => f^[n]) {x}

variable (T : X ≃ₜ X)

/-- **Directed intersections of compact sets are nonempty.** A downward-directed
family of nonempty closed subsets of a compact space has nonempty intersection. -/
theorem directed_inter_nonempty {ι : Type*} [Nonempty ι] (C : ι → Set X)
    (hdir : Directed (· ⊇ ·) C) (hne : ∀ i, (C i).Nonempty) (hcl : ∀ i, IsClosed (C i)) :
    (⋂ i, C i).Nonempty :=
  IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hdir hne
    (fun i => (hcl i).isCompact) hcl

/-- **Chains of subsystems have a subsystem lower bound.** A nonempty
downward-directed family of nonempty closed invariant sets has an intersection
that is again nonempty, closed, and invariant. -/
theorem chain_inter_invariant {ι : Type*} [Nonempty ι] (C : ι → Set X)
    (hdir : Directed (· ⊇ ·) C) (hne : ∀ i, (C i).Nonempty) (hcl : ∀ i, IsClosed (C i))
    (hinv : ∀ i, (T : X → X) '' C i = C i) :
    (⋂ i, C i).Nonempty ∧ IsClosed (⋂ i, C i) ∧
      (T : X → X) '' (⋂ i, C i) = ⋂ i, C i := by
  have h_nonempty : (⋂ i, C i).Nonempty :=
    directed_inter_nonempty C hdir hne hcl
  have h_closed : IsClosed (⋂ i, C i) :=
    isClosed_iInter hcl
  have h_inv : (T : X → X) '' (⋂ i, C i) = ⋂ i, C i := by
    have hT_inj : Function.Injective (T : X → X) := T.injective
    have hT_inj_on : Set.InjOn (T : X → X) (⋃ i, C i) :=
      Set.injOn_of_injective hT_inj
    calc
      (T : X → X) '' (⋂ i, C i) = ⋂ i, ((T : X → X) '' C i) := by
        rw [Set.InjOn.image_iInter_eq hT_inj_on]
      _ = ⋂ i, C i := by
        simp_rw [hinv]
  exact And.intro h_nonempty (And.intro h_closed h_inv)

/-- **Existence of a minimal subsystem.** There is a nonempty closed invariant set
`M` with no proper nonempty closed invariant subset. -/
theorem exists_minimal_subsystem :
    ∃ M : Set X, M.Nonempty ∧ IsClosed M ∧ (T : X → X) '' M = M ∧
      ∀ C : Set X, C ⊆ M → C.Nonempty → IsClosed C → (T : X → X) '' C = C → C = M := by
  -- S is the set of nonempty closed invariant subsets of X
  let S : Set (Set X) := {M | M.Nonempty ∧ IsClosed M ∧ (T : X → X) '' M = M}
  have huniv : Set.univ ∈ S := by
    refine ⟨Set.univ_nonempty, isClosed_univ, ?_⟩
    calc
      (T : X → X) '' Set.univ = Set.range (T : X → X) := Set.image_univ
      _ = Set.univ := T.surjective.range_eq
  -- Every chain in S (ordered by ⊆) has a lower bound in S
  have hchain : ∀ c ⊆ S, IsChain (· ⊆ ·) c → ∃ lb ∈ S, ∀ s ∈ c, lb ⊆ s := by
    intro c hcS hchain
    by_cases hcne : c.Nonempty
    · -- c is nonempty: use intersection as lower bound
      rcases hcne with ⟨s0, hs0⟩
      have h_nonempty_ι : Nonempty c := ⟨⟨s0, hs0⟩⟩
      let f : c → Set X := Subtype.val
      have hdir : Directed (· ⊇ ·) f := by
        intro i j
        rcases hchain.total i.2 j.2 with (h | h)
        · -- h : f i ⊆ f j, so f i is the smaller; take k := i
          exact ⟨i, Set.Subset.refl _, h⟩
        · -- h : f j ⊆ f i, so f j is the smaller; take k := j
          exact ⟨j, h, Set.Subset.refl _⟩
      have hne : ∀ i : c, (f i).Nonempty := by
        intro i; exact (hcS i.2).1
      have hcl : ∀ i : c, IsClosed (f i) := by
        intro i; exact (hcS i.2).2.1
      have hinv : ∀ i : c, (T : X → X) '' f i = f i := by
        intro i; exact (hcS i.2).2.2
      have h_chain_inter := chain_inter_invariant T f hdir hne hcl hinv
      refine ⟨⋂ i : c, f i, ?_, ?_⟩
      · exact ⟨h_chain_inter.1, h_chain_inter.2.1, h_chain_inter.2.2⟩
      · intro s hs
        exact Set.iInter_subset (fun (i : c) => f i) ⟨s, hs⟩
    · -- c is empty: use Set.univ as lower bound
      refine ⟨Set.univ, huniv, ?_⟩
      intro s hs
      exfalso; exact hcne ⟨s, hs⟩
  rcases zorn_superset S hchain with ⟨M, hM⟩
  rcases hM.1 with ⟨hM_nonempty, hM_closed, hM_inv⟩
  refine ⟨M, hM_nonempty, hM_closed, hM_inv, ?_⟩
  intro C hC_sub hC_nonempty hC_closed hC_inv
  have hC_S : C ∈ S := ⟨hC_nonempty, hC_closed, hC_inv⟩
  have hM_sub_C : M ⊆ C := hM.2 hC_S hC_sub
  exact Set.Subset.antisymm hC_sub hM_sub_C

/-- **`ω`-limit sets are nonempty.** -/
theorem omega_nonempty (x : X) : (omegaFwd (T : X → X) x).Nonempty := by
  unfold omegaFwd
  exact nonempty_omegaLimit Filter.atTop (fun n : ℕ => (T : X → X)^[n]) {x} (Set.singleton_nonempty x)

/-- **`ω`-limit sets are closed.** -/
theorem omega_closed (x : X) : IsClosed (omegaFwd (T : X → X) x) := by
  -- omegaFwd expands to omegaLimit, and Mathlib's isClosed_omegaLimit handles the rest
  simpa [omegaFwd] using isClosed_omegaLimit (f := Filter.atTop)
    (ϕ := fun (n : ℕ) => (T : X → X)^[n]) (s := {x})

/-- **`ω`-limit sets are forward invariant**: `T (ω(x)) ⊆ ω(x)`. -/
theorem omega_forward_invariant (x : X) :
    (T : X → X) '' omegaFwd (T : X → X) x ⊆ omegaFwd (T : X → X) x := by
  have hT_cont : Continuous (T : X → X) := T.continuous
  have h_comm (t : ℕ) (z : X) : (T : X → X) ((T : X → X)^[t] z) = ((T : X → X)^[t]) ((T : X → X) z) := by
    calc
      (T : X → X) ((T : X → X)^[t] z) = (T : X → X)^[t+1] z := by
        rw [Function.iterate_succ_apply']
      _ = ((T : X → X)^[t]) ((T : X → X) z) := by
        rw [Function.iterate_succ_apply]

  -- Step 1: mapsTo_omegaLimit gives T(ω(x)) ⊆ ω(T x)
  have h_mapsTo_Tx : Set.MapsTo (T : X → X) (omegaFwd (T : X → X) x) (omegaFwd (T : X → X) (T x)) := by
    have hs : Set.MapsTo (T : X → X) ({x} : Set X) ({T x} : Set X) := by
      intro z hz
      simp at hz
      subst hz
      simp
    have h := mapsTo_omegaLimit (f := Filter.atTop) (α' := X) (β' := X) (ϕ := fun (n : ℕ) => (T : X → X)^[n])
      (ϕ' := fun (n : ℕ) => (T : X → X)^[n]) (ga := (T : X → X)) (s' := {T x})
      (hs := hs) (hg := h_comm) (hgc := hT_cont)
    simpa [omegaFwd] using h

  -- Step 2: omegaLimit_image_eq + omegaLimit_subset_of_tendsto give ω(T x) ⊆ ω(x)
  have h_shift_tendsto : Filter.Tendsto (fun (n : ℕ) => n + 1) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_atTop.mpr
    intro N
    refine ⟨N, ?_⟩
    intro m hm
    omega

  have h_eq_shift : omegaFwd (T : X → X) (T x) = omegaLimit Filter.atTop (fun (n : ℕ) => (T : X → X)^[n+1]) {x} := by
    calc
      omegaFwd (T : X → X) (T x) = omegaLimit Filter.atTop (fun (n : ℕ) => (T : X → X)^[n]) {T x} := rfl
      _ = omegaLimit Filter.atTop (fun (n : ℕ) => (T : X → X)^[n]) ((T : X → X) '' {x}) := by simp
      _ = omegaLimit Filter.atTop (fun (n : ℕ) (z : X) => ((T : X → X)^[n]) ((T : X → X) z)) {x} := by
        rw [omegaLimit_image_eq]
      _ = omegaLimit Filter.atTop (fun (n : ℕ) => (T : X → X)^[n+1]) {x} := by
        apply congrArg (fun (ψ : ℕ → X → X) => omegaLimit Filter.atTop ψ {x})
        ext n z
        simp

  have h_subset : omegaFwd (T : X → X) (T x) ⊆ omegaFwd (T : X → X) x := by
    rw [h_eq_shift, omegaFwd]
    simpa using omegaLimit_subset_of_tendsto (m := fun (n : ℕ) => n + 1) (hf := h_shift_tendsto)
      (ϕ := fun (n : ℕ) => (T : X → X)^[n]) (s := {x})

  -- Step 3: Combine
  have h_image_subset : (T : X → X) '' omegaFwd (T : X → X) x ⊆ omegaFwd (T : X → X) (T x) :=
    h_mapsTo_Tx.image_subset
  exact Set.Subset.trans h_image_subset h_subset

/-- **`ω`-limit sets are invariant**: `T (ω(x)) = ω(x)`. -/
theorem omega_two_sided_invariant (x : X) :
    (T : X → X) '' omegaFwd (T : X → X) x = omegaFwd (T : X → X) x := by
  sorry

/-- **`ω`-limit sets are subsystems**: nonempty, closed, and invariant. -/
theorem omega_limit_properties (x : X) :
    (omegaFwd (T : X → X) x).Nonempty ∧ IsClosed (omegaFwd (T : X → X) x) ∧
      (T : X → X) '' omegaFwd (T : X → X) x = omegaFwd (T : X → X) x := by
  have h_nonempty : (omegaFwd (T : X → X) x).Nonempty := omega_nonempty T x
  have h_closed : IsClosed (omegaFwd (T : X → X) x) := omega_closed T x
  have h_inv : (T : X → X) '' omegaFwd (T : X → X) x = omegaFwd (T : X → X) x :=
    omega_two_sided_invariant T x
  exact ⟨h_nonempty, h_closed, h_inv⟩

/-- **Forward orbits are dense in a minimal system.** If `T` is minimal then for
every `x` the forward orbit `{T^[k] x : k ≥ 0}` is dense. -/
theorem minimal_forward_dense (hmin : IsMinimal (T : X → X)) (x : X) :
    Dense (Set.range (fun k : ℕ => (T : X → X)^[k] x)) := by
  have hprops := omega_limit_properties T x
  rcases hprops with ⟨hne, hcl, hinv⟩
  have huniv : omegaFwd (T : X → X) x = Set.univ :=
    hmin (omegaFwd (T : X → X) x) hcl hinv hne
  have hsubset : omegaFwd (T : X → X) x ⊆ closure (Set.range (fun k : ℕ => (T : X → X)^[k] x)) := by
    calc
      omegaFwd (T : X → X) x = omegaLimit Filter.atTop (fun n : ℕ => (T : X → X)^[n]) {x} := rfl
      _ ⊆ closure (Set.image2 (fun n : ℕ => (T : X → X)^[n]) Set.univ {x}) :=
        omegaLimit_subset_closure_image2 (f := Filter.atTop) (ϕ := fun n : ℕ => (T : X → X)^[n])
          (s := {x}) (u := Set.univ) (hu := Filter.univ_mem)
      _ = closure ((fun n : ℕ => (T : X → X)^[n] x) '' Set.univ) := by rw [Set.image2_singleton_right]
      _ = closure (Set.range (fun k : ℕ => (T : X → X)^[k] x)) := by simp
  have hunivsubset : Set.univ ⊆ closure (Set.range (fun k : ℕ => (T : X → X)^[k] x)) := by
    rw [← huniv]
    exact hsubset
  rw [dense_iff_closure_eq]
  exact Set.Subset.antisymm (Set.subset_univ _) hunivsubset

end Dynamics
end LeanEval
