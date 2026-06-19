import Mathlib
import EvalTools.Markers
import LeanEval.Dynamics.FurstenbergTopological.Recurrence
import LeanEval.Dynamics.FurstenbergTopological.Sequence

namespace LeanEval
namespace Dynamics

/-!
# Furstenberg–Weiss topological multiple recurrence (single-transformation form)

For every homeomorphism `T` of a nonempty compact metric space `X`,
there is a point `x ∈ X` that is **multiply recurrent**: for every
`d ≥ 1`, the iterates `T, T², …, T^d` of `x` return arbitrarily close
to `x` along a single common time sequence — `T^{j · n_k}(x) → x` as
`k → ∞` for every `j ∈ {1, …, d}`, with a strictly increasing
`n : ℕ → ℕ` shared across `j`.

This is the single-transformation formulation in Knill §56, which
specialises the full Furstenberg–Weiss recurrence theorem to the
family `T, T², …, T^d` instead of arbitrary commuting homeomorphisms.

Compact-Hausdorff alone is insufficient for this sequential
formulation: on the shift over `Ultrafilter ℤ` (compact Hausdorff, not
first-countable), every convergent sequence is eventually constant, so
`T^{j · n_k}(x) → x` along a strictly increasing `n_k` would force
`n_k = 0` eventually. First-countability would suffice as a hypothesis;
the compact-metric form is the standard Furstenberg–Weiss statement.
-/

open Filter Topology

/-- A point `x : X` is **multiply recurrent** for `T : X → X` if for
every `d ≥ 1` there is a strictly increasing `n : ℕ → ℕ` such that
`T^{j · n_k}(x) → x` for every `j ∈ {1, …, d}`. -/
def IsMultiplyRecurrent {X : Type*} [TopologicalSpace X]
    (T : X → X) (x : X) : Prop :=
  ∀ d : ℕ, 1 ≤ d →
    ∃ n : ℕ → ℕ, StrictMono n ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ d →
        Tendsto (fun k : ℕ => T^[j * n k] x) atTop (𝓝 x)

/-- **Restricted iterates agree with ambient iterates.** For a subsystem `M`
(`∀ x, x ∈ M ↔ T x ∈ M`), the iterate `(T|_M)^[k] x`, viewed in `X`, equals
`T^[k] x`. (The inclusion `M ↪ X` is moreover an isometric embedding, so subspace
and ambient distances coincide, by `isometry_subtype_coe`.) -/
theorem restricted_iterate_agreement {X : Type*} [MetricSpace X]
    (T : X ≃ₜ X) (M : Set X) (hM : ∀ x, x ∈ M ↔ T x ∈ M) (x : M) (k : ℕ) :
    (↑(((restrict T M hM : M → M))^[k] x) : X) = (T : X → X)^[k] (x : X) := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    calc
      (↑(((restrict T M hM : M → M))^[k.succ] x) : X)
          = (T : X → X) (↑(((restrict T M hM : M → M))^[k] x) : X) := by
        simp [Function.iterate_succ_apply', restrict, Homeomorph.subtype_apply_coe]
      _ = (T : X → X) ((T : X → X)^[k] (x : X)) := by
        rw [ih]
      _ = (T : X → X)^[k.succ] (x : X) := by
        simp [Function.iterate_succ_apply']

/-- **Transfer from a minimal subsystem to the ambient space.** If `x ∈ M` is
multiply recurrent for the restricted homeomorphism `T|_M`, then it is multiply
recurrent for `T` in `X`. -/
theorem minimal_transfer {X : Type*} [MetricSpace X]
    (T : X ≃ₜ X) (M : Set X) (hM : ∀ x, x ∈ M ↔ T x ∈ M) (x : M)
    (hx : IsMultiplyRecurrent (restrict T M hM : M → M) x) :
    IsMultiplyRecurrent (T : X → X) (x : X) := by
  intro d hd
  rcases hx d hd with ⟨n, hn_mono, hn⟩
  refine ⟨n, hn_mono, ?_⟩
  intro j hj1 hjd
  have h_tendsto_M : Filter.Tendsto (fun k : ℕ => ((restrict T M hM : M → M)^[j * n k] x))
      Filter.atTop (𝓝 x) := hn j hj1 hjd
  have h_cont : Continuous (fun (z : M) => (z : X)) := continuous_subtype_val
  have h_sq : Filter.Tendsto (fun (z : M) => (z : X)) (𝓝 x) (𝓝 (x : X)) :=
    h_cont.tendsto x
  have h_comp : Filter.Tendsto (fun k : ℕ => ((restrict T M hM : M → M)^[j * n k] x : X))
      Filter.atTop (𝓝 (x : X)) :=
    h_sq.comp h_tendsto_M
  have h_agreement (k : ℕ) : (((restrict T M hM : M → M)^[j * n k] x : M) : X) = (T : X → X)^[j * n k] (x : X) := by
    simpa using restricted_iterate_agreement T M hM x (j * n k)
  simpa [h_agreement] using h_comp

/-- **Furstenberg–Weiss topological multiple recurrence** (single-
transformation form). Every homeomorphism `T` of a nonempty compact
metric space `X` has a multiply recurrent point. -/
@[eval_problem]
theorem furstenberg_topological_recurrence {X : Type*} [MetricSpace X]
    [CompactSpace X] [Nonempty X] (T : X ≃ₜ X) :
    ∃ x : X, IsMultiplyRecurrent (T : X → X) x := by
  -- Step 1: obtain a minimal subsystem M of X
  rcases exists_minimal_subsystem T with ⟨M, hM_ne, hM_closed, hM_inv, hM_min⟩

  -- Step 2: convert image invariance to membership invariance ∀ x, x ∈ M ↔ T x ∈ M
  have hM_mem : ∀ x, x ∈ M ↔ T x ∈ M := by
    intro x
    constructor
    · intro hx
      have hTx_in_image : T x ∈ (T : X → X) '' M :=
        (Set.mem_image (T : X → X) M (T x)).mpr ⟨x, hx, rfl⟩
      rw [hM_inv] at hTx_in_image
      exact hTx_in_image
    · intro hTx
      have hTx_in_image : T x ∈ (T : X → X) '' M := by
        rw [hM_inv]
        exact hTx
      rcases (Set.mem_image (T : X → X) M (T x)).mp hTx_in_image with ⟨y, hyM, hy⟩
      have hy_eq_x : y = x := T.injective hy
      subst hy_eq_x
      exact hyM

  -- Step 3: M is a nonempty compact metric space (as a closed subspace of X)
  have hM_nonempty : Nonempty M := by
    rcases hM_ne with ⟨x, hx⟩
    exact ⟨⟨x, hx⟩⟩
  have hM_compact : CompactSpace M :=
    (hM_closed.isClosedEmbedding_subtypeVal (X := X)).compactSpace

  -- Step 4: the restricted homeomorphism T|_M is minimal
  have hmin : IsMinimal (restrict T M hM_mem : M → M) := by
    intro C hC_closed hC_inv hC_ne
    let ι : M → X := Subtype.val
    have hι_closedEmb : IsClosedEmbedding ι :=
      hM_closed.isClosedEmbedding_subtypeVal
    set C' : Set X := ι '' C with hC'_def
    have hC'_sub_M : C' ⊆ M := by
      rintro _ ⟨x, hx, rfl⟩; exact x.2
    have hC'_ne : C'.Nonempty := by
      rcases hC_ne with ⟨x, hx⟩
      refine ⟨ι x, x, hx, rfl⟩
    have hC'_closed : IsClosed C' :=
      hι_closedEmb.isClosedMap C hC_closed
    have hC'_inv : (T : X → X) '' C' = C' := by
      apply Set.Subset.antisymm
      · rintro z ⟨w, hw, rfl⟩
        rcases hw with ⟨x, hxC, rfl⟩
        have hRxC_mem : restrict T M hM_mem x ∈ C := by
          have htemp : restrict T M hM_mem x ∈ (restrict T M hM_mem : M → M) '' C :=
            (Set.mem_image (restrict T M hM_mem : M → M) C _).mpr ⟨x, hxC, rfl⟩
          rw [hC_inv] at htemp
          exact htemp
        have h_mem : T (ι x) ∈ C' :=
          (Set.mem_image ι C (T (ι x))).mpr ⟨restrict T M hM_mem x, hRxC_mem, rfl⟩
        exact h_mem
      · rintro z ⟨x, hxC, rfl⟩
        have hx_in_RC : x ∈ (restrict T M hM_mem : M → M) '' C := by
          rw [hC_inv]
          exact hxC
        rcases (Set.mem_image (restrict T M hM_mem : M → M) C x).mp hx_in_RC with ⟨y, hyC, hy⟩
        have hyC' : ι y ∈ C' := Set.mem_image_of_mem ι hyC
        have h_eq : T (ι y) = ι x := by
          calc
            T (ι y) = ((restrict T M hM_mem : M → M) y).val := rfl
            _ = x.val := by
              simp [hy]
            _ = ι x := rfl
        refine (Set.mem_image (T : X → X) C' (ι x)).mpr ⟨ι y, hyC', h_eq⟩
    have hC'_eq_M : C' = M :=
      hM_min C' hC'_sub_M hC'_ne hC'_closed hC'_inv
    ext x
    constructor
    · intro _
      exact Set.mem_univ _
    · intro _
      have : ι x ∈ C' := by
        rw [hC'_eq_M]
        exact x.2
      rcases (Set.mem_image ι C (ι x)).mp this with ⟨y, hyC, hy⟩
      have hy_eq_x : y = x := Subtype.val_injective hy
      subst hy_eq_x
      exact hyC

  -- Step 5: residual_recurrent gives a point x in M with qualitative recurrence
  rcases residual_recurrent (T := restrict T M hM_mem) hmin with ⟨x, hx⟩

  -- Step 6: recurrence_sequential upgrades to sequential recurrence (IsMultiplyRecurrent) inside M
  have hx_mul : IsMultiplyRecurrent (restrict T M hM_mem : M → M) x := by
    intro d hd
    rcases recurrence_sequential (T := restrict T M hM_mem) x d hd (hx d hd) with ⟨n, hn_mono, hn⟩
    exact ⟨n, hn_mono, hn⟩

  -- Step 7: minimal_transfer lifts multiply-recurrent point from M to X
  exact ⟨(x : X), minimal_transfer T M hM_mem x hx_mul⟩

end Dynamics
end LeanEval
