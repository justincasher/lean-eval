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
    (⋂ i, C i).Nonempty := by
  sorry

/-- **Chains of subsystems have a subsystem lower bound.** A nonempty
downward-directed family of nonempty closed invariant sets has an intersection
that is again nonempty, closed, and invariant. -/
theorem chain_inter_invariant {ι : Type*} [Nonempty ι] (C : ι → Set X)
    (hdir : Directed (· ⊇ ·) C) (hne : ∀ i, (C i).Nonempty) (hcl : ∀ i, IsClosed (C i))
    (hinv : ∀ i, (T : X → X) '' C i = C i) :
    (⋂ i, C i).Nonempty ∧ IsClosed (⋂ i, C i) ∧
      (T : X → X) '' (⋂ i, C i) = ⋂ i, C i := by
  sorry

/-- **Existence of a minimal subsystem.** There is a nonempty closed invariant set
`M` with no proper nonempty closed invariant subset. -/
theorem exists_minimal_subsystem :
    ∃ M : Set X, M.Nonempty ∧ IsClosed M ∧ (T : X → X) '' M = M ∧
      ∀ C : Set X, C ⊆ M → C.Nonempty → IsClosed C → (T : X → X) '' C = C → C = M := by
  sorry

/-- **`ω`-limit sets are nonempty.** -/
theorem omega_nonempty (x : X) : (omegaFwd (T : X → X) x).Nonempty := by
  sorry

/-- **`ω`-limit sets are closed.** -/
theorem omega_closed (x : X) : IsClosed (omegaFwd (T : X → X) x) := by
  sorry

/-- **`ω`-limit sets are forward invariant**: `T (ω(x)) ⊆ ω(x)`. -/
theorem omega_forward_invariant (x : X) :
    (T : X → X) '' omegaFwd (T : X → X) x ⊆ omegaFwd (T : X → X) x := by
  sorry

/-- **`ω`-limit sets are invariant**: `T (ω(x)) = ω(x)`. -/
theorem omega_two_sided_invariant (x : X) :
    (T : X → X) '' omegaFwd (T : X → X) x = omegaFwd (T : X → X) x := by
  sorry

/-- **`ω`-limit sets are subsystems**: nonempty, closed, and invariant. -/
theorem omega_limit_properties (x : X) :
    (omegaFwd (T : X → X) x).Nonempty ∧ IsClosed (omegaFwd (T : X → X) x) ∧
      (T : X → X) '' omegaFwd (T : X → X) x = omegaFwd (T : X → X) x := by
  sorry

/-- **Forward orbits are dense in a minimal system.** If `T` is minimal then for
every `x` the forward orbit `{T^[k] x : k ≥ 0}` is dense. -/
theorem minimal_forward_dense (hmin : IsMinimal (T : X → X)) (x : X) :
    Dense (Set.range (fun k : ℕ => (T : X → X)^[k] x)) := by
  sorry

end Dynamics
end LeanEval
