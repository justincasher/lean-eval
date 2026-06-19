import EvalTools.Markers
import LeanEval.Dynamics.FurstenbergTopological.VdW
import LeanEval.Dynamics.FurstenbergTopological.Minimal

/-!
# Approximate multiple recurrence and density of the recurrence sets

Building on van der Waerden's theorem and the minimal-subsystem machinery, this
file proves the *approximate* multiple recurrence statement (by colouring an
orbit with a finite `ε`-net) and then, inside a minimal system, that the
recurrence sets `A_{d,ε}` are open and dense.  A Baire-category argument yields a
single point that is recurrent at every order in the qualitative sense.
-/

namespace LeanEval
namespace Dynamics

open scoped Topology

variable {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]

/-- The recurrence set `A_{d,ε} = {x | ∃ n ≥ 1, ∀ 1 ≤ j ≤ d, dist (T^[j n] x) x < ε}`. -/
def recurrenceSet (T : X → X) (d : ℕ) (ε : ℝ) : Set X :=
  {x | ∃ n : ℕ, 1 ≤ n ∧ ∀ j, 1 ≤ j → j ≤ d → dist (T^[j * n] x) x < ε}

variable (T : X ≃ₜ X)

/-- **Finite `ε`-cover of a compact space.** For every `ε > 0` there is a finite
set of centres whose `ε`-balls cover `X`. -/
theorem finite_eps_cover (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset X, (Set.univ : Set X) ⊆ ⋃ c ∈ s, Metric.ball c ε := by
  sorry

/-- **Orbit colouring by an `ε`-net.** Given centres whose `ε/2`-balls cover `X`,
each orbit time `i` can be assigned a centre `col i` whose ball contains
`T^[i] z`. -/
theorem orbit_colouring (ε : ℝ) (hε : 0 < ε) (z : X) (s : Finset X)
    (hs : (Set.univ : Set X) ⊆ ⋃ c ∈ s, Metric.ball c (ε / 2)) :
    ∃ col : ℕ → X, (∀ i, col i ∈ s) ∧
      ∀ i, dist ((T : X → X)^[i] z) (col i) < ε / 2 := by
  sorry

/-- **A common ball bounds the distance.** Two points in a common `ε/2`-ball are
within `ε` of each other. -/
theorem common_ball_dist {a b c : X} {ε : ℝ}
    (ha : a ∈ Metric.ball c (ε / 2)) (hb : b ∈ Metric.ball c (ε / 2)) :
    dist a b < ε := by
  sorry

/-- **Approximate multiple recurrence.** For every `ε > 0` and `d ≥ 1` there are a
point `x` and `n ≥ 1` with `dist (T^[j n] x) x < ε` for all `1 ≤ j ≤ d`. -/
theorem eps_multiple_recurrence (ε : ℝ) (hε : 0 < ε) (d : ℕ) (hd : 1 ≤ d) :
    ∃ (x : X) (n : ℕ), 1 ≤ n ∧
      ∀ j, 1 ≤ j → j ≤ d → dist ((T : X → X)^[j * n] x) x < ε := by
  sorry

/-- **The recurrence sets are open.** -/
theorem recurrenceSet_open (d : ℕ) (ε : ℝ) :
    IsOpen (recurrenceSet (T : X → X) d ε) := by
  sorry

/-- **Orbit preimages cover a minimal system.** In a minimal system every point's
forward orbit meets a given nonempty open set. -/
theorem orbit_preimage_cover (hmin : IsMinimal (T : X → X)) {U : Set X}
    (hU : IsOpen U) (hUne : U.Nonempty) (x : X) :
    ∃ k : ℕ, (T : X → X)^[k] x ∈ U := by
  sorry

/-- **Finite cover by orbit preimages.** In a minimal system the preimages
`T^{-k} U` (`k ≤ K`) cover the whole space for some `K`. -/
theorem cover_by_preimages (hmin : IsMinimal (T : X → X)) {U : Set X}
    (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ K : ℕ, ∀ x : X, ∃ k, k ≤ K ∧ (T : X → X)^[k] x ∈ U := by
  sorry

/-- **Positive minimum over a finite family of moduli.** A finite family of strictly
positive reals indexed by `{0, …, K}` has a strictly positive lower bound. -/
theorem finite_min_pos (K : ℕ) (δ : ℕ → ℝ) (hδ : ∀ k ≤ K, 0 < δ k) :
    ∃ d : ℝ, 0 < d ∧ ∀ k ≤ K, d ≤ δ k := by
  sorry

/-- **Uniform modulus for finitely many iterates.** On a compact space, for every
`ε > 0` there is `δ > 0` controlling `T^[k]` simultaneously for all `k ≤ K`. -/
theorem uniform_modulus (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a b : X, dist a b < δ →
      ∀ k ≤ K, dist ((T : X → X)^[k] a) ((T : X → X)^[k] b) < ε := by
  sorry

/-- **The recurrence sets are dense.** In a minimal system each `A_{d,ε}`
(`d ≥ 1`, `ε > 0`) is dense. -/
theorem recurrenceSet_dense (hmin : IsMinimal (T : X → X)) (d : ℕ) (hd : 1 ≤ d)
    (ε : ℝ) (hε : 0 < ε) : Dense (recurrenceSet (T : X → X) d ε) := by
  sorry

/-- **A residual point exists.** The countable intersection of the recurrence sets
`A_{d+1, 1/(m+1)}` is dense (hence nonempty) in a minimal system. -/
theorem recurrence_residual_dense (hmin : IsMinimal (T : X → X)) :
    Dense (⋂ d : ℕ, ⋂ m : ℕ, recurrenceSet (T : X → X) (d + 1) (1 / ((m : ℝ) + 1))) := by
  sorry

/-- **A point recurrent at every order.** In a minimal system there is a point `x`
such that for every `d ≥ 1` and `ε > 0` there is `n ≥ 1` with
`dist (T^[j n] x) x < ε` for all `1 ≤ j ≤ d`. -/
theorem residual_recurrent (hmin : IsMinimal (T : X → X)) :
    ∃ x : X, ∀ d : ℕ, 1 ≤ d → ∀ ε : ℝ, 0 < ε →
      ∃ n : ℕ, 1 ≤ n ∧ ∀ j, 1 ≤ j → j ≤ d → dist ((T : X → X)^[j * n] x) x < ε := by
  sorry

end Dynamics
end LeanEval
