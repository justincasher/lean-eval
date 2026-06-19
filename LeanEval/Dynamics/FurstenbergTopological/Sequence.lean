import Mathlib
import EvalTools.Markers

/-!
# From qualitative recurrence to a return-time sequence

These lemmas upgrade the qualitative recurrence statement (for every `ε > 0`
there is a return time `n ≥ 1` with all `T^[j n] x` within `ε` of `x`) into a
genuine convergent return-time sequence `T^[j n_k] x → x`, handling both the case
of arbitrarily large small returns (subsequence extraction) and the bounded case
(which forces a periodic point).
-/

namespace LeanEval
namespace Dynamics

open scoped Topology

variable {X : Type*} [MetricSpace X] (T : X ≃ₜ X)

/-- **Subsequence extraction from frequent small returns.** If small return gaps
occur at arbitrarily large times, there is a strictly increasing `n_k` with
`T^[j n_k] x → x` for every `1 ≤ j ≤ d`. -/
theorem recurrence_subseq (x : X) (d : ℕ)
    (h : ∀ N : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ n, N < n ∧ ∀ j, 1 ≤ j → j ≤ d → dist ((T : X → X)^[j * n] x) x < ε) :
    ∃ n : ℕ → ℕ, StrictMono n ∧
      ∀ j, 1 ≤ j → j ≤ d →
        Filter.Tendsto (fun k => (T : X → X)^[j * n k] x) Filter.atTop (𝓝 x) := by
  sorry

/-- **A return time recurs across all scales.** If the qualitative hypothesis holds
but small returns are not arbitrarily large, some fixed `n* ∈ {1, …, N₀}` has gap
below `1/m` for infinitely many `m`. -/
theorem pigeonhole_fixed_return (x : X) (d : ℕ)
    (h1 : ∀ ε : ℝ, 0 < ε →
      ∃ n, 1 ≤ n ∧ ∀ j, 1 ≤ j → j ≤ d → dist ((T : X → X)^[j * n] x) x < ε)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (N₀ : ℕ)
    (h2 : ∀ n, N₀ < n →
      ¬ (∀ j, 1 ≤ j → j ≤ d → dist ((T : X → X)^[j * n] x) x < ε₀)) :
    ∃ nstar : ℕ, 1 ≤ nstar ∧ nstar ≤ N₀ ∧
      {m : ℕ | ∀ j, 1 ≤ j → j ≤ d →
        dist ((T : X → X)^[j * nstar] x) x < 1 / (m : ℝ)}.Infinite := by
  sorry

/-- **A gap below every scale is zero.** A nonnegative real that is below `1/m` for
infinitely many `m` is zero. -/
theorem small_inf_implies_zero {a : ℝ} (ha : 0 ≤ a)
    (h : {m : ℕ | a < 1 / (m : ℝ)}.Infinite) : a = 0 := by
  sorry

/-- **Bounded return times force a periodic point.** Under the qualitative
hypothesis, if small returns are not arbitrarily large then there is `n* ≥ 1`
with `T^[j n*] x = x` for all `1 ≤ j ≤ d`. -/
theorem recurrence_periodic (x : X) (d : ℕ)
    (h1 : ∀ ε : ℝ, 0 < ε →
      ∃ n, 1 ≤ n ∧ ∀ j, 1 ≤ j → j ≤ d → dist ((T : X → X)^[j * n] x) x < ε)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (N₀ : ℕ)
    (h2 : ∀ n, N₀ < n →
      ¬ (∀ j, 1 ≤ j → j ≤ d → dist ((T : X → X)^[j * n] x) x < ε₀)) :
    ∃ nstar : ℕ, 1 ≤ nstar ∧ ∀ j, 1 ≤ j → j ≤ d → (T : X → X)^[j * nstar] x = x := by
  sorry

/-- **Qualitative recurrence yields a recurrence sequence.** Under the qualitative
hypothesis there is a strictly increasing `n_k` with `T^[j n_k] x → x` for every
`1 ≤ j ≤ d`. -/
theorem recurrence_sequential (x : X) (d : ℕ) (hd : 1 ≤ d)
    (h : ∀ ε : ℝ, 0 < ε →
      ∃ n, 1 ≤ n ∧ ∀ j, 1 ≤ j → j ≤ d → dist ((T : X → X)^[j * n] x) x < ε) :
    ∃ n : ℕ → ℕ, StrictMono n ∧
      ∀ j, 1 ≤ j → j ≤ d →
        Filter.Tendsto (fun k => (T : X → X)^[j * n k] x) Filter.atTop (𝓝 x) := by
  sorry

end Dynamics
end LeanEval
