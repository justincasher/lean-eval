import LeanEval.KnotTheory.Prelude
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-- Check types -/
#check ContDiff
#check ContDiff.continuous_deriv
#check (ContDiff.continuous_deriv (𝕜 := ℝ) (n := (⊤ : ℕ∞)))
#check (ContDiff.continuous_deriv (𝕜 := ℝ) (n := (⊤ : ℕ∞)) : ContDiff ℝ (⊤ : ℕ∞) ?_ → ?_)
#check λ (γ : Knot) => γ.smooth