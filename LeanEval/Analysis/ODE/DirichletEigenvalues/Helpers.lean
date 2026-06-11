import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace LeanEval
namespace Analysis
namespace ODE

open scoped Real

/-! ## Preliminaries: derivatives of `sin(s·x)`, `cos(s·x)`, and their combinations -/

/-- Derivative of `t ↦ sin (s * t)` at `x` is `s * cos (s * x)`. -/
lemma sin_smul_hasDerivAt (s x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.sin (s * t)) (s * Real.cos (s * x)) x := by
  sorry

/-- Derivative of `t ↦ cos (s * t)` at `x` is `-(s * sin (s * x))`. -/
lemma cos_smul_hasDerivAt (s x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.cos (s * t)) (-(s * Real.sin (s * x))) x := by
  sorry

/-- First derivative of `t ↦ A * sin (s * t) + B * cos (s * t)`. -/
lemma sin_cos_combo_first_deriv (A B s x : ℝ) :
    HasDerivAt (fun t : ℝ => A * Real.sin (s * t) + B * Real.cos (s * t))
      (A * s * Real.cos (s * x) - B * s * Real.sin (s * x)) x := by
  have hsin := sin_smul_hasDerivAt s x
  have hcos := cos_smul_hasDerivAt s x
  have hA : HasDerivAt (fun t : ℝ => A * Real.sin (s * t)) (A * (s * Real.cos (s * x))) x :=
    hsin.const_mul A
  have hB : HasDerivAt (fun t : ℝ => B * Real.cos (s * t)) (B * (-(s * Real.sin (s * x)))) x :=
    hcos.const_mul B
  have hsum : HasDerivAt (fun t : ℝ => A * Real.sin (s * t) + B * Real.cos (s * t))
      (A * (s * Real.cos (s * x)) + B * (-(s * Real.sin (s * x)))) x :=
    hA.add hB
  simpa [mul_assoc, mul_comm, mul_left_comm, sub_eq_add_neg] using hsum

/-- Second derivative formula: the function `t ↦ A s cos (s t) - B s sin (s t)`, which is
the first derivative of `t ↦ A sin (s t) + B cos (s t)`, has at every `x` the value
`deriv _ x = -s² (A sin (s x) + B cos (s x))`. -/
lemma sin_cos_combo_second_deriv (A B s x : ℝ) :
    deriv (fun t : ℝ => A * s * Real.cos (s * t) - B * s * Real.sin (s * t)) x
      = -s ^ 2 * (A * Real.sin (s * x) + B * Real.cos (s * x)) := by
  sorry

/-- Initial values of `g(x) = A sin(s·x) + B cos(s·x)`: `g 0 = B` and `deriv g 0 = A s`. -/
lemma sin_cos_combo_initial_values (A B s : ℝ) :
    let g : ℝ → ℝ := fun t => A * Real.sin (s * t) + B * Real.cos (s * t)
    g 0 = B ∧ deriv g 0 = A * s := by
  intro g
  have h0 : g 0 = B := by
    dsimp [g]
    simp [Real.sin_zero, Real.cos_zero]
  have hderiv : deriv g 0 = A * s := by
    have h := sin_cos_combo_first_deriv A B s 0
    have hderiv_eq : deriv g 0 = A * s * Real.cos (s * 0) - B * s * Real.sin (s * 0) := by
      simpa [g] using h.deriv
    simpa [Real.sin_zero, Real.cos_zero, mul_zero, mul_one] using hderiv_eq
  exact And.intro h0 hderiv

/-- `g(x) = A sin(s·x) + B cos(s·x)` solves the harmonic oscillator on `ℝ`:
its first derivative is `A s cos(s·x) - B s sin(s·x)`, its second derivative is
`-s² g(x)`, and the initial data are `g 0 = B`, `deriv g 0 = A s`. -/
lemma sin_cos_combo_solves_ode (A B s : ℝ) :
    let g : ℝ → ℝ := fun t => A * Real.sin (s * t) + B * Real.cos (s * t)
    (∀ x : ℝ, HasDerivAt g (deriv g x) x) ∧
      (∀ x : ℝ, deriv g x = A * s * Real.cos (s * x) - B * s * Real.sin (s * x)) ∧
      (∀ x : ℝ, HasDerivAt (deriv g) (-s ^ 2 * g x) x) ∧
      (∀ x : ℝ, deriv (deriv g) x = -s ^ 2 * g x) ∧
      g 0 = B ∧ deriv g 0 = A * s := by
  sorry

/-! ## Backward direction: `sin(n·x)` is an eigenfunction -/

/-- For each positive natural `n`, there is `x₀ ∈ (0, π)` with `sin (n · x₀) ≠ 0`. -/
lemma sin_nx_nontrivial_witness (n : ℕ) (hn : 0 < n) :
    ∃ x₀ ∈ Set.Ioo (0 : ℝ) Real.pi, Real.sin ((n : ℝ) * x₀) ≠ 0 := by
  sorry

/-- For each positive natural `n`, the function `y(x) = sin(n·x)` realises the
Dirichlet eigenvalue `n²` on `J = ℝ`. -/
lemma sin_eigenfunction (n : ℕ) (hn : 0 < n) :
    let y : ℝ → ℝ := fun x => Real.sin ((n : ℝ) * x)
    (∀ x : ℝ, HasDerivAt y (deriv y x) x) ∧
      (∀ x : ℝ, HasDerivAt (deriv y) (-((n : ℝ) ^ 2 * y x)) x) ∧
      y 0 = 0 ∧ y Real.pi = 0 ∧
      ∃ x₀ ∈ Set.Ioo (0 : ℝ) Real.pi, y x₀ ≠ 0 := by
  sorry

end ODE
end Analysis
end LeanEval
