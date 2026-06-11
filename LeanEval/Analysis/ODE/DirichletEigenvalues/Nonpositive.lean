import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace LeanEval
namespace Analysis
namespace ODE

open scoped Real

/-! ## Forward direction, case `λ ≤ 0`: convexity of `y²` -/

/-- First derivative of `y²`: the function `t ↦ y t * y t` has derivative `2 y(x) y'(x)`
at every `x ∈ J`. -/
lemma y_sq_first_deriv {y : ℝ → ℝ} {J : Set ℝ}
    (hy : ∀ x ∈ J, HasDerivAt y (deriv y x) x) {x : ℝ} (hx : x ∈ J) :
    HasDerivAt (fun t => y t * y t) (2 * y x * deriv y x) x := by
  have h := hy x hx
  have prod := h.mul h
  convert prod using 1
  ring

/-- Second derivative formula for `y²`: with `h(t) = 2 y(t) y'(t)`, the function `h` has
derivative `2 y'(x)² - 2 λ y(x)²` at each `x ∈ J`. -/
lemma y_sq_second_deriv_formula {y : ℝ → ℝ} {J : Set ℝ} {lam : ℝ}
    (hy : ∀ x ∈ J, HasDerivAt y (deriv y x) x)
    (hyy : ∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x)
    {x : ℝ} (hx : x ∈ J) :
    HasDerivAt (fun t => 2 * y t * deriv y t)
      (2 * deriv y x ^ 2 - 2 * lam * y x ^ 2) x := by
  sorry

/-- Second derivative of `y²` is nonnegative when `λ ≤ 0`. -/
lemma y_sq_second_deriv_nonneg {y : ℝ → ℝ} {J : Set ℝ} {lam : ℝ}
    (hy : ∀ x ∈ J, HasDerivAt y (deriv y x) x)
    (hyy : ∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x)
    (hlam : lam ≤ 0) {x : ℝ} (hx : x ∈ J) :
    0 ≤ deriv (fun t => 2 * y t * deriv y t) x := by
  sorry

/-- `y²` is differentiable on `J`, with `deriv (y²) x = 2 y(x) y'(x)`. -/
lemma y_sq_differentiableOn_J {y : ℝ → ℝ} {J : Set ℝ}
    (hy : ∀ x ∈ J, HasDerivAt y (deriv y x) x) :
    DifferentiableOn ℝ (fun x => y x * y x) J ∧
      ∀ x ∈ J, deriv (fun t => y t * y t) x = 2 * y x * deriv y x := by
  sorry

/-- `deriv (y²)` is differentiable on `J`. -/
lemma y_sq_deriv_differentiableOn_J {y : ℝ → ℝ} {J : Set ℝ} {lam : ℝ}
    (hJ : IsOpen J)
    (hy : ∀ x ∈ J, HasDerivAt y (deriv y x) x)
    (hyy : ∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x) :
    DifferentiableOn ℝ (deriv (fun x => y x * y x)) J := by
  sorry

/-- `y²` is convex on `[0, π]` when `λ ≤ 0`. -/
lemma y_sq_convex {y : ℝ → ℝ} {J : Set ℝ} {lam : ℝ}
    (hJ : IsOpen J) (hsub : Set.Icc (0 : ℝ) Real.pi ⊆ J)
    (hy : ∀ x ∈ J, HasDerivAt y (deriv y x) x)
    (hyy : ∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x)
    (hlam : lam ≤ 0) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) Real.pi) (fun x => y x * y x) := by
  sorry

/-- If `λ ≤ 0` and the boundary conditions `y 0 = y π = 0` hold, then `y ≡ 0` on `[0, π]`. -/
lemma no_eigen_nonpos {y : ℝ → ℝ} {J : Set ℝ} {lam : ℝ}
    (hJ : IsOpen J) (hsub : Set.Icc (0 : ℝ) Real.pi ⊆ J)
    (hy : ∀ x ∈ J, HasDerivAt y (deriv y x) x)
    (hyy : ∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x)
    (hlam : lam ≤ 0) (hy0 : y 0 = 0) (hypi : y Real.pi = 0) :
    ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, y x = 0 := by
  sorry

end ODE
end Analysis
end LeanEval
