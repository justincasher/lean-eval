import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import LeanEval.Analysis.ODE.DirichletEigenvalues.Helpers
import LeanEval.Analysis.ODE.DirichletEigenvalues.Nonpositive
import LeanEval.Analysis.ODE.DirichletEigenvalues.Positive
import EvalTools.Markers

namespace LeanEval
namespace Analysis
namespace ODE

open scoped Real

/-!
Dirichlet eigenvalues of `-y'' = λ y` on `[0, π]`.

A nontrivial `C²` solution `y` (defined on some open interval `J` containing `[0, π]`)
of `-y''(x) = λ y(x)` with `y 0 = y π = 0` exists **iff** `λ = n²` for some positive
natural number `n`.

We follow the blueprint structure: a short backward direction (the function
`sin(n·x)` realises eigenvalue `n²`), and a forward direction that case-splits on the
sign of `λ`. The case `λ ≤ 0` uses convexity of `y²`; the case `λ > 0` uses an energy
argument to pin down the explicit form `(y'(0)/√λ)·sin(√λ·x) + y(0)·cos(√λ·x)`.

Helper lemmas live in `DirichletEigenvalues/Helpers.lean`,
`DirichletEigenvalues/Nonpositive.lean`, and `DirichletEigenvalues/Positive.lean`.
-/

/-- **Dirichlet eigenvalue characterization.** A real `λ` is a Dirichlet eigenvalue of
`-y'' = λ y` on `[0, π]` (i.e. there is a nontrivial `C²` solution on some open interval
containing `[0, π]`, vanishing at both endpoints) iff `λ = n²` for some positive natural
number `n`. -/
@[eval_problem]
theorem dirichlet_eigenvalues_eq_nat_sq (lam : ℝ) :
    (∃ (y : ℝ → ℝ) (J : Set ℝ),
        IsOpen J ∧ Set.Icc (0 : ℝ) Real.pi ⊆ J ∧
        (∀ x ∈ J, HasDerivAt y (deriv y x) x) ∧
        (∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x) ∧
        y 0 = 0 ∧ y Real.pi = 0 ∧
        ∃ x ∈ Set.Ioo (0 : ℝ) Real.pi, y x ≠ 0) ↔
      ∃ n : ℕ, 0 < n ∧ lam = (n : ℝ) ^ 2 := by
  constructor
  · rintro ⟨y, J, hJ, hsub, hy, hyy, hy0, hypi, hnontriv⟩
    by_cases hle : lam ≤ 0
    · exfalso
      rcases hnontriv with ⟨x₀, hx₀, hx₀_ne⟩
      have hy_zero : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, y x = 0 :=
        no_eigen_nonpos hJ hsub hy hyy hle hy0 hypi
      have hx₀_mem : x₀ ∈ Set.Icc (0 : ℝ) Real.pi := by
        rcases hx₀ with ⟨hx₀_left, hx₀_right⟩
        exact ⟨hx₀_left.le, hx₀_right.le⟩
      exact hx₀_ne (hy_zero x₀ hx₀_mem)
    · have hgt : 0 < lam := by
        by_contra! hle'
        exact hle hle'
      exact pos_eigen_nat_sq hJ hsub hy hyy hy0 hypi hnontriv hgt
  · rintro ⟨n, hn, hlam⟩
    rcases sin_eigenfunction n hn with ⟨hy_deriv_all, hy_second_deriv_all, hy0_all, hypi_all, hnontriv_all⟩
    refine ⟨fun x => Real.sin ((n : ℝ) * x), Set.univ, isOpen_univ, Set.subset_univ _,
      (fun x _ => hy_deriv_all x), (fun x _ => ?_), hy0_all, hypi_all, hnontriv_all⟩
    rw [hlam]
    exact hy_second_deriv_all x

end ODE
end Analysis
end LeanEval
