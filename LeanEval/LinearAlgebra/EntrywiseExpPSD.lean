import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import EvalTools.Markers

namespace LeanEval
namespace LinearAlgebra

open scoped MatrixOrder Matrix

/-!
The entrywise exponential of a positive semidefinite matrix is positive semidefinite.

This is a consequence of the Schur product theorem (Schur 1911) and the Taylor expansion
of the exponential function. The key idea is that `exp_⊙(A)_{ij} = exp(a_{ij})` can be
written as the convergent series `∑ₖ (1/k!) A^{⊙k}`, where `A^{⊙k}` denotes the k-fold
Hadamard product. Each `A^{⊙k}` is positive semidefinite by iterated application of the
Schur product theorem, and a convergent nonnegative combination of PSD matrices is PSD.

This result is part of the Schur–Pólya–Loewner theory of entrywise functions preserving
positive semidefiniteness, with applications in statistics (correlation matrices) and
quantum information theory (density matrices).
-/

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}

/-- **All-ones matrix is PSD.** The matrix `J ∈ ℝ^{n × n}` all of whose entries equal `1`
is positive semidefinite, being the outer product `𝟙 𝟙ᵀ` of the all-ones vector with itself. -/
theorem posSemidef_const_one :
    (Matrix.of (fun _ _ => (1 : ℝ)) : Matrix n n ℝ).PosSemidef := by
  sorry

/-- **Entrywise power successor as a Hadamard product.** For every matrix `A` and every `k`,
`A^{⊙(k+1)} = A ⊙ A^{⊙k}`, i.e. `A.map (· ^ (k+1)) = A ⊙ A.map (· ^ k)`. -/
theorem map_pow_succ (A : Matrix n n ℝ) (k : ℕ) :
    A.map (· ^ (k + 1)) = A ⊙ A.map (· ^ k) := by
  sorry

/-- **Entrywise powers are PSD.** If `A` is positive semidefinite, then for every `k` the
entrywise power `A^{⊙k}` (the matrix with entries `(a_{ij})^k`) is positive semidefinite. -/
theorem posSemidef_map_pow (hA : A.PosSemidef) (k : ℕ) :
    (A.map (· ^ k)).PosSemidef := by
  sorry

/-- **Entrywise exponential is Hermitian.** If `A` is positive semidefinite (in particular
Hermitian), then the entrywise exponential `exp_⊙(A)` is Hermitian. -/
theorem isHermitian_map_exp (hA : A.PosSemidef) :
    (A.map Real.exp).IsHermitian := by
  sorry

/-- **Quadratic form of an entrywise map as a double sum.** For any `f : ℝ → ℝ`, matrix `A`,
and vector `x`, the quadratic form `x* (A.map f) x` equals `∑ i ∑ j x_i f(a_{ij}) x_j`. -/
theorem quadForm_map_eq_double_sum (f : ℝ → ℝ) (A : Matrix n n ℝ) (x : n → ℝ) :
    star x ⬝ᵥ ((A.map f) *ᵥ x) = ∑ i, ∑ j, x i * f (A i j) * x j := by
  sorry

/-- **Per-entry summability of the scaled exponential series.** For fixed `i, j` and `x`,
the series `k ↦ x_i ((a_{ij})^k / k!) x_j` is summable over `k ∈ ℕ`. -/
theorem summable_quadForm_entry (A : Matrix n n ℝ) (x : n → ℝ) (i j : n) :
    Summable (fun k : ℕ => x i * (A i j ^ k / (k.factorial : ℝ)) * x j) := by
  sorry

/-- **Per-entry exponential as a tsum.** For fixed `i, j` and `x`,
`x_i exp(a_{ij}) x_j = ∑_{k=0}^∞ x_i ((a_{ij})^k / k!) x_j`. -/
theorem exp_entry_eq_tsum (A : Matrix n n ℝ) (x : n → ℝ) (i j : n) :
    x i * Real.exp (A i j) * x j
      = ∑' k : ℕ, x i * (A i j ^ k / (k.factorial : ℝ)) * x j := by
  sorry

/-- **Interchange of a single finite sum and the tsum.** For a finite index set `s` and a
family `g a : ℕ → ℝ` with each `g a` summable, `∑_{a ∈ s} ∑_k g a k = ∑_k ∑_{a ∈ s} g a k`. -/
theorem finsetSum_tsum_interchange {ι : Type*} (s : Finset ι) (g : ι → ℕ → ℝ)
    (hg : ∀ a ∈ s, Summable (g a)) :
    ∑ a ∈ s, ∑' k : ℕ, g a k = ∑' k : ℕ, ∑ a ∈ s, g a k := by
  sorry

/-- **Interchange of the finite double sum and the tsum.** For `x ∈ ℝ^n`,
`∑ i ∑ j ∑_k x_i ((a_{ij})^k / k!) x_j = ∑_k ∑ i ∑ j x_i ((a_{ij})^k / k!) x_j`. -/
theorem double_sum_tsum_interchange (A : Matrix n n ℝ) (x : n → ℝ) :
    ∑ i, ∑ j, ∑' k : ℕ, x i * (A i j ^ k / (k.factorial : ℝ)) * x j
      = ∑' k : ℕ, ∑ i, ∑ j, x i * (A i j ^ k / (k.factorial : ℝ)) * x j := by
  sorry

/-- **Power term as a scaled power quadratic form.** For every `k` and vector `x`,
`∑ i ∑ j x_i ((a_{ij})^k / k!) x_j = (1 / k!) (x* A^{⊙k} x)`. -/
theorem power_term_eq_quadForm (A : Matrix n n ℝ) (x : n → ℝ) (k : ℕ) :
    ∑ i, ∑ j, x i * (A i j ^ k / (k.factorial : ℝ)) * x j
      = (1 / (k.factorial : ℝ)) * (star x ⬝ᵥ ((A.map (· ^ k)) *ᵥ x)) := by
  sorry

/-- **Quadratic form as a series of power quadratic forms.** For every vector `x`,
`x* exp_⊙(A) x = ∑_{k=0}^∞ (1 / k!) (x* A^{⊙k} x)`, where the series converges. -/
theorem quadForm_map_exp_eq_tsum (A : Matrix n n ℝ) (x : n → ℝ) :
    star x ⬝ᵥ ((A.map Real.exp) *ᵥ x)
      = ∑' k : ℕ, (1 / (k.factorial : ℝ)) * (star x ⬝ᵥ ((A.map (· ^ k)) *ᵥ x)) := by
  sorry

/-- **Entrywise exponential of a PSD matrix is PSD.** If `A ∈ ℝ^{n × n}` is positive
semidefinite, then its entrywise exponential `exp_⊙(A)` (with entries `exp(a_{ij})`) is
positive semidefinite. -/
@[eval_problem]
theorem posSemidef_map_exp (hA : A.PosSemidef) :
    (A.map Real.exp).PosSemidef := by
  sorry

end LinearAlgebra
end LeanEval
