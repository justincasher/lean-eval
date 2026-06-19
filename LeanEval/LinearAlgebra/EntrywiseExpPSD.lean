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
  have h_vec : (Matrix.of (fun _ _ => (1 : ℝ)) : Matrix n n ℝ) = Matrix.vecMulVec (fun _ : n => (1 : ℝ)) (fun _ : n => (1 : ℝ)) := by
    ext i j
    simp [Matrix.vecMulVec_apply]
  rw [h_vec]
  exact Matrix.posSemidef_vecMulVec_self_star (fun _ : n => (1 : ℝ))

/-- **Entrywise power successor as a Hadamard product.** For every matrix `A` and every `k`,
`A^{⊙(k+1)} = A ⊙ A^{⊙k}`, i.e. `A.map (· ^ (k+1)) = A ⊙ A.map (· ^ k)`. -/
theorem map_pow_succ (A : Matrix n n ℝ) (k : ℕ) :
    A.map (· ^ (k + 1)) = A ⊙ A.map (· ^ k) := by
  ext i j
  simp [Matrix.hadamard, pow_succ, mul_comm]

/-- **Entrywise powers are PSD.** If `A` is positive semidefinite, then for every `k` the
entrywise power `A^{⊙k}` (the matrix with entries `(a_{ij})^k`) is positive semidefinite. -/
theorem posSemidef_map_pow (hA : A.PosSemidef) (k : ℕ) :
    (A.map (· ^ k)).PosSemidef := by
  induction k with
  | zero =>
    have h0 : A.map (· ^ 0) = Matrix.of (fun _ _ => (1 : ℝ)) := by
      ext i j; simp
    rw [h0]
    exact posSemidef_const_one
  | succ k ih =>
    rw [map_pow_succ A k]
    exact hA.hadamard ih

/-- **Entrywise exponential is Hermitian.** If `A` is positive semidefinite (in particular
Hermitian), then the entrywise exponential `exp_⊙(A)` is Hermitian. -/
theorem isHermitian_map_exp (hA : A.PosSemidef) :
    (A.map Real.exp).IsHermitian := by
  have hA_herm : A.IsHermitian := hA.1
  have h_semiconj : Function.Semiconj Real.exp star star := by
    intro x
    simp
  exact hA_herm.map Real.exp h_semiconj

/-- **Quadratic form of an entrywise map as a double sum.** For any `f : ℝ → ℝ`, matrix `A`,
and vector `x`, the quadratic form `x* (A.map f) x` equals `∑ i ∑ j x_i f(a_{ij}) x_j`. -/
theorem quadForm_map_eq_double_sum (f : ℝ → ℝ) (A : Matrix n n ℝ) (x : n → ℝ) :
    star x ⬝ᵥ ((A.map f) *ᵥ x) = ∑ i, ∑ j, x i * f (A i j) * x j := by
  simp [dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, mul_assoc, star_trivial]

/-- **Per-entry summability of the scaled exponential series.** For fixed `i, j` and `x`,
the series `k ↦ x_i ((a_{ij})^k / k!) x_j` is summable over `k ∈ ℕ`. -/
theorem summable_quadForm_entry (A : Matrix n n ℝ) (x : n → ℝ) (i j : n) :
    Summable (fun k : ℕ => x i * (A i j ^ k / (k.factorial : ℝ)) * x j) := by
  have h := Real.summable_pow_div_factorial (A i j)
  exact h.mul_left (x i) |>.mul_right (x j)

/-- **Per-entry exponential as a tsum.** For fixed `i, j` and `x`,
`x_i exp(a_{ij}) x_j = ∑_{k=0}^∞ x_i ((a_{ij})^k / k!) x_j`. -/
theorem exp_entry_eq_tsum (A : Matrix n n ℝ) (x : n → ℝ) (i j : n) :
    x i * Real.exp (A i j) * x j
      = ∑' k : ℕ, x i * (A i j ^ k / (k.factorial : ℝ)) * x j := by
  calc
    x i * Real.exp (A i j) * x j
        = x i * (∑' k : ℕ, (A i j) ^ k / (k.factorial : ℝ)) * x j := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    _ = (x i * ∑' k : ℕ, ((A i j) ^ k / (k.factorial : ℝ))) * x j := by ring
    _ = (∑' k : ℕ, x i * ((A i j) ^ k / (k.factorial : ℝ))) * x j := by rw [tsum_mul_left]
    _ = ∑' k : ℕ, (x i * ((A i j) ^ k / (k.factorial : ℝ))) * x j := by rw [tsum_mul_right]
    _ = ∑' k : ℕ, x i * ((A i j) ^ k / (k.factorial : ℝ)) * x j := by ring

/-- **Interchange of a single finite sum and the tsum.** For a finite index set `s` and a
family `g a : ℕ → ℝ` with each `g a` summable, `∑_{a ∈ s} ∑_k g a k = ∑_k ∑_{a ∈ s} g a k`. -/
theorem finsetSum_tsum_interchange {ι : Type*} (s : Finset ι) (g : ι → ℕ → ℝ)
    (hg : ∀ a ∈ s, Summable (g a)) :
    ∑ a ∈ s, ∑' k : ℕ, g a k = ∑' k : ℕ, ∑ a ∈ s, g a k :=
  (Summable.tsum_finsetSum hg).symm

/-- **Interchange of the finite double sum and the tsum.** For `x ∈ ℝ^n`,
`∑ i ∑ j ∑_k x_i ((a_{ij})^k / k!) x_j = ∑_k ∑ i ∑ j x_i ((a_{ij})^k / k!) x_j`. -/
theorem double_sum_tsum_interchange (A : Matrix n n ℝ) (x : n → ℝ) :
    ∑ i, ∑ j, ∑' k : ℕ, x i * (A i j ^ k / (k.factorial : ℝ)) * x j
      = ∑' k : ℕ, ∑ i, ∑ j, x i * (A i j ^ k / (k.factorial : ℝ)) * x j := by
  -- For each i, interchange the j-sum with the k-tsum using finsetSum_tsum_interchange
  have h_j_interchange : ∀ i, ∑ j : n, ∑' k : ℕ, x i * (A i j ^ k / (k.factorial : ℝ)) * x j
      = ∑' k : ℕ, ∑ j : n, x i * (A i j ^ k / (k.factorial : ℝ)) * x j := by
    intro i
    apply finsetSum_tsum_interchange (Finset.univ : Finset n) (fun j k => x i * (A i j ^ k / (k.factorial : ℝ)) * x j)
    intro j hj
    exact summable_quadForm_entry A x i j
  -- For each i, the series over k of the j-sum is summable (finite sum of summable series)
  have h_summable_i : ∀ i, Summable (fun k : ℕ => ∑ j : n, x i * (A i j ^ k / (k.factorial : ℝ)) * x j) := by
    intro i
    have hji : ∀ j, Summable (fun k : ℕ => x i * (A i j ^ k / (k.factorial : ℝ)) * x j) :=
      fun j => summable_quadForm_entry A x i j
    exact summable_sum (fun j _ => hji j)
  calc
    ∑ i : n, ∑ j : n, ∑' k : ℕ, x i * (A i j ^ k / (k.factorial : ℝ)) * x j
        = ∑ i : n, (∑' k : ℕ, ∑ j : n, x i * (A i j ^ k / (k.factorial : ℝ)) * x j) := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [h_j_interchange i]
    _ = ∑' k : ℕ, ∑ i : n, ∑ j : n, x i * (A i j ^ k / (k.factorial : ℝ)) * x j := by
      calc
        ∑ i : n, (∑' k : ℕ, ∑ j : n, x i * (A i j ^ k / (k.factorial : ℝ)) * x j)
            = ∑ i ∈ (Finset.univ : Finset n), ∑' k : ℕ, (∑ j : n, x i * (A i j ^ k / (k.factorial : ℝ)) * x j) := rfl
        _ = ∑' k : ℕ, ∑ i ∈ (Finset.univ : Finset n), (∑ j : n, x i * (A i j ^ k / (k.factorial : ℝ)) * x j) :=
          finsetSum_tsum_interchange (Finset.univ : Finset n) (fun i k => ∑ j : n, x i * (A i j ^ k / (k.factorial : ℝ)) * x j) (by
            intro i hi
            exact h_summable_i i)
        _ = ∑' k : ℕ, ∑ i : n, ∑ j : n, x i * (A i j ^ k / (k.factorial : ℝ)) * x j := rfl

/-- **Power term as a scaled power quadratic form.** For every `k` and vector `x`,
`∑ i ∑ j x_i ((a_{ij})^k / k!) x_j = (1 / k!) (x* A^{⊙k} x)`. -/
theorem power_term_eq_quadForm (A : Matrix n n ℝ) (x : n → ℝ) (k : ℕ) :
    ∑ i, ∑ j, x i * (A i j ^ k / (k.factorial : ℝ)) * x j
      = (1 / (k.factorial : ℝ)) * (star x ⬝ᵥ ((A.map (· ^ k)) *ᵥ x)) := by
  calc
    ∑ i, ∑ j, x i * (A i j ^ k / (k.factorial : ℝ)) * x j
        = ∑ i, ∑ j, (1 / (k.factorial : ℝ)) * (x i * (A i j ^ k) * x j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
    _ = ∑ i, (1 / (k.factorial : ℝ)) * (∑ j, x i * (A i j ^ k) * x j) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
    _ = (1 / (k.factorial : ℝ)) * (∑ i, ∑ j, x i * (A i j ^ k) * x j) := by
      rw [Finset.mul_sum]
    _ = (1 / (k.factorial : ℝ)) * (star x ⬝ᵥ ((A.map (· ^ k)) *ᵥ x)) := by
      rw [quadForm_map_eq_double_sum (· ^ k) A x]

/-- **Quadratic form as a series of power quadratic forms.** For every vector `x`,
`x* exp_⊙(A) x = ∑_{k=0}^∞ (1 / k!) (x* A^{⊙k} x)`, where the series converges. -/
theorem quadForm_map_exp_eq_tsum (A : Matrix n n ℝ) (x : n → ℝ) :
    star x ⬝ᵥ ((A.map Real.exp) *ᵥ x)
      = ∑' k : ℕ, (1 / (k.factorial : ℝ)) * (star x ⬝ᵥ ((A.map (· ^ k)) *ᵥ x)) := by
  calc
    star x ⬝ᵥ ((A.map Real.exp) *ᵥ x) = ∑ i, ∑ j, x i * Real.exp (A i j) * x j := by
      rw [quadForm_map_eq_double_sum Real.exp A x]
    _ = ∑ i, ∑ j, ∑' k : ℕ, x i * (A i j ^ k / (k.factorial : ℝ)) * x j := by
      simp_rw [exp_entry_eq_tsum A x]
    _ = ∑' k : ℕ, ∑ i, ∑ j, x i * (A i j ^ k / (k.factorial : ℝ)) * x j := by
      rw [double_sum_tsum_interchange A x]
    _ = ∑' k : ℕ, (1 / (k.factorial : ℝ)) * (star x ⬝ᵥ ((A.map (· ^ k)) *ᵥ x)) := by
      refine tsum_congr (fun k => ?_)
      rw [power_term_eq_quadForm A x k]

/-- **Entrywise exponential of a PSD matrix is PSD.** If `A ∈ ℝ^{n × n}` is positive
semidefinite, then its entrywise exponential `exp_⊙(A)` (with entries `exp(a_{ij})`) is
positive semidefinite. -/
@[eval_problem]
theorem posSemidef_map_exp (hA : A.PosSemidef) :
    (A.map Real.exp).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (isHermitian_map_exp hA) ?_
  intro x
  rw [quadForm_map_exp_eq_tsum A x]
  refine tsum_nonneg (fun k => ?_)
  have hk_nonneg : 0 ≤ (1 / (k.factorial : ℝ)) :=
    div_nonneg (by norm_num) (by exact mod_cast Nat.zero_le _)
  have hpow : (A.map (· ^ k)).PosSemidef := posSemidef_map_pow hA k
  have hxpow : 0 ≤ star x ⬝ᵥ ((A.map (· ^ k)) *ᵥ x) :=
    hpow.dotProduct_mulVec_nonneg x
  exact mul_nonneg hk_nonneg hxpow

end LinearAlgebra
end LeanEval
