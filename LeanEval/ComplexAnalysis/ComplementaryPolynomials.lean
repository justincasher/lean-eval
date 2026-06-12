import Mathlib
import EvalTools.Markers
import LeanEval.ComplexAnalysis.ComplementaryPolynomials.ConjugateReciprocal
import LeanEval.ComplexAnalysis.ComplementaryPolynomials.AuxiliaryG
import LeanEval.ComplexAnalysis.ComplementaryPolynomials.RootMultiplicity
import LeanEval.ComplexAnalysis.ComplementaryPolynomials.CircleRoots
import LeanEval.ComplexAnalysis.ComplementaryPolynomials.Factorization

namespace LeanEval
namespace ComplexAnalysis

open Polynomial

/-!
Complementary polynomials on the unit circle.

This is the basic existence statement appearing in quantum signal processing: if a complex
polynomial has sup norm at most `1` on the unit circle, then it admits a complementary polynomial
whose squared moduli add up to `1` on the circle.

The previous statement asked for `Q.natDegree = P.natDegree` (strict equality), which fails on
the boundary case `P = X`: there `|P(z)| = 1` on the entire unit circle, so any complementary `Q`
must vanish on the circle and hence be the zero polynomial; but `natDegree 0 = 0 ≠ 1 = natDegree X`.
We relax the constraint to `≤`, which is what Fejér-Riesz / spectral factorization actually
delivers (the degree of `Q` is at most that of `P`, with equality generically).

The development follows a spectral-factorization (Fejér–Riesz) blueprint, split across helper
files in `ComplementaryPolynomials/`:
* `ConjugateReciprocal.lean` — the conjugate-reciprocal polynomial `conjRecip N A`.
* `AuxiliaryG.lean` — the auxiliary polynomial `auxG P = X^n - P · P^{†n}` realising `1 - |P|²`.
* `RootMultiplicity.lean` — root-multiplicity transport under conjugation and reflection.
* `CircleRoots.lean` — circle roots of a circle-nonnegative polynomial have even multiplicity.
* `Factorization.lean` — the Fejér–Riesz factorization of a self-inversive polynomial.
-/

/-- The degenerate case `G = 0`: `P` has modulus `1` on the circle and `Q = 0` works. -/
theorem main_G_zero (P : ℂ[X]) (hG : auxG P = 0) :
    (∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ = 1) ∧
      ∃ Q : ℂ[X], Q.natDegree ≤ P.natDegree ∧
        ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ^ 2 + ‖Q.eval z‖ ^ 2 = 1 := by
  have h_norm_one : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ = 1 := by
    intro z hz
    have hG_eval : (auxG P).eval z = 0 := by
      rw [hG, eval_zero]
    have haux := auxG_eval_circle P hz
    rw [hG_eval] at haux
    have hz_ne_zero : z ≠ 0 := by
      intro hzero
      rw [hzero, norm_zero] at hz
      norm_num at hz
    have h_pow_ne_zero : z ^ P.natDegree ≠ 0 := pow_ne_zero P.natDegree hz_ne_zero
    have h_mul_zero : z ^ P.natDegree * ((1 - ‖P.eval z‖ ^ 2 : ℝ) : ℂ) = 0 := by
      exact haux.symm
    rcases mul_eq_zero.mp h_mul_zero with (h | h)
    · exact (h_pow_ne_zero h).elim
    · have h_real : (1 - ‖P.eval z‖ ^ 2 : ℝ) = 0 := by exact_mod_cast h
      have h_norm_sq_eq_one : ‖P.eval z‖ ^ 2 = 1 := by linarith
      have h_norm_nonneg : 0 ≤ ‖P.eval z‖ := norm_nonneg _
      nlinarith
  refine ⟨h_norm_one, ?_⟩
  refine ⟨0, ?_, ?_⟩
  · simp
  · intro z hz
    have h_norm_eq_one := h_norm_one z hz
    simp [h_norm_eq_one]

/-- From a factorization `Q · Q^{†n} = G` to the norm identity on the circle. -/
theorem factorization_to_norm (P Q : ℂ[X]) (hQ : Q.natDegree ≤ P.natDegree)
    (hfact : Q * conjRecip P.natDegree Q = auxG P) :
    ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ^ 2 + ‖Q.eval z‖ ^ 2 = 1 := by
  intro z hz
  have hz_ne_zero : z ≠ 0 := by
    intro hzero
    have : ‖z‖ = 0 := by simp [hzero]
    rw [hz] at this
    norm_num at this
  set n := P.natDegree with hn
  have h_pownz_ne_zero : z ^ n ≠ 0 := pow_ne_zero n hz_ne_zero
  -- Evaluate the factorization equality at z
  have h_eval_fact : (Q * conjRecip n Q).eval z = (auxG P).eval z := by
    rw [hfact]
  have h_eval_mul : (Q * conjRecip n Q).eval z = Q.eval z * (conjRecip n Q).eval z := by
    rw [eval_mul]
  rw [h_eval_mul] at h_eval_fact
  -- conjRecip_mul_eval: Q.eval z * (conjRecip n Q).eval z = z ^ n * ((‖Q.eval z‖ ^ 2 : ℝ) : ℂ)
  have h_conjRecip_eq : Q.eval z * (conjRecip n Q).eval z = z ^ n * ((‖Q.eval z‖ ^ 2 : ℝ) : ℂ) :=
    conjRecip_mul_eval n Q hQ hz
  rw [h_conjRecip_eq] at h_eval_fact
  -- auxG_eval_circle: (auxG P).eval z = z ^ n * ((1 - ‖P.eval z‖ ^ 2 : ℝ) : ℂ)
  have h_auxG_eq : (auxG P).eval z = z ^ n * ((1 - ‖P.eval z‖ ^ 2 : ℝ) : ℂ) :=
    auxG_eval_circle P hz
  rw [h_auxG_eq] at h_eval_fact
  -- Now we have: z^n * ((‖Q.eval z‖² : ℝ) : ℂ) = z^n * ((1 - ‖P.eval z‖² : ℝ) : ℂ)
  -- Cancel z ^ n
  have h_mul_cancel : ((‖Q.eval z‖ ^ 2 : ℝ) : ℂ) = ((1 - ‖P.eval z‖ ^ 2 : ℝ) : ℂ) := by
    apply mul_left_cancel₀ h_pownz_ne_zero
    exact h_eval_fact
  -- Since (↑) : ℝ → ℂ is injective
  have h_real_eq : ‖Q.eval z‖ ^ 2 = (1 : ℝ) - ‖P.eval z‖ ^ 2 := by
    exact_mod_cast h_mul_cancel
  -- Rearrange
  calc
    ‖P.eval z‖ ^ 2 + ‖Q.eval z‖ ^ 2 = ‖P.eval z‖ ^ 2 + ((1 : ℝ) - ‖P.eval z‖ ^ 2) := by rw [h_real_eq]
    _ = 1 := by ring

/-- If `P` is bounded by `1` on the unit circle, then there is a polynomial `Q` of degree at most
that of `P` whose squared moduli complement `P` to `1` on the unit circle. -/
@[eval_problem]
theorem exists_complementary_polynomial_on_unit_circle
    (P : ℂ[X])
    (hP : ∀ z : Circle, ‖P.eval (z : ℂ)‖ ≤ 1) :
    ∃ Q : ℂ[X],
      Q.natDegree ≤ P.natDegree ∧
        ∀ z : Circle, ‖P.eval (z : ℂ)‖ ^ 2 + ‖Q.eval (z : ℂ)‖ ^ 2 = 1 := by
  -- Convert hP from Circle to ℂ
  have hP' : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1 := by
    intro z hz
    have hz_mem : z ∈ Metric.sphere (0 : ℂ) 1 := by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
      exact hz
    exact hP ⟨z, hz_mem⟩
  set G := auxG P with hG_def
  by_cases hGzero : G = 0
  · -- Case G = 0: use main_G_zero
    rcases main_G_zero P hGzero with ⟨h_norm_one, Q, hQdeg, h_circle⟩
    refine ⟨Q, hQdeg, ?_⟩
    intro z
    have hz_norm : ‖(z : ℂ)‖ = 1 := Circle.norm_coe z
    exact h_circle (z : ℂ) hz_norm
  · -- Case G ≠ 0: apply Fejér–Riesz factorization
    have hdeg : G.natDegree ≤ 2 * P.natDegree := auxG_natDegree_le P
    have hself : conjRecip (2 * P.natDegree) G = G := auxG_self_inversive P
    have hpos : NonnegRealOnCircle P.natDegree G := auxG_nonneg_circle P hP'
    rcases fejer_riesz P.natDegree G hGzero hdeg hself hpos with ⟨Q, hQdeg, hfact⟩
    have h_circle_norm : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ^ 2 + ‖Q.eval z‖ ^ 2 = 1 :=
      factorization_to_norm P Q hQdeg hfact
    refine ⟨Q, hQdeg, ?_⟩
    intro z
    have hz_norm : ‖(z : ℂ)‖ = 1 := Circle.norm_coe z
    exact h_circle_norm (z : ℂ) hz_norm

end ComplexAnalysis
end LeanEval
