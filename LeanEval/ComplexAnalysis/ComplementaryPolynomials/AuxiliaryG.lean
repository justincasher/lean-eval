import Mathlib
import EvalTools.Markers
import LeanEval.ComplexAnalysis.ComplementaryPolynomials.ConjugateReciprocal

/-!
The auxiliary polynomial `G = Xⁿ - P · P^{†n}` realising `1 - |P|²` on the circle. Helper file
for `LeanEval.ComplexAnalysis.ComplementaryPolynomials`.
-/

namespace LeanEval
namespace ComplexAnalysis

open Polynomial

/-- The auxiliary polynomial `G = Xⁿ - P · P^{†n}` with `n = deg P`. -/
noncomputable def auxG (P : ℂ[X]) : ℂ[X] :=
  X ^ P.natDegree - P * conjRecip P.natDegree P

/-- `deg G ≤ 2n`. -/
theorem auxG_natDegree_le (P : ℂ[X]) :
    (auxG P).natDegree ≤ 2 * P.natDegree := by
  unfold auxG
  have hX : (X ^ P.natDegree : ℂ[X]).natDegree ≤ 2 * P.natDegree := by
    calc
      (X ^ P.natDegree : ℂ[X]).natDegree = P.natDegree := natDegree_X_pow (P.natDegree)
      _ ≤ P.natDegree + P.natDegree := Nat.le_add_right _ _
      _ = 2 * P.natDegree := by omega
  have hconj : (conjRecip P.natDegree P).natDegree ≤ P.natDegree :=
    conjRecip_natDegree_le P.natDegree P
  have hprod : (P * conjRecip P.natDegree P).natDegree ≤ 2 * P.natDegree := by
    calc
      (P * conjRecip P.natDegree P).natDegree ≤
          P.natDegree + (conjRecip P.natDegree P).natDegree := natDegree_mul_le
      _ ≤ P.natDegree + P.natDegree := Nat.add_le_add_left hconj _
      _ = 2 * P.natDegree := by omega
  calc
    (X ^ P.natDegree - P * conjRecip P.natDegree P).natDegree ≤
        max ((X ^ P.natDegree : ℂ[X]).natDegree) ((P * conjRecip P.natDegree P).natDegree) :=
      natDegree_sub_le _ _
    _ ≤ 2 * P.natDegree :=
      max_le hX hprod

/-- Value of `G` on the circle: `G(z) = zⁿ (1 - |P(z)|²)`. -/
theorem auxG_eval_circle (P : ℂ[X]) {z : ℂ} (hz : ‖z‖ = 1) :
    (auxG P).eval z = z ^ P.natDegree * ((1 - ‖P.eval z‖ ^ 2 : ℝ) : ℂ) := by
  have hdeg : P.natDegree ≤ P.natDegree := le_rfl
  calc
    (auxG P).eval z = ((X ^ P.natDegree - P * conjRecip P.natDegree P).eval z) := rfl
    _ = (X ^ P.natDegree).eval z - (P * conjRecip P.natDegree P).eval z := by
      rw [eval_sub]
    _ = (X ^ P.natDegree).eval z - (P.eval z * (conjRecip P.natDegree P).eval z) := by
      rw [eval_mul]
    _ = z ^ P.natDegree - (P.eval z * (conjRecip P.natDegree P).eval z) := by
      simp [eval_pow, eval_X]
    _ = z ^ P.natDegree - (z ^ P.natDegree * ((‖P.eval z‖ ^ 2 : ℝ) : ℂ)) := by
      rw [conjRecip_mul_eval P.natDegree P hdeg hz]
    _ = z ^ P.natDegree * (1 - ((‖P.eval z‖ ^ 2 : ℝ) : ℂ)) := by
      ring
    _ = z ^ P.natDegree * ((1 - ‖P.eval z‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring

/-- The predicate "`z ↦ z⁻ⁿ · H(z)` is a nonnegative real on the unit circle". -/
def NonnegRealOnCircle (n : ℕ) (H : ℂ[X]) : Prop :=
  ∀ z : ℂ, ‖z‖ = 1 → ∃ r : ℝ, 0 ≤ r ∧ (z ^ n)⁻¹ * H.eval z = (r : ℂ)

/-- If `P` is bounded by `1` on the circle, then `z⁻ⁿ G(z)` is a nonnegative real there. -/
theorem auxG_nonneg_circle (P : ℂ[X]) (hP : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1) :
    NonnegRealOnCircle P.natDegree (auxG P) := by
  intro z hz
  have hz_ne_zero : z ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hz
    norm_num at hz
  have hG := auxG_eval_circle P hz
  have h_pow_ne_zero : z ^ P.natDegree ≠ 0 := pow_ne_zero P.natDegree hz_ne_zero
  have h_sub_nonneg : 0 ≤ (1 : ℝ) - ‖P.eval z‖ ^ 2 := by
    have h_norm_nonneg : 0 ≤ ‖P.eval z‖ := norm_nonneg _
    have h_norm_le_one : ‖P.eval z‖ ≤ 1 := hP z hz
    nlinarith
  have hcalc : (z ^ P.natDegree)⁻¹ * (auxG P).eval z = ((1 - ‖P.eval z‖ ^ 2 : ℝ) : ℂ) := by
    rw [hG]
    field_simp [h_pow_ne_zero]
  refine ⟨(1 : ℝ) - ‖P.eval z‖ ^ 2, h_sub_nonneg, hcalc⟩

/-- Auxiliary lemma: `(Xⁿ)^{†2n} = Xⁿ`. -/
private lemma auxG_self_inversive_aux_conjRecip_X_pow (n : ℕ) : conjRecip (2 * n) (X ^ n) = X ^ n := by
  unfold conjRecip
  rw [show (X ^ n).map (starRingEnd ℂ) = X ^ n by simp]
  rw [reflect_monomial]
  have hn : n ≤ 2 * n := by omega
  rw [revAt_le hn]
  have h_sub : 2 * n - n = n := by
    omega
  rw [h_sub]

/-- `G` is self-inversive: `G^{†2n} = G`. -/
theorem auxG_self_inversive (P : ℂ[X]) :
    conjRecip (2 * P.natDegree) (auxG P) = auxG P := by
  unfold auxG
  rw [conjRecip_sub]
  rw [auxG_self_inversive_aux_conjRecip_X_pow P.natDegree]
  set n := P.natDegree with hn
  have hn_nat : P.natDegree ≤ n := le_rfl
  have hconjdeg : (conjRecip n P).natDegree ≤ n := conjRecip_natDegree_le n P
  have h_mul : conjRecip (2 * n) (P * conjRecip n P) = P * conjRecip n P := by
    calc
      conjRecip (2 * n) (P * conjRecip n P)
          = conjRecip (n + n) (P * conjRecip n P) := by rw [show (2 : ℕ) * n = n + n by omega]
      _ = conjRecip n P * conjRecip n (conjRecip n P) := by
        rw [conjRecip_mul n n P (conjRecip n P) hn_nat hconjdeg]
      _ = conjRecip n P * P := by rw [conjRecip_conjRecip n P hn_nat]
      _ = P * conjRecip n P := mul_comm _ _
  rw [h_mul]

end ComplexAnalysis
end LeanEval
