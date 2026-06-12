import Mathlib
import EvalTools.Markers

/-!
The conjugate-reciprocal polynomial `conjRecip N A`. Helper file for
`LeanEval.ComplexAnalysis.ComplementaryPolynomials`.
-/

namespace LeanEval
namespace ComplexAnalysis

open Polynomial

/-- The **conjugate-reciprocal** `A^{†N}`: conjugate the coefficients of `A` and reflect them
within degree `N`. Informally `A^{†N}(z) = zᴺ · conj(A)(1/z)`. -/
noncomputable def conjRecip (N : ℕ) (A : ℂ[X]) : ℂ[X] :=
  reflect N (A.map (starRingEnd ℂ))

/-- Evaluation of a polynomial with conjugated coefficients. -/
theorem map_conj_eval (A : ℂ[X]) (w : ℂ) :
    (A.map (starRingEnd ℂ)).eval w = starRingEnd ℂ (A.eval (starRingEnd ℂ w)) := by
  rw [Polynomial.eval_map]
  have h := Polynomial.hom_eval₂ (starRingEnd ℂ w) (g := starRingEnd ℂ) (f := RingHom.id ℂ) (p := A)
  -- h : starRingEnd ℂ (A.eval₂ (RingHom.id ℂ) (starRingEnd ℂ w)) = A.eval₂ ((starRingEnd ℂ).comp (RingHom.id ℂ)) (starRingEnd ℂ (starRingEnd ℂ w))
  -- The RHS: (starRingEnd ℂ).comp (RingHom.id ℂ) = starRingEnd ℂ by RingHom.comp_id
  -- and starRingEnd ℂ (starRingEnd ℂ w) = w by starRingEnd_apply and star_star
  rw [RingHom.comp_id, show (starRingEnd ℂ) ((starRingEnd ℂ) w) = w from by simp] at h
  -- h : starRingEnd ℂ (A.eval₂ (RingHom.id ℂ) (starRingEnd ℂ w)) = A.eval₂ (starRingEnd ℂ) w
  -- Goal: A.eval₂ (starRingEnd ℂ) w = starRingEnd ℂ (A.eval (starRingEnd ℂ w))
  -- From h.symm: A.eval₂ (starRingEnd ℂ) w = starRingEnd ℂ (A.eval₂ (RingHom.id ℂ) (starRingEnd ℂ w))
  -- Since A.eval₂ (RingHom.id ℂ) (starRingEnd ℂ w) = A.eval (starRingEnd ℂ w), we're done
  rw [← h, show A.eval₂ (RingHom.id ℂ) (starRingEnd ℂ w) = A.eval (starRingEnd ℂ w) from rfl]

/-- The conjugate-reciprocal has degree at most `N`, provided `N ≥ deg A`. -/
theorem conjRecip_natDegree_le (N : ℕ) (A : ℂ[X]) (hA : A.natDegree ≤ N) :
    (conjRecip N A).natDegree ≤ N := by
  unfold conjRecip
  have hmap : (A.map (starRingEnd ℂ)).natDegree = A.natDegree :=
    natDegree_map_eq_of_injective (starRingEnd ℂ).injective A
  calc (reflect N (A.map (starRingEnd ℂ))).natDegree
      ≤ max N (A.map (starRingEnd ℂ)).natDegree := natDegree_reflect_le
    _ = max N A.natDegree := by rw [hmap]
    _ = N := max_eq_left hA

/-- Reflection-evaluation identity: `(reflect N A)(z) = zᴺ A(z⁻¹)` for `z ≠ 0`. -/
theorem reflect_eval (N : ℕ) (A : ℂ[X]) (hA : A.natDegree ≤ N) {z : ℂ} (hz : z ≠ 0) :
    (reflect N A).eval z = z ^ N * A.eval z⁻¹ := by
  have hz_unit : IsUnit z := isUnit_iff_ne_zero.mpr hz
  haveI : Invertible z := hz_unit.invertible
  haveI : Invertible (z⁻¹ : ℂ) := inferInstance
  have h := Polynomial.eval₂_reflect_mul_pow (RingHom.id ℂ) (z⁻¹ : ℂ) (N := N) (f := A) (hf := hA)
  have h_simp : ⅟(z⁻¹ : ℂ) = z :=
    invOf_eq_right_inv (by simp [inv_mul_cancel₀ hz])
  rw [h_simp] at h
  rw [eval₂_id, eval₂_id] at h
  -- h : (reflect N A).eval z * (z⁻¹) ^ N = A.eval (z⁻¹)
  have hp : (z⁻¹ : ℂ) ^ N * z ^ N = 1 := by
    calc
      (z⁻¹ : ℂ) ^ N * z ^ N = ((z⁻¹ : ℂ) * z) ^ N := (mul_pow (z⁻¹ : ℂ) z N).symm
      _ = 1 ^ N := by simp [inv_mul_cancel₀ hz]
      _ = 1 := by simp
  calc
    (reflect N A).eval z = (reflect N A).eval z * 1 := by simp
    _ = (reflect N A).eval z * ((z⁻¹ : ℂ) ^ N * z ^ N) := by rw [hp]
    _ = ((reflect N A).eval z * (z⁻¹) ^ N) * z ^ N := by ring
    _ = A.eval (z⁻¹) * z ^ N := by rw [h]
    _ = z ^ N * A.eval (z⁻¹) := by ring

/-- Evaluation of the conjugate-reciprocal on the unit circle: `A^{†N}(z) = zᴺ · conj(A(z))`. -/
theorem conjRecip_eval (N : ℕ) (A : ℂ[X]) (hA : A.natDegree ≤ N) {z : ℂ} (hz : ‖z‖ = 1) :
    (conjRecip N A).eval z = z ^ N * starRingEnd ℂ (A.eval z) := by
  have hz_ne_zero : z ≠ 0 := by
    intro hzero
    have : ‖z‖ = 0 := by
      simp [hzero]
    rw [hz] at this
    norm_num at this

  set g := A.map (starRingEnd ℂ) with hg_def

  have hg_natDegree : g.natDegree ≤ N := by
    calc
      g.natDegree = (A.map (starRingEnd ℂ)).natDegree := rfl
      _ ≤ A.natDegree := Polynomial.natDegree_map_le (f := starRingEnd ℂ) (p := A)
      _ ≤ N := hA

  have hz_star_self : starRingEnd ℂ (z⁻¹) = z := by
    calc
      starRingEnd ℂ (z⁻¹) = star (z⁻¹) := rfl
      _ = (star z)⁻¹ := by rw [star_inv₀ (x := z)]
      _ = (starRingEnd ℂ z)⁻¹ := rfl
      _ = (z⁻¹)⁻¹ := by rw [Complex.inv_eq_conj hz]
      _ = z := by simp

  calc
    (conjRecip N A).eval z = (reflect N g).eval z := rfl
    _ = z ^ N * g.eval z⁻¹ := by
      rw [reflect_eval N g hg_natDegree hz_ne_zero]
    _ = z ^ N * ((A.map (starRingEnd ℂ)).eval z⁻¹) := rfl
    _ = z ^ N * starRingEnd ℂ (A.eval (starRingEnd ℂ (z⁻¹))) := by
      rw [map_conj_eval A (z⁻¹)]
    _ = z ^ N * starRingEnd ℂ (A.eval z) := by rw [hz_star_self]

/-- Modulus identity: `A(z) · A^{†N}(z) = zᴺ · |A(z)|²` on the unit circle. -/
theorem conjRecip_mul_eval (N : ℕ) (A : ℂ[X]) (hA : A.natDegree ≤ N) {z : ℂ} (hz : ‖z‖ = 1) :
    A.eval z * (conjRecip N A).eval z = z ^ N * ((‖A.eval z‖ ^ 2 : ℝ) : ℂ) := by
  rw [conjRecip_eval N A hA hz]
  calc
    A.eval z * (z ^ N * starRingEnd ℂ (A.eval z)) = z ^ N * (A.eval z * starRingEnd ℂ (A.eval z)) := by
      ring
    _ = z ^ N * ((‖A.eval z‖ ^ 2 : ℝ) : ℂ) := by
      have h : A.eval z * starRingEnd ℂ (A.eval z) = ((‖A.eval z‖ ^ 2 : ℝ) : ℂ) := by
        calc
          A.eval z * starRingEnd ℂ (A.eval z) = A.eval z * star (A.eval z) := by rw [starRingEnd_apply]
          _ = star (A.eval z) * A.eval z := mul_comm _ _
          _ = (Complex.normSq (A.eval z) : ℂ) := by
            simpa using (Complex.normSq_eq_conj_mul_self (z := A.eval z)).symm
          _ = ((Complex.normSq (A.eval z) : ℝ) : ℂ) := rfl
          _ = ((‖A.eval z‖ ^ 2 : ℝ) : ℂ) := by
            simp [Complex.normSq_eq_norm_sq]
      rw [h]

/-- Multiplicativity of the conjugate-reciprocal. -/
theorem conjRecip_mul (M N : ℕ) (A B : ℂ[X]) (hA : A.natDegree ≤ M) (hB : B.natDegree ≤ N) :
    conjRecip (M + N) (A * B) = conjRecip M A * conjRecip N B := by
  unfold conjRecip
  rw [Polynomial.map_mul]
  rw [Polynomial.reflect_mul (A.map (starRingEnd ℂ)) (B.map (starRingEnd ℂ))]
  · rw [Polynomial.natDegree_map]; exact hA
  · rw [Polynomial.natDegree_map]; exact hB

/-- Reflection commutes with coefficient mapping. -/
theorem reflect_map_comm {S : Type*} [CommSemiring S] (f : ℂ →+* S) (N : ℕ) (A : ℂ[X]) :
    reflect N (A.map f) = (reflect N A).map f := by
  exact Polynomial.reflect_map f A N

/-- The conjugate-reciprocal is an involution (for `N ≥ deg A`). -/
theorem conjRecip_conjRecip (N : ℕ) (A : ℂ[X]) (hA : A.natDegree ≤ N) :
    conjRecip N (conjRecip N A) = A := by
  unfold conjRecip
  calc
    reflect N ((reflect N (A.map (starRingEnd ℂ))).map (starRingEnd ℂ))
        = reflect N (reflect N ((A.map (starRingEnd ℂ)).map (starRingEnd ℂ))) := by
      rw [reflect_map_comm (starRingEnd ℂ) N (A.map (starRingEnd ℂ))]
    _ = reflect N (reflect N (A.map ((starRingEnd ℂ).comp (starRingEnd ℂ)))) := by
      rw [Polynomial.map_map]
    _ = reflect N (reflect N (A.map (RingHom.id ℂ))) := by
      simp
    _ = reflect N (reflect N A) := by simp
    _ = A := by
      simp

/-- The conjugate-reciprocal distributes over differences. -/
theorem conjRecip_sub (N : ℕ) (A B : ℂ[X]) :
    conjRecip N (A - B) = conjRecip N A - conjRecip N B := by
  unfold conjRecip
  rw [Polynomial.map_sub, Polynomial.reflect_sub]

/-- `(Xⁿ)^{†2n} = Xⁿ`. -/
theorem conjRecip_X_pow (n : ℕ) :
    conjRecip (2 * n) (X ^ n) = X ^ n := by
  unfold conjRecip
  calc
    reflect (2 * n) ((X ^ n).map (starRingEnd ℂ)) = reflect (2 * n) (X ^ n) := by
      simp [Polynomial.map_pow, Polynomial.map_X]
    _ = X ^ revAt (2 * n) n := by rw [Polynomial.reflect_monomial]
    _ = X ^ n := by
      have hn : n ≤ 2 * n := by
        simpa [two_mul] using Nat.le_add_left n n
      rw [Polynomial.revAt_le hn]
      have hsub : (2 * n : ℕ) - n = n := by
        calc
          (2 * n : ℕ) - n = n + n - n := by ring
          _ = n := Nat.add_sub_cancel n n
      rw [hsub]

/-- Coefficient symmetry of a self-inversive polynomial: `coeff j H = conj (coeff (2n-j) H)`. -/
theorem selfInversive_coeff_symm (n : ℕ) (H : ℂ[X]) (hself : conjRecip (2 * n) H = H)
    {j : ℕ} (hj : j ≤ 2 * n) :
    H.coeff j = starRingEnd ℂ (H.coeff (2 * n - j)) := by
  sorry

/-- Leading coefficient of the conjugate-reciprocal: `coeff N (A^{†N}) = conj (A 0)`, and if
`A 0 ≠ 0` then `deg (A^{†N}) = N` with leading coefficient `conj (A 0)`. -/
theorem conjRecip_leadingCoeff (N : ℕ) (A : ℂ[X]) (hA : A.natDegree ≤ N) :
    (conjRecip N A).coeff N = starRingEnd ℂ (A.eval 0) ∧
      (A.eval 0 ≠ 0 → (conjRecip N A).natDegree = N ∧
        (conjRecip N A).leadingCoeff = starRingEnd ℂ (A.eval 0)) := by
  sorry

end ComplexAnalysis
end LeanEval
