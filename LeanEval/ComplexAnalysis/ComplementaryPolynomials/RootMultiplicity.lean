import Mathlib
import EvalTools.Markers
import LeanEval.ComplexAnalysis.ComplementaryPolynomials.ConjugateReciprocal

/-!
Root-multiplicity transport under coefficient conjugation and under reflection, and the
inverse-conjugate root pairing for self-inversive polynomials. Helper file for
`LeanEval.ComplexAnalysis.ComplementaryPolynomials`.
-/

namespace LeanEval
namespace ComplexAnalysis

open Polynomial

/-- Multiplicity transport under conjugation. -/
theorem rootMultiplicity_map_conj (A : ℂ[X]) (v : ℂ) :
    (A.map (starRingEnd ℂ)).rootMultiplicity v = A.rootMultiplicity (starRingEnd ℂ v) := by
  have hinj : Function.Injective (starRingEnd ℂ) := star_injective (R := ℂ)
  simpa [starRingEnd_self_apply] using (Polynomial.eq_rootMultiplicity_map hinj (starRingEnd ℂ v)).symm

/-- Reflection of a linear factor. -/
theorem reflect_linear {v : ℂ} (hv : v ≠ 0) :
    reflect 1 (X - C v) = C (-v) * (X - C v⁻¹) := by
  calc
    reflect 1 (X - C v) = reflect 1 (C (1 : ℂ) * X ^ 1 + C (-v) * X ^ 0) := by
      congr 1
      calc
        X - C v = X + C (-v) := by
          simp [C_neg, sub_eq_add_neg]
        _ = C (1 : ℂ) * X ^ 1 + C (-v) * X ^ 0 := by simp
    _ = reflect 1 (C (1 : ℂ) * X ^ 1) + reflect 1 (C (-v) * X ^ 0) := by
      rw [reflect_add]
    _ = (C (1 : ℂ) * X ^ revAt 1 1) + (C (-v) * X ^ revAt 1 0) := by
      rw [reflect_C_mul_X_pow, reflect_C_mul_X_pow]
    _ = (C (1 : ℂ) * X ^ 0) + (C (-v) * X ^ 1) := by
      have h0 : (0 : ℕ) ≤ 1 := by omega
      have h1 : (1 : ℕ) ≤ 1 := by omega
      rw [revAt_le h0, revAt_le h1, Nat.sub_zero, show (1 : ℕ) - 1 = 0 by omega]
    _ = 1 + C (-v) * X := by simp
    _ = C (-v) * (X - C v⁻¹) := by
      calc
        1 + C (-v) * X = C (-v) * X - C (-1 : ℂ) := by
          calc
            1 + C (-v) * X = C (1 : ℂ) + C (-v) * X := by simp
            _ = C (-v) * X + C (1 : ℂ) := by ring
            _ = C (-v) * X - C (-1 : ℂ) := by simp
        _ = C (-v) * X - C (-v * v⁻¹) := by field_simp [hv]
        _ = C (-v) * X - C (-v) * C v⁻¹ := by simp
        _ = C (-v) * (X - C v⁻¹) := by ring

private lemma aux_reflect_linear' (v : ℂ) : reflect 1 X = (1 : ℂ[X]) := by
  calc
    reflect 1 X = reflect 1 (C (1 : ℂ) * X ^ 1) := by simp
    _ = C (1 : ℂ) * X ^ (revAt 1 1) := reflect_C_mul_X_pow 1 1 (c := (1 : ℂ))
    _ = X ^ 0 := by simp
    _ = 1 := by simp

private lemma aux_reflect_linear'' (v : ℂ) : reflect 1 (C v) = C v * X := by
  calc
    reflect 1 (C v) = reflect 1 (C v * X ^ 0) := by simp
    _ = C v * X ^ (revAt 1 0) := reflect_C_mul_X_pow 1 0 (c := v)
    _ = C v * X := by simp

private lemma dvd_reflect_transport_aux_reflect_pow (k : ℕ) (v : ℂ) :
    reflect k ((X - C v) ^ k) = (reflect 1 (X - C v)) ^ k := by
  induction' k with k ih
  · simp
  · have h_f_deg : ((X - C v) ^ k).natDegree ≤ k := by simp
    have h_g_deg : (X - C v).natDegree ≤ 1 := by simp
    calc
      reflect (k + 1) ((X - C v) ^ (k + 1))
          = reflect (k + 1) (((X - C v) ^ k) * (X - C v)) := by rw [pow_succ]
      _ = reflect k ((X - C v) ^ k) * reflect 1 (X - C v) :=
        Polynomial.reflect_mul ((X - C v) ^ k) (X - C v) h_f_deg h_g_deg
      _ = (reflect 1 (X - C v)) ^ k * reflect 1 (X - C v) := by rw [ih]
      _ = (reflect 1 (X - C v)) ^ (k + 1) := by rw [pow_succ]

private lemma dvd_reflect_transport_aux (N : ℕ) (A : ℂ[X]) (hA : A.natDegree ≤ N) {w : ℂ} (hw : w ≠ 0)
    (k : ℕ) (hdiv : (X - C w⁻¹) ^ k ∣ A) : (X - C w) ^ k ∣ reflect N A := by
  rcases hdiv with ⟨B, hA_eq⟩
  by_cases hA0 : A = 0
  · subst hA0; simp
  have hf0 : (X - C w⁻¹) ^ k ≠ 0 :=
    pow_ne_zero k (Polynomial.X_sub_C_ne_zero (w⁻¹))
  have hB0 : B ≠ 0 := by
    intro h
    apply hA0
    rw [hA_eq, h, mul_zero]
  have hf_deg_leq : ((X - C w⁻¹) ^ k).natDegree ≤ k := by simp
  have hf_deg_eq : ((X - C w⁻¹) ^ k).natDegree = k := by simp
  have h_deg_mul : A.natDegree = k + B.natDegree := by
    calc
      A.natDegree = ((X - C w⁻¹) ^ k * B).natDegree := by rw [hA_eq]
      _ = ((X - C w⁻¹) ^ k).natDegree + B.natDegree :=
        Polynomial.natDegree_mul hf0 hB0
      _ = k + B.natDegree := by rw [hf_deg_eq]
  have hk_le_N : k ≤ N := by
    have : k ≤ A.natDegree := by
      rw [h_deg_mul]
      exact Nat.le_add_right k (B.natDegree)
    exact Nat.le_trans this hA
  have hBdeg_leq : B.natDegree ≤ N - k := by
    have hsum : k + B.natDegree ≤ N := by
      rw [← h_deg_mul]
      exact hA
    have hsub : (k + B.natDegree) - k ≤ N - k := Nat.sub_le_sub_right hsum k
    simpa [Nat.add_sub_cancel] using hsub
  have h_sum_eq : k + (N - k) = N := by omega
  have h_reflect_eq : reflect N A = reflect k ((X - C w⁻¹) ^ k) * reflect (N - k) B := by
    calc
      reflect N A = reflect N ((X - C w⁻¹) ^ k * B) := by rw [hA_eq]
      _ = reflect (k + (N - k)) ((X - C w⁻¹) ^ k * B) := by rw [h_sum_eq]
      _ = reflect k ((X - C w⁻¹) ^ k) * reflect (N - k) B :=
        Polynomial.reflect_mul ((X - C w⁻¹) ^ k) B hf_deg_leq hBdeg_leq
  rw [h_reflect_eq]
  have h_dvd_reflect_pow : (X - C w) ^ k ∣ reflect k ((X - C w⁻¹) ^ k) := by
    have h_eq : reflect k ((X - C w⁻¹) ^ k) = (C (-w⁻¹)) ^ k * (X - C w) ^ k := by
      calc
        reflect k ((X - C w⁻¹) ^ k) = (reflect 1 (X - C w⁻¹)) ^ k :=
          dvd_reflect_transport_aux_reflect_pow k (w⁻¹)
        _ = (C (-w⁻¹) * (X - C (w⁻¹)⁻¹)) ^ k := by
          simpa [inv_inv] using congrArg (· ^ k) (reflect_linear (inv_ne_zero hw))
        _ = (C (-w⁻¹) * (X - C w)) ^ k := by simp [inv_inv]
        _ = (C (-w⁻¹)) ^ k * (X - C w) ^ k := by rw [mul_pow]
    rw [h_eq]
    exact dvd_mul_left ((X - C w) ^ k) ((C (-w⁻¹)) ^ k)
  refine h_dvd_reflect_pow.trans ?_
  exact dvd_mul_right (reflect k ((X - C w⁻¹) ^ k)) (reflect (N - k) B)

/-- Reflection of a power of a linear factor: a unit multiple of `(X - C v⁻¹) ^ k`. -/
theorem reflect_pow_linear {v : ℂ} (hv : v ≠ 0) (k : ℕ) :
    reflect k ((X - C v) ^ k) = (C (-v)) ^ k * (X - C v⁻¹) ^ k := by
  calc
    reflect k ((X - C v) ^ k) = (reflect 1 (X - C v)) ^ k :=
      dvd_reflect_transport_aux_reflect_pow k v
    _ = (C (-v) * (X - C v⁻¹)) ^ k := by rw [reflect_linear hv]
    _ = (C (-v)) ^ k * (X - C v⁻¹) ^ k := by rw [mul_pow]

/-- Divisibility transport under reflection. -/
theorem dvd_reflect_transport (N : ℕ) (A : ℂ[X]) (hA : A.natDegree ≤ N) {w : ℂ} (hw : w ≠ 0)
    (k : ℕ) :
    (X - C w) ^ k ∣ reflect N A ↔ (X - C w⁻¹) ^ k ∣ A := by
  constructor
  · intro h
    have h_ref_deg : (reflect N A).natDegree ≤ N := by
      calc
        (reflect N A).natDegree ≤ max N A.natDegree := Polynomial.natDegree_reflect_le
        _ ≤ N := by simp [hA]
    have h_imp := dvd_reflect_transport_aux N (reflect N A) h_ref_deg (w := w⁻¹) (hw := inv_ne_zero hw) k
    have h_goal : (X - C w⁻¹) ^ k ∣ reflect N (reflect N A) :=
      h_imp (by simpa [inv_inv] using h)
    simpa [Polynomial.reflect_reflect] using h_goal
  · intro h
    apply dvd_reflect_transport_aux N A hA (w := w) (hw := hw) k
    exact h

/-- Multiplicity transport under reflection: mult of `w` in `reflect N A` equals mult of `w⁻¹`. -/
theorem rootMultiplicity_reflect (N : ℕ) (A : ℂ[X]) (hA0 : A ≠ 0) (hA : A.natDegree ≤ N) {w : ℂ}
    (hw : w ≠ 0) :
    (reflect N A).rootMultiplicity w = A.rootMultiplicity w⁻¹ := by
  have hR0 : reflect N A ≠ 0 := mt reflect_eq_zero_iff.mp hA0
  have h_forall : ∀ k, (k ≤ (reflect N A).rootMultiplicity w) ↔ (k ≤ A.rootMultiplicity w⁻¹) := by
    intro k
    rw [Polynomial.le_rootMultiplicity_iff hR0, Polynomial.le_rootMultiplicity_iff hA0,
      dvd_reflect_transport N A hA hw k]
  apply le_antisymm
  · apply (h_forall ((reflect N A).rootMultiplicity w)).mp
    exact le_refl _
  · apply (h_forall (A.rootMultiplicity w⁻¹)).mpr
    exact le_refl _

/-- Inverse-conjugate root pairing for a self-inversive polynomial. -/
theorem conjRecip_root_pairing (n : ℕ) (H : ℂ[X]) (hH0 : H ≠ 0) (hH : H.natDegree ≤ 2 * n)
    (hself : conjRecip (2 * n) H = H) {w : ℂ} (hw : w ≠ 0) :
    H.rootMultiplicity w = H.rootMultiplicity (starRingEnd ℂ w)⁻¹ := by
  have h_map_ne_zero : H.map (starRingEnd ℂ) ≠ 0 := Polynomial.map_ne_zero hH0
  have h_map_natDegree : (H.map (starRingEnd ℂ)).natDegree ≤ 2 * n := by
    calc
      (H.map (starRingEnd ℂ)).natDegree ≤ H.natDegree := Polynomial.natDegree_map_le
      _ ≤ 2 * n := hH
  have h_H_eq_reflect : H = reflect (2 * n) (H.map (starRingEnd ℂ)) := by
    calc
      H = conjRecip (2 * n) H := by symm; exact hself
      _ = reflect (2 * n) ((H.map (starRingEnd ℂ))) := rfl
  calc
    H.rootMultiplicity w = (reflect (2 * n) (H.map (starRingEnd ℂ))).rootMultiplicity w :=
      congrArg (fun q : ℂ[X] => q.rootMultiplicity w) h_H_eq_reflect
    _ = (H.map (starRingEnd ℂ)).rootMultiplicity w⁻¹ :=
      rootMultiplicity_reflect (2 * n) (H.map (starRingEnd ℂ)) h_map_ne_zero h_map_natDegree hw
    _ = H.rootMultiplicity (starRingEnd ℂ (w⁻¹)) :=
      rootMultiplicity_map_conj H (w⁻¹)
    _ = H.rootMultiplicity ((starRingEnd ℂ w)⁻¹) := by simp

/-- Local factorization at a root. -/
theorem local_factorization (H : ℂ[X]) (hH : H ≠ 0) (w : ℂ) :
    ∃ g : ℂ[X], H = (X - C w) ^ (H.rootMultiplicity w) * g ∧ g.eval w ≠ 0 := by
  rcases Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd H hH w with ⟨g, h_eq, h_not_dvd⟩
  refine ⟨g, h_eq, ?_⟩
  intro h_eval
  apply h_not_dvd
  exact Polynomial.dvd_iff_isRoot.mpr h_eval

end ComplexAnalysis
end LeanEval
