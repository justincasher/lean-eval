import Mathlib

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
theorem conjRecip_conjRecip (N : ℕ) (A : ℂ[X]) (_hA : A.natDegree ≤ N) :
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
        simp [two_mul]
      rw [Polynomial.revAt_le hn]
      have hsub : (2 * n : ℕ) - n = n := by omega
      rw [hsub]

/-- Coefficient symmetry of a self-inversive polynomial: `coeff j H = conj (coeff (2n-j) H)`. -/
theorem selfInversive_coeff_symm (n : ℕ) (H : ℂ[X]) (hself : conjRecip (2 * n) H = H)
    {j : ℕ} (hj : j ≤ 2 * n) :
    H.coeff j = starRingEnd ℂ (H.coeff (2 * n - j)) := by
  unfold conjRecip at hself
  have hcoeff : (reflect (2 * n) (H.map (starRingEnd ℂ))).coeff j = H.coeff j := by
    rw [hself]
  rw [Polynomial.coeff_reflect] at hcoeff
  rw [Polynomial.revAt_le hj] at hcoeff
  rw [Polynomial.coeff_map] at hcoeff
  exact hcoeff.symm

/-- Leading coefficient of the conjugate-reciprocal: `coeff N (A^{†N}) = conj (A 0)`, and if
`A 0 ≠ 0` then `deg (A^{†N}) = N` with leading coefficient `conj (A 0)`. -/
theorem conjRecip_leadingCoeff (N : ℕ) (A : ℂ[X]) (hA : A.natDegree ≤ N) :
    (conjRecip N A).coeff N = starRingEnd ℂ (A.eval 0) ∧
      (A.eval 0 ≠ 0 → (conjRecip N A).natDegree = N ∧
        (conjRecip N A).leadingCoeff = starRingEnd ℂ (A.eval 0)) := by
  -- Part 1: coefficient at degree N
  have hcoeffN : (conjRecip N A).coeff N = starRingEnd ℂ (A.eval 0) := by
    unfold conjRecip
    calc
      (reflect N (A.map (starRingEnd ℂ))).coeff N = (A.map (starRingEnd ℂ)).coeff (revAt N N) := by
        rw [coeff_reflect]
      _ = (A.map (starRingEnd ℂ)).coeff 0 := by
        simp
      _ = starRingEnd ℂ (A.coeff 0) := by rw [coeff_map]
      _ = starRingEnd ℂ (A.eval 0) := by rw [coeff_zero_eq_eval_zero]

  -- Part 2: degree and leading coefficient when the constant term is nonzero
  have h_deg_le_N : (conjRecip N A).natDegree ≤ N :=
    conjRecip_natDegree_le N A hA

  refine ⟨hcoeffN, ?_⟩

  intro hA0_ne

  -- The coefficient at N is nonzero, because star is injective
  have hcoeffN_ne_zero : (conjRecip N A).coeff N ≠ 0 := by
    rw [hcoeffN]
    intro hzero
    apply hA0_ne
    have hstar_inj : Function.Injective (starRingEnd ℂ) := star_injective
    apply hstar_inj
    simpa using hzero

  have h_natDegree_eq_N : (conjRecip N A).natDegree = N := by
    apply le_antisymm h_deg_le_N
    by_contra hlt
    have hlt' : (conjRecip N A).natDegree < N := Nat.lt_of_not_ge hlt
    have hcoeffN_zero : (conjRecip N A).coeff N = 0 :=
      coeff_eq_zero_of_natDegree_lt hlt'
    exact hcoeffN_ne_zero hcoeffN_zero

  have h_leadingCoeff : (conjRecip N A).leadingCoeff = starRingEnd ℂ (A.eval 0) := by
    rw [leadingCoeff, h_natDegree_eq_N, hcoeffN]

  exact ⟨h_natDegree_eq_N, h_leadingCoeff⟩

end ComplexAnalysis
end LeanEval
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
    conjRecip_natDegree_le P.natDegree P le_rfl
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
  have hconjdeg : (conjRecip n P).natDegree ≤ n := conjRecip_natDegree_le n P le_rfl
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

private lemma aux_reflect_linear' (_v : ℂ) : reflect 1 X = (1 : ℂ[X]) := by
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
/-!
Roots on the unit circle of a circle-nonnegative polynomial have even multiplicity. The analytic
core: sign persistence, even-order forcing, the `eⁱᵗ - 1 = it·u(t)` expansion, and
real-valuedness of the reduced factor. Helper file for
`LeanEval.ComplexAnalysis.ComplementaryPolynomials`.
-/

namespace LeanEval
namespace ComplexAnalysis

open Polynomial

/-- Sign persistence: a continuous function positive at `0` is positive near `0`. -/
theorem sign_persistence {φ : ℝ → ℝ} (hφ : Continuous φ) (h : 0 < φ 0) :
    ∀ᶠ t in nhds (0 : ℝ), 0 < φ t := by
  -- The set (0, ∞) is open and contains φ 0
  have hmem : Set.Ioi (0 : ℝ) ∈ nhds (φ 0) := isOpen_Ioi.mem_nhds h
  -- Continuity at 0 pulls back neighbourhoods of φ 0 to neighbourhoods of 0
  have hmem' : φ ⁻¹' Set.Ioi (0 : ℝ) ∈ nhds (0 : ℝ) := hφ.continuousAt hmem
  -- Unfold the definition of ∀ᶠ in 𝓝 0
  filter_upwards [hmem'] with t ht
  exact ht

/-- Nonnegativity of `tᵐ φ(t)` near `0` (with `φ(0) > 0`) forces `m` even. -/
theorem nonneg_even_order_pos {φ : ℝ → ℝ} (hφ : Continuous φ) (h0 : 0 < φ 0) (m : ℕ)
    (hnn : ∀ᶠ t in nhds (0 : ℝ), 0 ≤ t ^ m * φ t) : Even m := by
  have hφpos : ∀ᶠ t in nhds (0 : ℝ), 0 < φ t := sign_persistence hφ h0
  have hboth : ∀ᶠ t in nhds (0 : ℝ), 0 ≤ t ^ m * φ t ∧ 0 < φ t := hnn.and hφpos
  rcases Metric.mem_nhds_iff.mp hboth with ⟨ε, hε, hball⟩
  have hneg : -ε/2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    constructor <;> nlinarith
  have hboth_t : 0 ≤ (-ε/2 : ℝ) ^ m * φ (-ε/2) ∧ 0 < φ (-ε/2) := by
    simpa using hball hneg
  have hnn_s : 0 ≤ (-ε/2 : ℝ) ^ m * φ (-ε/2) := hboth_t.1
  have hpos_s : 0 < φ (-ε/2) := hboth_t.2
  by_cases hm : Even m
  · exact hm
  · have hm_odd : Odd m := by
      rcases Nat.even_or_odd m with (hm_even | hm_odd)
      · exact absurd hm_even hm
      · exact hm_odd
    have h_pow_neg : (-ε/2 : ℝ) ^ m < 0 :=
      hm_odd.pow_neg (by nlinarith)
    have h_mul_neg : (-ε/2 : ℝ) ^ m * φ (-ε/2) < 0 :=
      mul_neg_of_neg_of_pos h_pow_neg hpos_s
    nlinarith

/-- Nonnegativity of `tᵐ φ(t)` near `0` (with `φ(0) ≠ 0`) forces `m` even. -/
theorem nonneg_even_order {φ : ℝ → ℝ} (hφ : Continuous φ) (h0 : φ 0 ≠ 0) (m : ℕ)
    (hnn : ∀ᶠ t in nhds (0 : ℝ), 0 ≤ t ^ m * φ t) : Even m := by
  by_cases hpos : 0 < φ 0
  · -- φ 0 > 0
    have hφpos : ∀ᶠ t in nhds (0 : ℝ), 0 < φ t := sign_persistence hφ hpos
    have hboth : ∀ᶠ t in nhds (0 : ℝ), 0 ≤ t ^ m * φ t ∧ 0 < φ t := hnn.and hφpos
    rcases Metric.mem_nhds_iff.mp hboth with ⟨ε, hε, hball⟩
    have hneg : -ε/2 ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
      constructor <;> nlinarith
    have hboth_t : 0 ≤ (-ε/2 : ℝ) ^ m * φ (-ε/2) ∧ 0 < φ (-ε/2) := by
      simpa using hball hneg
    have hnn_s : 0 ≤ (-ε/2 : ℝ) ^ m * φ (-ε/2) := hboth_t.1
    have hpos_s : 0 < φ (-ε/2) := hboth_t.2
    by_cases hm : Even m
    · exact hm
    · have hm_odd : Odd m := by
        rcases Nat.even_or_odd m with (hm_even | hm_odd)
        · exact absurd hm_even hm
        · exact hm_odd
      have h_pow_neg : (-ε/2 : ℝ) ^ m < 0 :=
        hm_odd.pow_neg (by nlinarith)
      have h_mul_neg : (-ε/2 : ℝ) ^ m * φ (-ε/2) < 0 :=
        mul_neg_of_neg_of_pos h_pow_neg hpos_s
      nlinarith
  · -- φ 0 ≤ 0, so φ 0 < 0 since φ 0 ≠ 0
    have hneg : φ 0 < 0 := by
      by_contra! h
      have : 0 < φ 0 := lt_of_le_of_ne h h0.symm
      exact hpos this
    -- apply sign_persistence to -φ
    have h_neg_φ : Continuous (-φ) := hφ.neg
    have h_neg_φ_zero : 0 < (-φ) 0 := by simpa using hneg
    have hφneg : ∀ᶠ t in nhds (0 : ℝ), 0 < (-φ) t := sign_persistence h_neg_φ h_neg_φ_zero
    have hboth : ∀ᶠ t in nhds (0 : ℝ), 0 ≤ t ^ m * φ t ∧ 0 < (-φ) t := hnn.and hφneg
    rcases Metric.mem_nhds_iff.mp hboth with ⟨ε, hε, hball⟩
    have hpos2 : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
      constructor <;> nlinarith
    have hboth_t : 0 ≤ (ε/2 : ℝ) ^ m * φ (ε/2) ∧ 0 < (-φ) (ε/2) := by
      simpa using hball hpos2
    have hnn_s : 0 ≤ (ε/2 : ℝ) ^ m * φ (ε/2) := hboth_t.1
    have hneg_s : φ (ε/2) < 0 := by
      have hpos_negφ : 0 < (-φ) (ε/2) := hboth_t.2
      -- (-φ)(x) = -(φ x), so 0 < -(φ(ε/2)), hence φ(ε/2) < 0
      have : (-φ) (ε/2) = -(φ (ε/2)) := rfl
      rw [this] at hpos_negφ
      linarith
    by_cases hm : Even m
    · exact hm
    · have hm_odd : Odd m := by
        rcases Nat.even_or_odd m with (hm_even | hm_odd)
        · exact absurd hm_even hm
        · exact hm_odd
      have h_pow_pos : 0 < (ε/2 : ℝ) ^ m := pow_pos (by nlinarith) m
      nlinarith

/-- Linear expansion `eⁱᵗ - 1 = i t u(t)` with `u` continuous and `u(0) = 1`. -/
theorem exp_sub_one_expansion :
    ∃ u : ℝ → ℂ, Continuous u ∧ u 0 = 1 ∧
      ∀ t : ℝ, Complex.exp (Complex.I * (t : ℂ)) - 1 = Complex.I * (t : ℂ) * u t := by
  -- derivative of f(z) = exp(Iz) at 0 is I
  have hderiv : HasDerivAt (fun (z : ℂ) => Complex.exp (Complex.I * z)) Complex.I (0 : ℂ) := by
    have h_lin : HasDerivAt (fun (z : ℂ) => Complex.I * z) Complex.I (0 : ℂ) :=
      hasDerivAt_const_mul Complex.I (x := (0 : ℂ))
    have h_cexp := h_lin.cexp
    simpa [Complex.exp_zero, mul_comm, one_mul] using h_cexp

  have hI_ne_zero : Complex.I ≠ 0 := by norm_num

  -- g(z) = update ((exp(Iz)-1)/z) 0 I, continuous at 0 by HasDerivAt.continuousAt_div
  have hg_cont_at_0_raw : ContinuousAt
    (Function.update (fun (z : ℂ) => (Complex.exp (Complex.I * z) - Complex.exp (Complex.I * (0 : ℂ))) / (z - 0)) (0 : ℂ) Complex.I)
    (0 : ℂ) :=
    hderiv.continuousAt_div

  have hg_cont_at_0 : ContinuousAt
    (Function.update (fun (z : ℂ) => (Complex.exp (Complex.I * z) - 1) / z) (0 : ℂ) Complex.I) (0 : ℂ) := by
    simpa using hg_cont_at_0_raw

  let g : ℂ → ℂ := Function.update (fun (z : ℂ) => (Complex.exp (Complex.I * z) - 1) / z) 0 Complex.I
  have hg0 : g 0 = Complex.I := by
    simp [g]

  -- define u(t) = g(t : ℂ) / I
  let u : ℝ → ℂ := fun t => g ((t : ℂ)) / Complex.I
  have hu0 : u 0 = 1 := by
    simp [u, hg0]

  -- verify the identity for all t
  have hu_id : ∀ t : ℝ, Complex.exp (Complex.I * (t : ℂ)) - 1 = Complex.I * (t : ℂ) * u t := by
    intro t
    by_cases ht : t = 0
    · subst ht; simp
    · have hz_ne_zero : (t : ℂ) ≠ 0 := by exact_mod_cast ht
      have hg_eq : g (t : ℂ) = (Complex.exp (Complex.I * (t : ℂ)) - 1) / (t : ℂ) := by
        simp [g, hz_ne_zero]
      calc
        Complex.exp (Complex.I * (t : ℂ)) - 1
            = ((Complex.exp (Complex.I * (t : ℂ)) - 1) / (t : ℂ)) * (t : ℂ) := by
          field_simp [hz_ne_zero]
        _ = g (t : ℂ) * (t : ℂ) := by rw [hg_eq]
        _ = (g (t : ℂ) / Complex.I) * (Complex.I * (t : ℂ)) := by
          field_simp [hI_ne_zero, g, hg_eq]
        _ = Complex.I * (t : ℂ) * u t := by
          dsimp [u]
          ring

  -- continuity of u
  have hu_cont : Continuous u := by
    -- u is continuous at 0 because g is continuous at 0 and division by I is continuous
    have h_cont_at_0 : ContinuousAt u 0 := by
      have hmap_cont : ContinuousAt (fun (t : ℝ) => (t : ℂ)) (0 : ℝ) :=
        Complex.continuous_ofReal.continuousAt
      have hg_comp_cont : ContinuousAt (fun (t : ℝ) => g ((t : ℂ))) (0 : ℝ) :=
        hg_cont_at_0.comp (f := fun (t : ℝ) => (t : ℂ)) (x := (0 : ℝ)) hmap_cont
      refine ContinuousAt.div (by
        simpa using hg_comp_cont
      ) continuousAt_const hI_ne_zero
    -- u is continuous away from 0 because it's a quotient of continuous functions
    have h_cont_away : ∀ (t : ℝ), t ≠ 0 → ContinuousAt u t := by
      intro t ht
      have hmap_cont : ContinuousAt (fun (s : ℝ) => (s : ℂ)) t :=
        Complex.continuous_ofReal.continuousAt
      have h_num_cont : ContinuousAt (fun (s : ℝ) => Complex.exp (Complex.I * (s : ℂ)) - 1) t := by
        refine ContinuousAt.sub ?_ continuousAt_const
        refine (Complex.continuous_exp.continuousAt.comp ?_)
        exact (ContinuousAt.const_mul hmap_cont Complex.I)
      have h_den_cont : ContinuousAt (fun (s : ℝ) => Complex.I * (s : ℂ)) t :=
        ContinuousAt.const_mul hmap_cont Complex.I
      have h_den_ne_zero_val : Complex.I * (t : ℂ) ≠ 0 := by
        intro hzero
        apply ht
        have : (t : ℂ) = 0 := mul_eq_zero.mp hzero |>.resolve_left hI_ne_zero
        exact_mod_cast this
      -- for t ≠ 0, u(s) = (exp(I*s)-1)/(I*s) for all s near t (s ≠ 0)
      have h_local_eq : u =ᶠ[nhds t] (fun (s : ℝ) => (Complex.exp (Complex.I * (s : ℂ)) - 1) / (Complex.I * (s : ℂ))) := by
        -- the set {s | s ≠ 0} is open and contains t, so it's a neighbourhood of t
        have hopen : IsOpen ({x : ℝ | x ≠ 0} : Set ℝ) := isOpen_ne
        have hmem : {x : ℝ | x ≠ 0} ∈ nhds t := hopen.mem_nhds ht
        refine Filter.eventually_of_mem hmem ?_
        intro s hs
        dsimp [u]
        have hz_ne_zero_s : (s : ℂ) ≠ 0 := by exact_mod_cast hs
        field_simp [hI_ne_zero, hz_ne_zero_s]
        simp [g, hz_ne_zero_s]
      apply (ContinuousAt.congr ?_ h_local_eq.symm)
      exact (h_num_cont.div h_den_cont h_den_ne_zero_val)
    refine continuous_iff_continuousAt.mpr fun t => ?_
    by_cases ht : t = 0
    · subst ht; exact h_cont_at_0
    · exact h_cont_away t ht

  exact ⟨u, hu_cont, hu0, hu_id⟩

/-- If `tᵐ ψ(t)` is real for all `t`, then `ψ(t)` is real for all `t`. -/
theorem psi_real {ψ : ℝ → ℂ} (hψ : Continuous ψ) (m : ℕ)
    (hreal : ∀ t : ℝ, ((t : ℂ) ^ m * ψ t).im = 0) :
    ∀ t : ℝ, (ψ t).im = 0 := by
  set f : ℝ → ℝ := fun t => (ψ t).im with hf
  have hf_cont : Continuous f :=
    Complex.continuous_im.comp hψ
  have hfzero : Set.EqOn f (fun _ => (0 : ℝ)) ({0}ᶜ : Set ℝ) := by
    intro t ht
    rw [Set.mem_compl_iff, Set.mem_singleton_iff] at ht
    have h_im_tpow : ((t : ℂ) ^ m).im = 0 := by
      simpa [map_pow] using (Complex.ofReal_im (t ^ m))
    have h_mul_im : ((t : ℂ) ^ m * ψ t).im = ((t : ℂ) ^ m).re * (ψ t).im := by
      calc
        ((t : ℂ) ^ m * ψ t).im = ((t : ℂ) ^ m).re * (ψ t).im + ((t : ℂ) ^ m).im * (ψ t).re := by
          rw [Complex.mul_im]
        _ = ((t : ℂ) ^ m).re * (ψ t).im := by rw [h_im_tpow, zero_mul, add_zero]
    have h_re_nz : ((t : ℂ) ^ m).re ≠ 0 := by
      have h_t_ne_zero : (t : ℂ) ≠ 0 := by exact mod_cast ht
      have h_pow_nz : (t : ℂ) ^ m ≠ 0 := pow_ne_zero m h_t_ne_zero
      intro hzero
      apply h_pow_nz
      exact Complex.ext (by simpa using hzero) h_im_tpow
    have hzero_mul : ((t : ℂ) ^ m * ψ t).im = 0 := hreal t
    rw [h_mul_im] at hzero_mul
    have h_imzero : (ψ t).im = 0 := mul_eq_zero.mp hzero_mul |>.resolve_left h_re_nz
    simp [f, h_imzero]
  have h_dense : Dense ({0}ᶜ : Set ℝ) := dense_compl_singleton (0 : ℝ)
  have h_zero_cont : Continuous fun _ : ℝ => (0 : ℝ) := continuous_const
  have h_eq : f = fun _ : ℝ => (0 : ℝ) :=
    hf_cont.ext_on h_dense h_zero_cont hfzero
  intro t
  simpa [f] using congr_fun h_eq t

/-- Continuity of the reduced circle factor `ψ(t) = (w eⁱᵗ)⁻ⁿ (i w)ᵐ u(t)ᵐ g(w eⁱᵗ)`. -/
theorem psi_continuous (w : ℂ) (hw : ‖w‖ = 1) (n m : ℕ) (g : ℂ[X])
    (u : ℝ → ℂ) (hu_cont : Continuous u) (hu0 : u 0 = 1) :
    Continuous (fun t : ℝ => (w * Complex.exp (Complex.I * (t : ℂ)))⁻¹ ^ n *
        (Complex.I * w) ^ m * u t ^ m * g.eval (w * Complex.exp (Complex.I * (t : ℂ)))) ∧
      (fun t : ℝ => (w * Complex.exp (Complex.I * (t : ℂ)))⁻¹ ^ n *
        (Complex.I * w) ^ m * u t ^ m * g.eval (w * Complex.exp (Complex.I * (t : ℂ)))) 0
        = w⁻¹ ^ n * (Complex.I * w) ^ m * g.eval w := by
  have hw_ne_zero : w ≠ 0 := by
    intro h
    rw [h] at hw
    simp at hw
  have h_exp_ne_zero : ∀ t : ℝ, Complex.exp (Complex.I * (t : ℂ)) ≠ 0 := fun t =>
    Complex.exp_ne_zero _
  have h_f_ne_zero : ∀ t : ℝ, w * Complex.exp (Complex.I * (t : ℂ)) ≠ 0 := fun t =>
    mul_ne_zero hw_ne_zero (h_exp_ne_zero t)
  let f : ℝ → ℂ := fun t => w * Complex.exp (Complex.I * (t : ℂ))
  have hf_cont : Continuous f := by
    dsimp [f]
    have h_exp_cont : Continuous (fun (t : ℝ) => Complex.exp (Complex.I * (t : ℂ))) :=
      Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
    exact continuous_const.mul h_exp_cont
  have h_cont_inv_pow : Continuous (fun t : ℝ => (f t)⁻¹ ^ n) := by
    have h_inv_cont : Continuous (fun t : ℝ => (f t)⁻¹) := by
      refine continuous_iff_continuousAt.mpr fun t => ?_
      have hf_contAt : ContinuousAt f t := hf_cont.continuousAt
      exact hf_contAt.inv₀ (h_f_ne_zero t)
    exact h_inv_cont.pow n
  have h_cont_const : Continuous (fun _ : ℝ => (Complex.I * w) ^ m) :=
    continuous_const
  have h_cont_u_pow : Continuous (fun t : ℝ => u t ^ m) :=
    hu_cont.pow m
  have h_cont_g : Continuous (fun t : ℝ => g.eval (f t)) :=
    g.continuous.comp hf_cont
  have h_cont_prod : Continuous (fun t : ℝ => (f t)⁻¹ ^ n * (Complex.I * w) ^ m * u t ^ m * g.eval (f t)) := by
    refine ((h_cont_inv_pow.mul h_cont_const).mul h_cont_u_pow).mul h_cont_g
  have h_val0 : (fun t : ℝ => (w * Complex.exp (Complex.I * (t : ℂ)))⁻¹ ^ n *
      (Complex.I * w) ^ m * u t ^ m * g.eval (w * Complex.exp (Complex.I * (t : ℂ)))) 0
      = w⁻¹ ^ n * (Complex.I * w) ^ m * g.eval w := by
    simp [hu0]
  exact ⟨h_cont_prod, h_val0⟩

/-- A circle root of a circle-nonnegative polynomial has even multiplicity. -/
theorem circle_root_even (n : ℕ) (H : ℂ[X]) (hH : H ≠ 0) (hpos : NonnegRealOnCircle n H)
    {w : ℂ} (hw : ‖w‖ = 1) : Even (H.rootMultiplicity w) := by
  set m := H.rootMultiplicity w with hm
  -- Factor H = (X - w)ᵐ·g with g(w) ≠ 0
  rcases local_factorization H hH w with ⟨g, hH_eq, hg⟩
  have hw_ne_zero : w ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hw
    norm_num at hw
  -- Get u from the exponential expansion
  rcases exp_sub_one_expansion with ⟨u, hu_cont, hu0, hu_id⟩
  -- Define ψ(t) = (w·eⁱᵗ)⁻ⁿ·(i·w)ᵐ·u(t)ᵐ·g(w·eⁱᵗ)
  set ψ : ℝ → ℂ := fun t => (w * Complex.exp (Complex.I * (t : ℂ)))⁻¹ ^ n *
    (Complex.I * w) ^ m * u t ^ m * g.eval (w * Complex.exp (Complex.I * (t : ℂ))) with hψ
  have hz_norm_one : ∀ t : ℝ, ‖w * Complex.exp (Complex.I * (t : ℂ))‖ = 1 := by
    intro t
    calc
      ‖w * Complex.exp (Complex.I * (t : ℂ))‖ = ‖w‖ * ‖Complex.exp (Complex.I * (t : ℂ))‖ := norm_mul _ _
      _ = 1 * 1 := by
        rw [hw]
        simp
      _ = 1 := by simp
  have hz_nonzero : ∀ t : ℝ, w * Complex.exp (Complex.I * (t : ℂ)) ≠ 0 := by
    intro t
    exact norm_ne_zero_iff.mp (by
      have : ‖w * Complex.exp (Complex.I * (t : ℂ))‖ = 1 := hz_norm_one t
      linarith)
  -- ψ is continuous
  have hψ_cont : Continuous ψ := by
    have h_cont_z : Continuous (fun t : ℝ => w * Complex.exp (Complex.I * (t : ℂ))) := by
      refine continuous_const.mul ?_
      have h_lin_cont : Continuous (fun (t : ℝ) => Complex.I * (t : ℂ)) :=
        (continuous_const.mul Complex.continuous_ofReal)
      exact Complex.continuous_exp.comp h_lin_cont
    have h_cont_inv : Continuous (fun t : ℝ => (w * Complex.exp (Complex.I * (t : ℂ)))⁻¹) :=
      h_cont_z.inv₀ hz_nonzero
    have h_cont_inv_pow : Continuous (fun t : ℝ => (w * Complex.exp (Complex.I * (t : ℂ)))⁻¹ ^ n) :=
      h_cont_inv.pow n
    have h_cont_Iw_pow : Continuous (fun _ : ℝ => (Complex.I * w) ^ m) := continuous_const
    have h_cont_u_pow : Continuous (fun t : ℝ => u t ^ m) := hu_cont.pow m
    have h_cont_g : Continuous (fun t : ℝ => g.eval (w * Complex.exp (Complex.I * (t : ℂ)))) :=
      (Polynomial.continuous g).comp h_cont_z
    have h_raw_cont : Continuous (fun t : ℝ => (w * Complex.exp (Complex.I * (t : ℂ)))⁻¹ ^ n *
      ((Complex.I * w) ^ m * u t ^ m * g.eval (w * Complex.exp (Complex.I * (t : ℂ))))) :=
      h_cont_inv_pow.mul ((h_cont_Iw_pow.mul h_cont_u_pow).mul h_cont_g)
    simpa [ψ, mul_assoc] using h_raw_cont
  -- ψ(0) ≠ 0
  have hψ0_ne_zero : ψ 0 ≠ 0 := by
    have hψ0_val : ψ 0 = w⁻¹ ^ n * (Complex.I * w) ^ m * g.eval w := by
      dsimp [ψ]
      simp [hu0, Complex.exp_zero]
    rw [hψ0_val]
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact pow_ne_zero n (inv_ne_zero hw_ne_zero)
      · exact pow_ne_zero m (mul_ne_zero (by norm_num : Complex.I ≠ 0) hw_ne_zero)
    · exact hg
  -- Key identity: (w·eⁱᵗ)⁻ⁿ·H(w·eⁱᵗ) = tᵐ·ψ(t)
  have h_identity : ∀ t : ℝ, (w * Complex.exp (Complex.I * (t : ℂ)))⁻¹ ^ n *
    H.eval (w * Complex.exp (Complex.I * (t : ℂ))) = (t : ℂ) ^ m * ψ t := by
    intro t
    calc
      (w * Complex.exp (Complex.I * (t : ℂ)))⁻¹ ^ n *
        H.eval (w * Complex.exp (Complex.I * (t : ℂ)))
          = (w * Complex.exp (Complex.I * (t : ℂ)))⁻¹ ^ n *
            (((X - C w) ^ m * g).eval (w * Complex.exp (Complex.I * (t : ℂ)))) := by rw [hH_eq]
      _ = (w * Complex.exp (Complex.I * (t : ℂ)))⁻¹ ^ n *
          ((w * Complex.exp (Complex.I * (t : ℂ)) - w) ^ m *
            g.eval (w * Complex.exp (Complex.I * (t : ℂ)))) := by
        simp [eval_mul, eval_pow, eval_sub, eval_X, eval_C]
      _ = (w * Complex.exp (Complex.I * (t : ℂ)))⁻¹ ^ n *
          ((w * (Complex.exp (Complex.I * (t : ℂ)) - 1)) ^ m *
            g.eval (w * Complex.exp (Complex.I * (t : ℂ)))) := by ring
      _ = (w * Complex.exp (Complex.I * (t : ℂ)))⁻¹ ^ n *
          ((w * (Complex.I * (t : ℂ) * u t)) ^ m *
            g.eval (w * Complex.exp (Complex.I * (t : ℂ)))) := by rw [hu_id t]
      _ = (w * Complex.exp (Complex.I * (t : ℂ)))⁻¹ ^ n *
          ((((Complex.I * w) * (t : ℂ)) * u t) ^ m *
            g.eval (w * Complex.exp (Complex.I * (t : ℂ)))) := by ring
      _ = (w * Complex.exp (Complex.I * (t : ℂ)))⁻¹ ^ n *
          (((Complex.I * w) * (t : ℂ)) ^ m * u t ^ m *
            g.eval (w * Complex.exp (Complex.I * (t : ℂ)))) := by rw [mul_pow]
      _ = (w * Complex.exp (Complex.I * (t : ℂ)))⁻¹ ^ n *
          ((Complex.I * w) ^ m * (t : ℂ) ^ m * u t ^ m *
            g.eval (w * Complex.exp (Complex.I * (t : ℂ)))) := by rw [mul_pow]
      _ = ((t : ℂ) ^ m) * ((w * Complex.exp (Complex.I * (t : ℂ)))⁻¹ ^ n *
          (Complex.I * w) ^ m * u t ^ m * g.eval (w * Complex.exp (Complex.I * (t : ℂ)))) := by ring
      _ = (t : ℂ) ^ m * ψ t := rfl
  -- Since (w·eⁱᵗ) is on the unit circle, the hypothesis tells us (w·eⁱᵗ)⁻ⁿ·H(w·eⁱᵗ) is real.
  -- Hence tᵐ·ψ(t) is real for every t.
  have h_real : ∀ t : ℝ, ((t : ℂ) ^ m * ψ t).im = 0 := by
    intro t
    have hz := hpos (w * Complex.exp (Complex.I * (t : ℂ))) (hz_norm_one t)
    rcases hz with ⟨r, hr_nonneg, hr⟩
    have h_eq : (w * Complex.exp (Complex.I * (t : ℂ)))⁻¹ ^ n *
      H.eval (w * Complex.exp (Complex.I * (t : ℂ))) = (r : ℂ) := by
      calc
        (w * Complex.exp (Complex.I * (t : ℂ)))⁻¹ ^ n *
          H.eval (w * Complex.exp (Complex.I * (t : ℂ)))
            = ((w * Complex.exp (Complex.I * (t : ℂ))) ^ n)⁻¹ *
              H.eval (w * Complex.exp (Complex.I * (t : ℂ))) := by rw [inv_pow]
        _ = (r : ℂ) := hr
    have h_eq' : (t : ℂ) ^ m * ψ t = (r : ℂ) := by
      calc
        (t : ℂ) ^ m * ψ t = (w * Complex.exp (Complex.I * (t : ℂ)))⁻¹ ^ n *
          H.eval (w * Complex.exp (Complex.I * (t : ℂ))) := by symm; exact h_identity t
        _ = (r : ℂ) := h_eq
    rw [h_eq']
    simp
  -- By psi_real, ψ(t) is real for all t
  have h_ψ_real : ∀ t : ℝ, (ψ t).im = 0 :=
    psi_real hψ_cont m h_real
  -- Define φ(t) = Re ψ(t), a continuous ℝ → ℝ function
  set φ : ℝ → ℝ := fun t => (ψ t).re with hφ
  have hφ_cont : Continuous φ :=
    Complex.continuous_re.comp hψ_cont
  have hφ0_ne_zero : φ 0 ≠ 0 := by
    intro hzero
    apply hψ0_ne_zero
    have h_im_zero : (ψ 0).im = 0 := h_ψ_real 0
    exact Complex.ext (by simpa [hφ] using hzero) h_im_zero
  have h_nonneg : ∀ t : ℝ, 0 ≤ (t : ℝ) ^ m * φ t := by
    intro t
    have hz := hpos (w * Complex.exp (Complex.I * (t : ℂ))) (hz_norm_one t)
    rcases hz with ⟨r, hr_nonneg, hr⟩
    have h_eq_complex : (t : ℂ) ^ m * ψ t = (r : ℂ) := by
      calc
        (t : ℂ) ^ m * ψ t = (w * Complex.exp (Complex.I * (t : ℂ)))⁻¹ ^ n *
          H.eval (w * Complex.exp (Complex.I * (t : ℂ))) := by
          symm; exact h_identity t
        _ = ((w * Complex.exp (Complex.I * (t : ℂ))) ^ n)⁻¹ *
          H.eval (w * Complex.exp (Complex.I * (t : ℂ))) := by rw [inv_pow]
        _ = (r : ℂ) := hr
    have h_re_eq : ((t : ℂ) ^ m * ψ t).re = (t : ℝ) ^ m * φ t := by
      have h_im_t : ((t : ℂ) ^ m).im = 0 := by
        simpa [Complex.ofReal_pow] using Complex.ofReal_im (t ^ m)
      have h_im_ψ : (ψ t).im = 0 := h_ψ_real t
      calc
        ((t : ℂ) ^ m * ψ t).re = ((t : ℂ) ^ m).re * (ψ t).re - ((t : ℂ) ^ m).im * (ψ t).im :=
          Complex.mul_re _ _
        _ = ((t : ℂ) ^ m).re * (ψ t).re := by
          rw [h_im_t, h_im_ψ, zero_mul, sub_zero]
        _ = (t : ℝ) ^ m * (ψ t).re := by
          have h_re_t : ((t : ℂ) ^ m).re = (t : ℝ) ^ m := by
            simpa [Complex.ofReal_pow] using (Complex.ofReal_re (t ^ m))
          rw [h_re_t]
        _ = (t : ℝ) ^ m * φ t := rfl
    rw [h_eq_complex] at h_re_eq
    have h_re_r : ((r : ℂ).re : ℝ) = r := by simp
    rw [h_re_r] at h_re_eq
    rw [← h_re_eq]
    exact hr_nonneg
  have h_nonneg_nhds : ∀ᶠ t in nhds (0 : ℝ), 0 ≤ (t : ℝ) ^ m * φ t :=
    Filter.Eventually.of_forall h_nonneg
  exact nonneg_even_order hφ_cont hφ0_ne_zero m h_nonneg_nhds

end ComplexAnalysis
end LeanEval
/-!
The Fejér–Riesz factorization: a nonzero self-inversive polynomial that is nonnegative on the
circle (after the `z⁻ⁿ` twist) factors as `Q · Q^{†n}` with `deg Q ≤ n`. Helper file for
`LeanEval.ComplexAnalysis.ComplementaryPolynomials`.
-/

namespace LeanEval
namespace ComplexAnalysis

open Polynomial

/-- Two nonzero polynomials with equal leading coefficient and equal root multiset are equal. -/
theorem eq_of_leadingCoeff_roots {F G : ℂ[X]} (_hF : F ≠ 0) (_hG : G ≠ 0)
    (hlc : F.leadingCoeff = G.leadingCoeff) (hroots : F.roots = G.roots) : F = G := by
  have hF_root_card : Multiset.card F.roots = F.natDegree := by
    simpa using IsAlgClosed.card_roots_eq_natDegree (p := F) (k := ℂ)
  have hG_root_card : Multiset.card G.roots = G.natDegree := by
    simpa using IsAlgClosed.card_roots_eq_natDegree (p := G) (k := ℂ)
  have hF_eq : C F.leadingCoeff * (F.roots.map fun a => X - C a).prod = F :=
    Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hF_root_card
  have hG_eq : C G.leadingCoeff * (G.roots.map fun a => X - C a).prod = G :=
    Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hG_root_card
  calc
    F = C F.leadingCoeff * (F.roots.map fun a => X - C a).prod := by
      symm; exact hF_eq
    _ = C G.leadingCoeff * (G.roots.map fun a => X - C a).prod := by
      rw [hlc, hroots]
    _ = G := hG_eq

/-- The inversion–conjugation map `σ(w) = 1 / conj(w)` on `ℂ`. -/
noncomputable def invConj (w : ℂ) : ℂ := (starRingEnd ℂ w)⁻¹

/-- `σ` is an involution on `ℂ⁰`, with fixed points exactly the unit circle. -/
theorem invConj_invConj {w : ℂ} (hw : w ≠ 0) :
    invConj (invConj w) = w ∧ (invConj w = w ↔ ‖w‖ = 1) := by
  have h1 : invConj (invConj w) = w := by
    dsimp [invConj]
    calc
      (starRingEnd ℂ ((starRingEnd ℂ w)⁻¹))⁻¹ = (((starRingEnd ℂ (starRingEnd ℂ w))⁻¹))⁻¹ := by
        rw [Complex.conj_inv (starRingEnd ℂ w)]
      _ = (w⁻¹)⁻¹ := by simp
      _ = w := by simp
  have h2 : invConj w = w ↔ ‖w‖ = 1 := by
    dsimp [invConj]
    constructor
    · intro h
      have hstar : starRingEnd ℂ w ≠ 0 := star_ne_zero.mpr hw
      field_simp [hstar] at h
      -- h : 1 = starRingEnd ℂ w * w
      have h_mul : starRingEnd ℂ w * w = (Complex.normSq w : ℂ) := by
        calc
          starRingEnd ℂ w * w = w * starRingEnd ℂ w := mul_comm _ _
          _ = (Complex.normSq w : ℂ) := Complex.mul_conj w
      rw [h_mul] at h
      -- h : 1 = (Complex.normSq w : ℂ)
      have h_normSq : Complex.normSq w = (1 : ℝ) := by
        exact_mod_cast h.symm
      have h_norm_sq_eq : Complex.normSq w = ‖w‖ ^ 2 := by
        simp [Complex.normSq_eq_norm_sq]
      rw [h_norm_sq_eq] at h_normSq
      have h_nonneg : 0 ≤ ‖w‖ := norm_nonneg _
      nlinarith
    · intro h
      have h_norm_sq : Complex.normSq w = (1 : ℝ) := by
        calc
          Complex.normSq w = ‖w‖ ^ 2 := by simp [Complex.normSq_eq_norm_sq]
          _ = 1 := by nlinarith
      have h_mul : starRingEnd ℂ w * w = 1 := by
        calc
          starRingEnd ℂ w * w = (Complex.normSq w : ℂ) := by
            calc
              starRingEnd ℂ w * w = w * starRingEnd ℂ w := mul_comm _ _
              _ = (Complex.normSq w : ℂ) := Complex.mul_conj w
          _ = (1 : ℂ) := by exact_mod_cast h_norm_sq
      have hstar : starRingEnd ℂ w ≠ 0 := star_ne_zero.mpr hw
      field_simp [hstar]
      -- goal: 1 = starRingEnd ℂ w * w
      rw [h_mul]
  exact And.intro h1 h2

/-- Size bound for the root half. -/
theorem fr_size_bound (n : ℕ) (H : ℂ[X]) (_hH0 : H ≠ 0) (hdeg : H.natDegree ≤ 2 * n)
    {S : Multiset ℂ} (hS : H.roots = S + S.map invConj) : S.card ≤ n := by
  have h_card_roots : H.roots.card = H.natDegree :=
    IsAlgClosed.card_roots_eq_natDegree (p := H)
  have h_card_map : (S.map invConj).card = S.card := Multiset.card_map invConj S
  have h_card_sum : (S + S.map invConj).card = S.card + (S.map invConj).card :=
    Multiset.card_add _ _
  have h_card_Hroots : H.roots.card = S.card + S.card := by
    calc
      H.roots.card = (S + S.map invConj).card := by rw [hS]
      _ = S.card + (S.map invConj).card := h_card_sum
      _ = S.card + S.card := by rw [h_card_map]
  have h_sum_le : S.card + S.card ≤ 2 * n := by
    calc
      S.card + S.card = H.roots.card := by symm; exact h_card_Hroots
      _ = H.natDegree := h_card_roots
      _ ≤ 2 * n := hdeg
  have h_two_mul : 2 * S.card = S.card + S.card := by rw [Nat.two_mul]
  have h_mul_le : 2 * S.card ≤ 2 * n := by
    calc
      2 * S.card = S.card + S.card := h_two_mul
      _ ≤ 2 * n := h_sum_le
  omega

/-- Leading coefficient of a scaled factor product and its conjugate-reciprocal. -/
theorem fr_leadingCoeff_conjRecip (n : ℕ) (c : ℂ) (hc : c ≠ 0) (S : Multiset ℂ)
    (hS : ∀ r ∈ S, r ≠ 0) (hcard : S.card ≤ n)
    (Q : ℂ[X]) (hQ : Q = C c * (S.map (fun r => X - C r)).prod)
    (ω : ℂ) (hω : ω = starRingEnd ℂ ((S.map (fun r => -r)).prod)) :
    ω ≠ 0 ∧
      (conjRecip n Q).leadingCoeff = starRingEnd ℂ c * ω ∧
      (conjRecip n Q).leadingCoeff = starRingEnd ℂ (Q.eval 0) ∧
      (Q * conjRecip n Q).leadingCoeff = ((‖c‖ ^ 2 : ℝ) : ℂ) * ω := by
  -- ω = conj(∏(-r)) where each r ≠ 0, so ω ≠ 0
  have h_no_zero : (0 : ℂ) ∉ S.map (fun r => -r) := by
    intro hzero
    rcases Multiset.mem_map.mp hzero with ⟨r, hr, h⟩
    have : r = 0 := by
      calc
        r = -(-r) := by simp
        _ = -(0 : ℂ) := by rw [h]
        _ = 0 := by simp
    exact hS r hr this
  have h_prod_ne_zero : (S.map (fun r => -r)).prod ≠ 0 :=
    Multiset.prod_ne_zero h_no_zero
  have h_omega_ne_zero : ω ≠ 0 := by
    rw [hω]
    intro hzero
    apply h_prod_ne_zero
    simpa using (star_eq_zero.mp hzero)

  -- Q.eval 0 = c * ∏(-r) (non-zero)
  have hQeval0 : Q.eval 0 = c * ((S.map (fun r => -r)).prod) := by
    rw [hQ]
    calc
      (C c * (S.map (fun r => X - C r)).prod).eval 0
          = c * ((S.map (fun r => X - C r)).prod).eval 0 := by simp
      _ = c * (((S.map (fun r => X - C r)).map (eval 0)).prod) := by
        rw [eval_multiset_prod]
      _ = c * ((S.map (fun r => (X - C r).eval 0)).prod) := by simp
      _ = c * ((S.map (fun r => -r)).prod) := by simp

  have hQeval0_ne_zero : Q.eval 0 ≠ 0 := by
    rw [hQeval0]
    exact mul_ne_zero hc h_prod_ne_zero

  have hQeval0_star_nonzero : starRingEnd ℂ (Q.eval 0) ≠ 0 := by
    exact mt star_eq_zero.mp hQeval0_ne_zero

  -- natDegree of the product (S.map (fun r => X - C r)).prod
  have hprod_natDegree : ((S.map (fun r => X - C r)).prod).natDegree = S.card := by
    have hmonic : ∀ f ∈ (S.map (fun r => X - C r)), Monic f := by
      intro f hf
      rcases Multiset.mem_map.mp hf with ⟨r, hr, rfl⟩
      exact Polynomial.monic_X_sub_C r
    calc
      ((S.map (fun r => X - C r)).prod).natDegree
          = ((S.map (fun r => X - C r)).map natDegree).sum :=
        Polynomial.natDegree_multiset_prod_of_monic (S.map (fun r => X - C r)) hmonic
      _ = (S.map (fun r => (X - C r).natDegree)).sum := by simp
      _ = (S.map (fun _ => 1)).sum := by simp
      _ = S.card := by simp

  have hQ_natDegree : Q.natDegree = S.card := by
    rw [hQ]
    have hprod_monic : ((S.map (fun r => X - C r)).prod).Monic :=
      Polynomial.monic_multiset_prod_of_monic S (fun r => X - C r) (by
        intro r hr; exact Polynomial.monic_X_sub_C r)
    have hprod_ne_zero_prod : (S.map (fun r => X - C r)).prod ≠ 0 :=
      hprod_monic.ne_zero
    have hC_ne_zero : C c ≠ 0 := Polynomial.C_ne_zero.mpr hc
    calc
      (C c * (S.map (fun r => X - C r)).prod).natDegree
          = (C c).natDegree + ((S.map (fun r => X - C r)).prod).natDegree :=
        Polynomial.natDegree_mul hC_ne_zero hprod_ne_zero_prod
      _ = 0 + S.card := by simp [hprod_natDegree]
      _ = S.card := by simp

  have hQ_natDegree_le_n : Q.natDegree ≤ n := by
    rw [hQ_natDegree]
    exact hcard

  have h_map_natDegree_le_n : (Q.map (starRingEnd ℂ)).natDegree ≤ n := by
    calc
      (Q.map (starRingEnd ℂ)).natDegree ≤ Q.natDegree :=
        Polynomial.natDegree_map_le
      _ ≤ n := hQ_natDegree_le_n

  have h_conj_natDegree_le_n : (conjRecip n Q).natDegree ≤ n := by
    calc
      (conjRecip n Q).natDegree = (reflect n (Q.map (starRingEnd ℂ))).natDegree := rfl
      _ ≤ max n ((Q.map (starRingEnd ℂ)).natDegree) := Polynomial.natDegree_reflect_le
      _ = n := max_eq_left h_map_natDegree_le_n

  -- coeff (conjRecip n Q) n = starRingEnd ℂ (Q.eval 0) ≠ 0
  have h_coeff_n_conj : coeff (conjRecip n Q) n = starRingEnd ℂ (Q.eval 0) := by
    calc
      coeff (conjRecip n Q) n = coeff (reflect n (Q.map (starRingEnd ℂ))) n := rfl
      _ = coeff (Q.map (starRingEnd ℂ)) (revAt n n) := by rw [Polynomial.coeff_reflect]
      _ = coeff (Q.map (starRingEnd ℂ)) 0 := by simp
      _ = starRingEnd ℂ (coeff Q 0) := by rw [Polynomial.coeff_map]
      _ = starRingEnd ℂ (Q.eval 0) := by rw [Polynomial.coeff_zero_eq_eval_zero]

  have h_coeff_n_conj_ne_zero : coeff (conjRecip n Q) n ≠ 0 := by
    rw [h_coeff_n_conj]
    exact hQeval0_star_nonzero

  have h_conj_natDegree : (conjRecip n Q).natDegree = n :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero h_conj_natDegree_le_n h_coeff_n_conj_ne_zero

  have h_leading_conj : (conjRecip n Q).leadingCoeff = coeff (conjRecip n Q) n := by
    calc
      (conjRecip n Q).leadingCoeff = coeff (conjRecip n Q) ((conjRecip n Q).natDegree) := rfl
      _ = coeff (conjRecip n Q) n := by rw [h_conj_natDegree]

  -- (conjRecip n Q).leadingCoeff = starRingEnd ℂ (Q.eval 0) = starRingEnd ℂ c * ω
  have h_part2 : (conjRecip n Q).leadingCoeff = starRingEnd ℂ c * ω := by
    calc
      (conjRecip n Q).leadingCoeff = starRingEnd ℂ (Q.eval 0) := by
        calc
          (conjRecip n Q).leadingCoeff = coeff (conjRecip n Q) n := h_leading_conj
          _ = starRingEnd ℂ (Q.eval 0) := h_coeff_n_conj
      _ = starRingEnd ℂ (c * ((S.map (fun r => -r)).prod)) := by rw [hQeval0]
      _ = starRingEnd ℂ c * starRingEnd ℂ ((S.map (fun r => -r)).prod) := by simp
      _ = starRingEnd ℂ c * ω := by rw [hω]

  have h_part3 : (conjRecip n Q).leadingCoeff = starRingEnd ℂ (Q.eval 0) := by
    calc
      (conjRecip n Q).leadingCoeff = coeff (conjRecip n Q) n := h_leading_conj
      _ = starRingEnd ℂ (Q.eval 0) := h_coeff_n_conj

  -- (Q * conjRecip n Q).leadingCoeff = (‖c‖^2 : ℂ) * ω
  have h_Q_leadingCoeff : Q.leadingCoeff = c := by
    rw [hQ]
    have hprod_monic : ((S.map (fun r => X - C r)).prod).Monic :=
      Polynomial.monic_multiset_prod_of_monic S (fun r => X - C r) (by
        intro r hr; exact Polynomial.monic_X_sub_C r)
    calc
      (C c * (S.map (fun r => X - C r)).prod).leadingCoeff
          = (C c).leadingCoeff * ((S.map (fun r => X - C r)).prod).leadingCoeff := by
        rw [Polynomial.leadingCoeff_mul]
      _ = c * 1 := by simp [hprod_monic.leadingCoeff]
      _ = c := by simp

  have h_part4 : (Q * conjRecip n Q).leadingCoeff = ((‖c‖ ^ 2 : ℝ) : ℂ) * ω := by
    calc
      (Q * conjRecip n Q).leadingCoeff = Q.leadingCoeff * (conjRecip n Q).leadingCoeff := by
        rw [Polynomial.leadingCoeff_mul]
      _ = c * (starRingEnd ℂ c * ω) := by rw [h_Q_leadingCoeff, h_part2]
      _ = (c * starRingEnd ℂ c) * ω := by ring
      _ = ((‖c‖ ^ 2 : ℝ) : ℂ) * ω := by
        have h_c_star : c * starRingEnd ℂ c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
          calc
            c * starRingEnd ℂ c = (c * starRingEnd ℂ c) := rfl
            _ = (starRingEnd ℂ c * c) := by ring
            _ = (Complex.normSq c : ℂ) := by
              simpa using (Complex.normSq_eq_conj_mul_self (z := c)).symm
            _ = ((Complex.normSq c : ℝ) : ℂ) := rfl
            _ = ((‖c‖ ^ 2 : ℝ) : ℂ) := by simp [Complex.normSq_eq_norm_sq]
        rw [h_c_star]
      _ = ((‖c‖ ^ 2 : ℝ) : ℂ) * ω := rfl

  exact And.intro h_omega_ne_zero (And.intro h_part2 (And.intro h_part3 h_part4))

-- `fejer_riesz` (the general factorization) is defined at the end of this file, after the
-- zero-root reduction lemmas (`fr_zero_factor`, `fr_zero_free`, `fr_recombine`) it depends on.

/-- Count form of the root pairing: roots of a self-inversive `H` are nonzero and `σ`-paired. -/
theorem fr_build_S_root_pairing (n : ℕ) (H : ℂ[X]) (hH0 : H ≠ 0) (hdeg : H.natDegree ≤ 2 * n)
    (hself : conjRecip (2 * n) H = H) (h0 : H.eval 0 ≠ 0) :
    (∀ r ∈ H.roots, r ≠ 0) ∧
      ∀ w : ℂ, w ≠ 0 → H.roots.count w = H.roots.count (invConj w) := by
  have h_roots_nonzero : ∀ r ∈ H.roots, r ≠ 0 := by
    intro r hr
    have h_isRoot : IsRoot H r := (Polynomial.mem_roots hH0).mp hr
    intro hzero
    have : H.eval 0 = 0 := by simpa [hzero] using h_isRoot
    exact h0 this
  have h_count_eq : ∀ w : ℂ, w ≠ 0 → H.roots.count w = H.roots.count (invConj w) := by
    intro w hw
    calc
      H.roots.count w = H.rootMultiplicity w := by rw [Polynomial.count_roots]
      _ = H.rootMultiplicity ((starRingEnd ℂ w)⁻¹) :=
        conjRecip_root_pairing n H hH0 hdeg hself hw
      _ = H.rootMultiplicity (invConj w) := rfl
      _ = H.roots.count (invConj w) := by rw [Polynomial.count_roots]
  exact And.intro h_roots_nonzero h_count_eq

/-- Partition of a multiset by modulus `< 1`, `= 1`, `> 1`. -/
theorem fr_build_S_partition (R : Multiset ℂ) :
    R = R.filter (fun r => ‖r‖ < 1) + R.filter (fun r => ‖r‖ = 1)
          + R.filter (fun r => ‖r‖ > 1) := by
  ext a
  simp [Multiset.count_add, Multiset.count_filter]
  by_cases hlt : ‖a‖ < 1
  · have h_not_eq : ‖a‖ ≠ 1 := by linarith
    have h_not_gt : ¬ 1 < ‖a‖ := by linarith
    simp [hlt, h_not_eq, h_not_gt]
  · by_cases heq : ‖a‖ = 1
    · simp [heq]
    · have hge : 1 ≤ ‖a‖ := not_lt.mp hlt
      have hgt : 1 < ‖a‖ := by
        by_contra! hle
        have : ‖a‖ = 1 := le_antisymm hle hge
        exact heq this
      simp [hlt, heq, hgt]

/-- Count transport across the modulus filters: `σ` carries the `> 1` part onto the `< 1` part and
fixes the circle part. -/
theorem fr_build_S_count_transport (R : Multiset ℂ) (hR : ∀ r ∈ R, r ≠ 0)
    (hcount : ∀ w : ℂ, w ≠ 0 → R.count w = R.count (invConj w)) :
    (∀ w : ℂ, (R.filter (fun r => ‖r‖ > 1)).count w
        = (R.filter (fun r => ‖r‖ < 1)).count (invConj w)) ∧
      ∀ w : ℂ, ‖w‖ = 1 → invConj w = w := by
  -- helper: on the unit circle, σ(w) = w
  have h_circle_fixed : ∀ w : ℂ, ‖w‖ = 1 → invConj w = w := by
    intro w hw
    have hw_ne_zero : w ≠ 0 := by
      intro hzero
      rw [hzero, norm_zero] at hw
      linarith
    have h_mul_conj_eq_one : w * starRingEnd ℂ w = (1 : ℂ) := by
      calc
        w * starRingEnd ℂ w = Complex.normSq w := Complex.mul_conj w
        _ = ((Complex.normSq w : ℝ) : ℂ) := rfl
        _ = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
          simp [Complex.normSq_eq_norm_sq]
        _ = ((1 : ℝ) : ℂ) := by simp [hw]
        _ = (1 : ℂ) := by norm_num
    have h_conj_eq_inv : starRingEnd ℂ w = w⁻¹ := by
      calc
        starRingEnd ℂ w = (1 : ℂ) * starRingEnd ℂ w := by simp
        _ = (w⁻¹ * w) * starRingEnd ℂ w := by field_simp [hw_ne_zero]
        _ = w⁻¹ * (w * starRingEnd ℂ w) := by ring
        _ = w⁻¹ * (1 : ℂ) := by rw [h_mul_conj_eq_one]
        _ = w⁻¹ := by simp
    calc
      invConj w = (starRingEnd ℂ w)⁻¹ := rfl
      _ = (w⁻¹)⁻¹ := by rw [h_conj_eq_inv]
      _ = w := by field_simp [hw_ne_zero]
  -- helper: ‖invConj w‖ = ‖w‖⁻¹ for w ≠ 0
  have h_norm_invConj (w : ℂ) (hw : w ≠ 0) : ‖invConj w‖ = ‖w‖⁻¹ := by
    simp [invConj, norm_inv]
  refine ⟨?_, h_circle_fixed⟩
  intro w
  rw [Multiset.count_filter, Multiset.count_filter]
  by_cases h_gt : ‖w‖ > 1
  · -- Case ‖w‖ > 1: both sides equal R.count (invConj w)
    have hw_ne_zero : w ≠ 0 := by
      intro hzero
      rw [hzero, norm_zero] at h_gt
      linarith
    have h_inv_norm_lt_one : ‖invConj w‖ < 1 := by
      rw [h_norm_invConj w hw_ne_zero]
      -- ‖w‖ > 1, so 0 < ‖w‖ and therefore ‖w‖⁻¹ < 1
      have hpos : 0 < ‖w‖ := by linarith
      have h_one_pos : (0 : ℝ) < 1 := by norm_num
      have h := (one_div_lt_one_div hpos h_one_pos).mpr h_gt
      simpa using h
    simp [h_gt, h_inv_norm_lt_one, hcount w hw_ne_zero]
  · -- Case ¬(‖w‖ > 1)
    have h_le : ‖w‖ ≤ 1 := by linarith
    by_cases hw0 : w = 0
    · subst w
      have h_invConj_zero : invConj (0 : ℂ) = 0 := by
        simp [invConj]
      have h0_not_mem : (0 : ℂ) ∉ R := by
        intro h; exact hR 0 h rfl
      have h0_count : R.count (0 : ℂ) = 0 := Multiset.count_eq_zero_of_notMem h0_not_mem
      simp [h_invConj_zero, h0_count]
    · have h_not_inv_lt_one : ¬ ‖invConj w‖ < 1 := by
        rw [h_norm_invConj w hw0]
        by_cases h_eq1 : ‖w‖ = 1
        · rw [h_eq1, inv_one]
          linarith
        · have h_lt1 : ‖w‖ < 1 := h_le.lt_of_ne h_eq1
          have h_pos : 0 < ‖w‖ := by
            -- w ≠ 0 and norm is nonnegative, so ‖w‖ > 0
            have h_nonzero_norm : ‖w‖ ≠ 0 := mt Complex.norm_eq_zero_iff.mp hw0
            have h_nonneg_norm : 0 ≤ ‖w‖ := norm_nonneg _
            exact lt_of_le_of_ne h_nonneg_norm h_nonzero_norm.symm
          have h_one_pos : (0 : ℝ) < 1 := by norm_num
          have h := (one_div_lt_one_div h_one_pos h_pos).mpr h_lt1
          -- h : 1 / 1 < 1 / ‖w‖, which simplifies to 1 < ‖w‖⁻¹
          have : 1 < ‖w‖⁻¹ := by simpa using h
          linarith
      simp [h_gt, h_not_inv_lt_one]

/-- A multiset with all-even counts has a half. -/
theorem exists_half_of_even_count {α : Type*} [DecidableEq α] (M : Multiset α)
    (h : ∀ w, Even (M.count w)) :
    ∃ T : Multiset α, T + T = M ∧ ∀ w, T.count w = M.count w / 2 := by
  induction M using Multiset.strongInductionOn with
  | _ M IH =>
    by_cases hM0 : M = 0
    · subst hM0
      exact ⟨0, by simp, by simp⟩
    · -- pick an element w ∈ M
      obtain ⟨w, hw⟩ := Multiset.exists_mem_of_ne_zero hM0
      have hw_pos : 0 < M.count w := Multiset.count_pos.mpr hw
      have hw_even : Even (M.count w) := h w
      -- count w is even and ≥ 1, hence ≥ 2
      have hw_ge2 : 2 ≤ M.count w := by
        rcases hw_even with ⟨k, hk⟩
        omega
      -- M' := M - replicate 2 w has strictly smaller card and all-even counts
      set M' := M - Multiset.replicate 2 w with hM'def
      have hcount' : ∀ a, M'.count a = M.count a - (Multiset.replicate 2 w).count a := by
        intro a
        rw [hM'def, Multiset.count_sub]
      have hcount'_w : M'.count w = M.count w - 2 := by
        rw [hcount' w]; simp
      have hcount'_ne : ∀ a, a ≠ w → M'.count a = M.count a := by
        intro a ha
        rw [hcount' a]; simp [ha]
      have hcard_lt : M' < M := by
        apply lt_of_le_of_ne (Multiset.sub_le_self _ _)
        intro heq
        have hcw := congrArg (Multiset.count w) heq
        rw [hcount'_w] at hcw
        omega
      have hM'_even : ∀ a, Even (M'.count a) := by
        intro a
        by_cases ha : a = w
        · subst ha
          rw [hcount'_w]
          rcases h a with ⟨k, hk⟩
          exact ⟨k - 1, by omega⟩
        · rw [hcount'_ne a ha]; exact h a
      obtain ⟨T', hT'add, hT'count⟩ := IH M' hcard_lt hM'_even
      refine ⟨w ::ₘ T', ?_, ?_⟩
      · -- (w ::ₘ T') + (w ::ₘ T') = M
        apply Multiset.ext.mpr
        intro a
        by_cases ha : a = w
        · subst ha
          rw [Multiset.count_add, Multiset.count_cons_self]
          have : T'.count a + T'.count a = M'.count a := by
            have := congrArg (Multiset.count a) hT'add
            rwa [Multiset.count_add] at this
          omega
        · rw [Multiset.count_add, Multiset.count_cons_of_ne ha]
          have : T'.count a + T'.count a = M'.count a := by
            have := congrArg (Multiset.count a) hT'add
            rwa [Multiset.count_add] at this
          rw [hcount'_ne a ha] at this
          omega
      · intro a
        by_cases ha : a = w
        · subst ha
          rw [Multiset.count_cons_self, hT'count a, hcount'_w]
          rcases h a with ⟨k, hk⟩
          omega
        · rw [Multiset.count_cons_of_ne ha, hT'count a, hcount'_ne a ha]

/-- The circle part of the root multiset has all-even counts and a `σ`-invariant half. -/
theorem fr_build_S_circle_half (n : ℕ) (H : ℂ[X]) (hH0 : H ≠ 0) (_hdeg : H.natDegree ≤ 2 * n)
    (_hself : conjRecip (2 * n) H = H) (hpos : NonnegRealOnCircle n H) :
    (∀ w : ℂ, Even ((H.roots.filter (fun r => ‖r‖ = 1)).count w)) ∧
      ∃ T : Multiset ℂ, T + T = H.roots.filter (fun r => ‖r‖ = 1) ∧
        (∀ w : ℂ, T.count w = (H.roots.filter (fun r => ‖r‖ = 1)).count w / 2) ∧
        T.map invConj = T := by
  set F := H.roots.filter (fun r => ‖r‖ = 1) with hF
  have hF_circle : ∀ r ∈ F, ‖r‖ = 1 := by
    intro r hr
    exact (Multiset.mem_filter.mp hr).2
  have h_even_all : ∀ w : ℂ, Even (F.count w) := by
    intro w
    by_cases hw_circle : ‖w‖ = 1
    · have hcount_eq : F.count w = H.rootMultiplicity w := by
        calc
          F.count w = (H.roots.filter (fun r => ‖r‖ = 1)).count w := rfl
          _ = H.roots.count w := Multiset.count_filter_of_pos hw_circle
          _ = H.rootMultiplicity w := by rw [Polynomial.count_roots]
      rw [hcount_eq]
      exact circle_root_even n H hH0 hpos hw_circle
    · have hcount0 : F.count w = 0 := Multiset.count_filter_of_neg hw_circle
      rw [hcount0]
      exact ⟨0, by simp⟩
  rcases exists_half_of_even_count F h_even_all with ⟨T, hTadd, hTcount⟩
  have hTmap_invConj_eq : T.map invConj = T := by
    have hT_circle : ∀ r ∈ T, ‖r‖ = 1 := by
      intro r hr
      have hmem : r ∈ T + T := Multiset.mem_add.mpr (Or.inl hr)
      rw [hTadd] at hmem
      exact hF_circle r hmem
    have h_invConj_fix : ∀ r ∈ T, invConj r = r := by
      intro r hr
      have hcircle := hT_circle r hr
      have h_ne_zero : r ≠ 0 := by
        intro hzero
        rw [hzero] at hcircle
        norm_num at hcircle
      exact ((invConj_invConj h_ne_zero).2).mpr hcircle
    calc
      T.map invConj = T.map (fun x : ℂ => x) := Multiset.map_congr rfl h_invConj_fix
      _ = T := Multiset.map_id T
  exact ⟨h_even_all, T, hTadd, hTcount, hTmap_invConj_eq⟩

/-- `invConj` is injective on `ℂ`: it is complex inversion composed with conjugation. -/
private theorem invConj_injective : Function.Injective invConj := by
  intro a b h
  have h' : (starRingEnd ℂ a)⁻¹ = (starRingEnd ℂ b)⁻¹ := h
  have h'' : starRingEnd ℂ a = starRingEnd ℂ b := inv_injective h'
  rw [starRingEnd_apply, starRingEnd_apply] at h''
  exact star_injective h''

/-- `invConj` sends `0` to `0`. -/
private theorem invConj_zero : invConj (0 : ℂ) = 0 := by
  simp [invConj]

/-- Counting through a `map invConj`, for multisets with no zero elements:
`(A.map invConj).count w = A.count (invConj w)`. -/
private theorem count_map_invConj (A : Multiset ℂ) (hA : ∀ r ∈ A, r ≠ 0) (w : ℂ) :
    (A.map invConj).count w = A.count (invConj w) := by
  by_cases hw : w = 0
  · -- both sides are zero: `A` has no zeros and `invConj` of a nonzero is nonzero
    subst hw
    have hL : (A.map invConj).count 0 = 0 := by
      rw [Multiset.count_eq_zero]
      intro hmem
      rcases Multiset.mem_map.mp hmem with ⟨r, hr, hrw⟩
      have hr0 : r ≠ 0 := hA r hr
      have : invConj r ≠ 0 := by
        intro hc
        apply hr0
        have := invConj_injective (by rw [hc, invConj_zero] : invConj r = invConj 0)
        exact this
      exact this hrw
    have hR : A.count (invConj 0) = 0 := by
      rw [invConj_zero, Multiset.count_eq_zero]
      intro hmem
      exact hA 0 hmem rfl
    rw [hL, hR]
  · -- nonzero: use injectivity and the involution `invConj (invConj w) = w`
    have hinv : invConj (invConj w) = w := (invConj_invConj hw).1
    calc
      (A.map invConj).count w
          = (A.map invConj).count (invConj (invConj w)) := by rw [hinv]
      _ = A.count (invConj w) :=
        Multiset.count_map_eq_count' invConj A invConj_injective (invConj w)

/-- Halving the root multiset of a self-inversive, circle-nonnegative polynomial. -/
theorem fr_build_S (n : ℕ) (H : ℂ[X]) (hH0 : H ≠ 0) (hdeg : H.natDegree ≤ 2 * n)
    (hself : conjRecip (2 * n) H = H) (hpos : NonnegRealOnCircle n H) (h0 : H.eval 0 ≠ 0) :
    ∃ S : Multiset ℂ, (∀ r ∈ S, r ≠ 0) ∧ H.roots = S + S.map invConj := by
  set R := H.roots with hRdef
  -- root pairing: roots are nonzero and `σ`-count-symmetric
  obtain ⟨hR_nonzero, hR_count⟩ := fr_build_S_root_pairing n H hH0 hdeg hself h0
  -- count transport: `> 1` part maps onto `< 1` part; circle part is fixed
  obtain ⟨h_transport, _h_circle_fixed⟩ := fr_build_S_count_transport R hR_nonzero hR_count
  -- circle half: a `σ`-invariant `T` with `T + T = (R.filter (‖·‖ = 1))`
  obtain ⟨_h_even, T, hTadd, _hTcount, hTmap⟩ :=
    fr_build_S_circle_half n H hH0 hdeg hself hpos
  -- name the three modulus pieces
  set Rlt := R.filter (fun r => ‖r‖ < 1) with hRlt
  set Req := R.filter (fun r => ‖r‖ = 1) with hReq
  set Rgt := R.filter (fun r => ‖r‖ > 1) with hRgt
  -- the candidate half
  refine ⟨Rlt + T, ?_, ?_⟩
  · -- every element of `Rlt + T` is nonzero
    intro r hr
    rcases Multiset.mem_add.mp hr with hr | hr
    · exact hR_nonzero r (Multiset.mem_of_mem_filter hr)
    · -- `T ≤ Req ≤ R`, so `r ∈ R`
      have hrEq : r ∈ Req := by
        rw [← hTadd]
        exact Multiset.mem_add.mpr (Or.inl hr)
      exact hR_nonzero r (Multiset.mem_of_mem_filter hrEq)
  · -- `H.roots = (Rlt + T) + (Rlt + T).map invConj`
    -- key: `Rlt.map invConj = Rgt` as multisets
    have h_Rlt_nonzero : ∀ r ∈ Rlt, r ≠ 0 := fun r hr =>
      hR_nonzero r (Multiset.mem_of_mem_filter hr)
    have h_map_Rlt : Rlt.map invConj = Rgt := by
      ext w
      rw [count_map_invConj Rlt h_Rlt_nonzero w]
      exact (h_transport w).symm
    -- expand the map of the candidate half
    have h_map_half : (Rlt + T).map invConj = Rgt + T := by
      rw [Multiset.map_add, h_map_Rlt, hTmap]
    -- assemble and compare with the partition
    have h_partition : R = Rlt + Req + Rgt := fr_build_S_partition R
    have h_TT : T + T = Req := hTadd
    -- finish by `count` arithmetic
    rw [h_partition]
    rw [h_map_half]
    ext w
    simp only [Multiset.count_add]
    have : Req.count w = T.count w + T.count w := by
      rw [← Multiset.count_add, h_TT]
    rw [this]
    omega

/-- The Fejér–Riesz root multiset. -/
theorem fr_multiset (n : ℕ) (H : ℂ[X]) (hH0 : H ≠ 0) (hdeg : H.natDegree ≤ 2 * n)
    (hself : conjRecip (2 * n) H = H) (hpos : NonnegRealOnCircle n H) (h0 : H.eval 0 ≠ 0) :
    ∃ S : Multiset ℂ, S.card ≤ n ∧ (∀ r ∈ S, r ≠ 0) ∧ H.roots = S + S.map invConj := by
  rcases fr_build_S n H hH0 hdeg hself hpos h0 with ⟨S, hSzero, hroots⟩
  refine ⟨S, ?_, hSzero, hroots⟩
  exact fr_size_bound n H hH0 hdeg hroots

/-- Constant term of a top-degree self-inversive polynomial is the conjugate of its leading
coefficient (hence nonzero). -/
theorem fr_multiset_H0 (n : ℕ) (H : ℂ[X]) (hH0 : H ≠ 0) (_hdeg : H.natDegree ≤ 2 * n)
    (hself : conjRecip (2 * n) H = H) (hdegeq : H.natDegree = 2 * n) :
    H.eval 0 = starRingEnd ℂ H.leadingCoeff ∧ H.eval 0 ≠ 0 := by
  have hcoeff_symm : coeff H 0 = starRingEnd ℂ (coeff H (2 * n)) := by
    apply selfInversive_coeff_symm n H hself (j := 0)
    omega
  have hcoeff0_eval0 : coeff H 0 = H.eval 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
  have hcoeff_leading : coeff H (2 * n) = H.leadingCoeff := by
    calc
      coeff H (2 * n) = coeff H (H.natDegree) := by rw [hdegeq]
      _ = H.leadingCoeff := Polynomial.coeff_natDegree
  have h_eq : H.eval 0 = starRingEnd ℂ H.leadingCoeff := by
    calc
      H.eval 0 = coeff H 0 := by rw [Polynomial.coeff_zero_eq_eval_zero]
      _ = starRingEnd ℂ (coeff H (2 * n)) := hcoeff_symm
      _ = starRingEnd ℂ H.leadingCoeff := by rw [hcoeff_leading]
  have h_ne_zero : H.eval 0 ≠ 0 := by
    rw [h_eq]
    have h_lc_ne_zero : H.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hH0
    intro hzero
    apply h_lc_ne_zero
    exact star_injective (by simpa using hzero)
  exact ⟨h_eq, h_ne_zero⟩

/-- Multiplicity transport for the conjugate-reciprocal: mult of `w` in `Q^{†n}` equals mult of
`1/conj w = σ w` in `Q`. -/
theorem fr_complementary_mult (n : ℕ) (Q : ℂ[X]) (hQ0 : Q ≠ 0) (hQ : Q.natDegree ≤ n)
    {w : ℂ} (hw : w ≠ 0) :
    (conjRecip n Q).rootMultiplicity w = Q.rootMultiplicity (invConj w) := by
  unfold conjRecip
  have hmap_ne_zero : Q.map (starRingEnd ℂ) ≠ 0 := Polynomial.map_ne_zero hQ0
  have hmap_natDegree : (Q.map (starRingEnd ℂ)).natDegree ≤ n := by
    calc
      (Q.map (starRingEnd ℂ)).natDegree ≤ Q.natDegree := Polynomial.natDegree_map_le
      _ ≤ n := hQ
  calc
    (reflect n (Q.map (starRingEnd ℂ))).rootMultiplicity w
        = (Q.map (starRingEnd ℂ)).rootMultiplicity w⁻¹ :=
      rootMultiplicity_reflect n (Q.map (starRingEnd ℂ)) hmap_ne_zero hmap_natDegree hw
    _ = Q.rootMultiplicity (starRingEnd ℂ (w⁻¹)) := rootMultiplicity_map_conj Q (w⁻¹)
    _ = Q.rootMultiplicity ((starRingEnd ℂ w)⁻¹) := by simp
    _ = Q.rootMultiplicity (invConj w) := rfl

/-- Roots of a scaled product of linear factors. -/
theorem fr_roots_scaled_prod (c : ℂ) (hc : c ≠ 0) (S : Multiset ℂ) :
    (C c * (S.map (fun r => X - C r)).prod) ≠ 0 ∧
      (C c * (S.map (fun r => X - C r)).prod).roots = S := by
  have hprod_nonzero : (S.map (fun r => X - C r)).prod ≠ 0 :=
    Polynomial.Monic.ne_zero (Polynomial.monic_multiset_prod_of_monic S (fun r => X - C r) (fun r hr =>
      Polynomial.monic_X_sub_C r))
  have h_nonzero : C c * (S.map (fun r => X - C r)).prod ≠ 0 :=
    mul_ne_zero (Polynomial.C_ne_zero.mpr hc) hprod_nonzero
  have h_roots : (C c * (S.map (fun r => X - C r)).prod).roots = S := by
    calc
      (C c * (S.map (fun r => X - C r)).prod).roots = ((S.map (fun r => X - C r)).prod).roots := by
        rw [Polynomial.roots_C_mul _ hc]
      _ = S := by simp
  exact And.intro h_nonzero h_roots

/-- Root multiset of a scaled factor product and of its conjugate-reciprocal. -/
theorem fr_complementary_roots (n : ℕ) (c : ℂ) (hc : c ≠ 0) (S : Multiset ℂ)
    (hS : ∀ r ∈ S, r ≠ 0) (hcard : S.card = n) :
    (C c * (S.map (fun r => X - C r)).prod).roots = S ∧
      (conjRecip n (C c * (S.map (fun r => X - C r)).prod)).roots = S.map invConj := by
  set Q := C c * (S.map (fun r => X - C r)).prod with hQ_def
  -- first conjunct: roots of the scaled product
  obtain ⟨hQ0, hQroots⟩ := fr_roots_scaled_prod c hc S
  refine ⟨hQroots, ?_⟩
  -- Q.natDegree = S.card = n
  have hQnatDeg : Q.natDegree = n := by
    rw [hQ_def, Polynomial.natDegree_C_mul hc,
      Polynomial.natDegree_multiset_prod_X_sub_C_eq_card S, hcard]
  -- `invConj r ≠ 0` for `r ∈ S`
  have h_invConj_ne : ∀ r ∈ S, invConj r ≠ 0 := by
    intro r hr hzero
    have hr0 : r ≠ 0 := hS r hr
    apply hr0
    apply invConj_injective
    rw [hzero, invConj_zero]
  apply Multiset.ext.mpr
  intro w
  by_cases hw : w = 0
  · -- w = 0: neither side contains 0
    subst hw
    -- right side count is 0
    have hR : (S.map invConj).count 0 = 0 := by
      rw [Multiset.count_eq_zero]
      intro hmem
      rcases Multiset.mem_map.mp hmem with ⟨r, hr, hrw⟩
      exact h_invConj_ne r hr hrw
    -- left side count is 0: `0` is not a root of `conjRecip n Q` because its constant
    -- coefficient `coeff Q n = c ≠ 0` (after conjugation) is nonzero.
    have hL : (conjRecip n Q).roots.count 0 = 0 := by
      rw [Polynomial.count_roots]
      apply Polynomial.rootMultiplicity_eq_zero
      rw [Polynomial.zero_isRoot_iff_coeff_zero_eq_zero]
      -- coeff 0 of conjRecip n Q = starRingEnd ℂ (coeff Q n) = starRingEnd ℂ c ≠ 0
      have h_coeff0 : coeff (conjRecip n Q) 0 = coeff (Q.map (starRingEnd ℂ)) n := by
        calc
          coeff (conjRecip n Q) 0 = coeff (reflect n (Q.map (starRingEnd ℂ))) 0 := rfl
          _ = coeff (Q.map (starRingEnd ℂ)) (revAt n 0) := by rw [Polynomial.coeff_reflect]
          _ = coeff (Q.map (starRingEnd ℂ)) n := by simp
      rw [h_coeff0, Polynomial.coeff_map]
      -- coeff Q n = leadingCoeff Q = c ≠ 0
      have h_Qcoeff_n : coeff Q n = c := by
        rw [← hQnatDeg, Polynomial.coeff_natDegree, hQ_def]
        have hprod_monic : ((S.map (fun r => X - C r)).prod).Monic :=
          Polynomial.monic_multiset_prod_of_monic S (fun r => X - C r) (by
            intro r hr; exact Polynomial.monic_X_sub_C r)
        rw [Polynomial.leadingCoeff_mul]
        simp [hprod_monic.leadingCoeff]
      rw [h_Qcoeff_n]
      exact (mt star_eq_zero.mp hc)
    rw [hL, hR]
  · -- w ≠ 0
    rw [Polynomial.count_roots,
      fr_complementary_mult n Q hQ0 (le_of_eq hQnatDeg) hw,
      ← Polynomial.count_roots, hQroots,
      count_map_invConj S hS w]

/-- Roots of `Q · Q^{†n}` for a scaled factor product `Q = c ∏ (X - r)`. -/
theorem fr_complementary (n : ℕ) (c : ℂ) (hc : c ≠ 0) (S : Multiset ℂ)
    (hS : ∀ r ∈ S, r ≠ 0) (hcard : S.card = n) :
    ((C c * (S.map (fun r => X - C r)).prod) *
        conjRecip n (C c * (S.map (fun r => X - C r)).prod)).roots = S + S.map invConj := by
  set Q := C c * (S.map (fun r => X - C r)).prod with hQ_def
  obtain ⟨hQ0, hQroots⟩ := fr_roots_scaled_prod c hc S
  obtain ⟨hroots1, hroots2⟩ := fr_complementary_roots n c hc S hS hcard
  -- conjRecip n Q ≠ 0: its leading coefficient ω is nonzero
  have hconj_ne : conjRecip n Q ≠ 0 := by
    have h_full := fr_leadingCoeff_conjRecip n c hc S hS hcard.le Q hQ_def
      (starRingEnd ℂ ((S.map (fun r => -r)).prod)) rfl
    obtain ⟨hω_ne, hlc_eq, _, _⟩ := h_full
    intro hzero
    rw [hzero, Polynomial.leadingCoeff_zero] at hlc_eq
    exact (mul_ne_zero (mt star_eq_zero.mp hc) hω_ne) hlc_eq.symm
  rw [Polynomial.roots_mul (mul_ne_zero hQ0 hconj_ne), hroots1, hroots2]

/-- The matched factor `D = Q₀ · Q₀^{†n}`: nonzero, with `σ`-paired root multiset and leading
coefficient `ω`. -/
theorem fr_positive_multiple_D (n : ℕ) (S : Multiset ℂ) (hS : ∀ r ∈ S, r ≠ 0)
    (hcard : S.card = n) :
    let Q0 := (S.map (fun r => X - C r)).prod
    let D := Q0 * conjRecip n Q0
    let ω := starRingEnd ℂ ((S.map (fun r => -r)).prod)
    D ≠ 0 ∧ ω ≠ 0 ∧ D.roots = S + S.map invConj ∧ D.leadingCoeff = ω := by
  intro Q0 D ω
  have hc_ne_zero : (1 : ℂ) ≠ 0 := by norm_num
  -- ω ≠ 0 from fr_leadingCoeff_conjRecip with c = 1
  have h_omega_ne_zero : ω ≠ 0 := by
    have h_full := fr_leadingCoeff_conjRecip n (1 : ℂ) hc_ne_zero S hS hcard.le
      (C (1 : ℂ) * (S.map (fun r => X - C r)).prod) (by simp) ω rfl
    rcases h_full with ⟨hω_ne_zero, _, _, _⟩
    exact hω_ne_zero
  -- D.roots = S + S.map invConj from fr_complementary with c = 1
  have h_roots : D.roots = S + S.map invConj := by
    dsimp [D, Q0]
    simpa using fr_complementary n (1 : ℂ) hc_ne_zero S hS hcard
  -- D.leadingCoeff = ω from fr_leadingCoeff_conjRecip with c = 1
  have h_lc : D.leadingCoeff = ω := by
    dsimp [D, Q0]
    have h_full := fr_leadingCoeff_conjRecip n (1 : ℂ) hc_ne_zero S hS hcard.le
      (C (1 : ℂ) * (S.map (fun r => X - C r)).prod) (by simp) ω rfl
    rcases h_full with ⟨_, _, _, h_lc_prod⟩
    calc
      ((S.map (fun r => X - C r)).prod * conjRecip n ((S.map (fun r => X - C r)).prod)).leadingCoeff
          = ((C (1 : ℂ) * (S.map (fun r => X - C r)).prod) *
              conjRecip n (C (1 : ℂ) * (S.map (fun r => X - C r)).prod)).leadingCoeff := by simp
      _ = ((‖(1 : ℂ)‖ ^ 2 : ℝ) : ℂ) * ω := h_lc_prod
      _ = (1 : ℂ) * ω := by norm_num
      _ = ω := by simp
  -- D ≠ 0 because its leading coefficient ω is nonzero
  have h_D_ne_zero : D ≠ 0 := by
    intro hzero
    have hzero_lc : D.leadingCoeff = 0 := by
      simp [hzero]
    rw [h_lc] at hzero_lc
    exact h_omega_ne_zero hzero_lc
  exact ⟨h_D_ne_zero, h_omega_ne_zero, h_roots, h_lc⟩

/-- A circle point off the roots of a nonzero polynomial. -/
theorem fr_positive_multiple_point (H : ℂ[X]) (hH0 : H ≠ 0) :
    ∃ z0 : ℂ, ‖z0‖ = 1 ∧ H.eval z0 ≠ 0 := by
  -- (a) the unit circle is infinite
  have hcirc : {z : ℂ | ‖z‖ = 1}.Infinite := by
    have hIcc : (Set.Icc (0 : ℝ) 1).Infinite := by
      rw [← Set.infinite_coe_iff]
      exact Set.Icc.infinite (by norm_num)
    have hinj : Set.InjOn (fun t : ℝ => (Circle.exp t : ℂ)) (Set.Icc 0 1) := by
      intro x hx y hy hxy
      apply Circle.exp_injOn_Icc (a := 0) (b := 1) (by nlinarith [Real.pi_gt_three]) hx hy
      exact Circle.coe_injective hxy
    have himg : ((fun t : ℝ => (Circle.exp t : ℂ)) '' Set.Icc 0 1).Infinite :=
      hIcc.image hinj
    refine himg.mono ?_
    rintro z ⟨t, _, rfl⟩
    exact Circle.norm_coe _
  -- (b) the root set is finite
  have hfin : {z : ℂ | H.eval z = 0}.Finite := by
    have := Polynomial.finite_setOf_isRoot hH0
    simpa [Polynomial.IsRoot] using this
  -- (c) extract a circle point not in the (finite) root set
  obtain ⟨z0, hz0_circ, hz0_root⟩ := hcirc.exists_notMem_finite hfin
  exact ⟨z0, hz0_circ, hz0_root⟩

/-- The matched factor is a squared modulus on the circle: `z⁻ⁿ D(z) = ‖Q₀(z)‖²`. -/
theorem fr_D_eval_circle (n : ℕ) (S : Multiset ℂ) (hcard : S.card ≤ n) {z : ℂ} (hz : ‖z‖ = 1) :
    let Q0 := (S.map (fun r => X - C r)).prod
    (z ^ n)⁻¹ * (Q0 * conjRecip n Q0).eval z = ((‖Q0.eval z‖ ^ 2 : ℝ) : ℂ) := by
  intro Q0
  have hz_ne_zero : z ≠ 0 := by
    intro hzero
    have : ‖z‖ = 0 := by simp [hzero]
    rw [hz] at this
    norm_num at this
  have hQ0_natDegree : Q0.natDegree ≤ n := by
    calc
      Q0.natDegree = S.card := Polynomial.natDegree_multiset_prod_X_sub_C_eq_card S
      _ ≤ n := hcard
  have h_pow_ne_zero : z ^ n ≠ 0 := pow_ne_zero n hz_ne_zero
  calc
    (z ^ n)⁻¹ * (Q0 * conjRecip n Q0).eval z = (z ^ n)⁻¹ * (Q0.eval z * (conjRecip n Q0).eval z) := by
      rw [Polynomial.eval_mul]
    _ = (z ^ n)⁻¹ * (z ^ n * ((‖Q0.eval z‖ ^ 2 : ℝ) : ℂ)) := by
      rw [conjRecip_mul_eval n Q0 hQ0_natDegree hz]
    _ = ((z ^ n)⁻¹ * z ^ n) * ((‖Q0.eval z‖ ^ 2 : ℝ) : ℂ) := by ring
    _ = (1 : ℂ) * ((‖Q0.eval z‖ ^ 2 : ℝ) : ℂ) := by simp [h_pow_ne_zero]
    _ = ((‖Q0.eval z‖ ^ 2 : ℝ) : ℂ) := by simp

/-- Positivity of the scaling factor `λ` with `H = C λ · D`. -/
theorem fr_positive_multiple_lambda (n : ℕ) (H : ℂ[X]) (hH0 : H ≠ 0) (_hdeg : H.natDegree ≤ 2 * n)
    (_hself : conjRecip (2 * n) H = H) (hpos : NonnegRealOnCircle n H)
    (S : Multiset ℂ) (_hS : ∀ r ∈ S, r ≠ 0) (hcard : S.card ≤ n)
    (_hroots : H.roots = S + S.map invConj)
    (lam : ℂ)
    (hHeq : H = C lam *
      ((S.map (fun r => X - C r)).prod * conjRecip n (S.map (fun r => X - C r)).prod)) :
    ∃ r : ℝ, 0 < r ∧ lam = (r : ℂ) := by
  set Q0 := (S.map (fun r => X - C r)).prod with hQ0
  have hQ0_eval_ne_zero (z : ℂ) (hz : ‖z‖ = 1) (hz_ne : H.eval z ≠ 0) : Q0.eval z ≠ 0 := by
    intro hzero
    have hD_eval_zero : (Q0 * conjRecip n Q0).eval z = 0 := by
      simp [hzero, eval_mul]
    have hH_eval_zero : H.eval z = 0 := by
      rw [hHeq, eval_mul, eval_C, hD_eval_zero, mul_zero]
    exact hz_ne hH_eval_zero
  rcases fr_positive_multiple_point H hH0 with ⟨z0, hz0_norm, hz0_ne⟩
  have hz0_ne_zero : z0 ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hz0_norm
    norm_num at hz0_norm
  rcases hpos z0 hz0_norm with ⟨r, hr_nonneg, hr_eq⟩
  have hr_pos : 0 < r := by
    have h_nonzero : (z0 ^ n)⁻¹ * H.eval z0 ≠ 0 := by
      have h_pow_ne_zero : z0 ^ n ≠ 0 := pow_ne_zero n hz0_ne_zero
      have h_eval_ne_zero : H.eval z0 ≠ 0 := hz0_ne
      apply mul_ne_zero (inv_ne_zero h_pow_ne_zero) h_eval_ne_zero
    by_contra! hrle
    have hrzero : r = 0 := by linarith
    apply h_nonzero
    rw [hr_eq, hrzero]
    simp
  have hD_eq : (z0 ^ n)⁻¹ * (Q0 * conjRecip n Q0).eval z0 = ((‖Q0.eval z0‖ ^ 2 : ℝ) : ℂ) := by
    dsimp [Q0]
    exact fr_D_eval_circle n S hcard hz0_norm
  have hQ0_eval_ne_zero' : Q0.eval z0 ≠ 0 :=
    hQ0_eval_ne_zero z0 hz0_norm hz0_ne
  have h_norm_sq_pos : 0 < ‖Q0.eval z0‖ ^ 2 := by
    have h_nonzero_norm : ‖Q0.eval z0‖ ≠ 0 := mt norm_eq_zero.mp hQ0_eval_ne_zero'
    have hpos_norm : 0 < ‖Q0.eval z0‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm h_nonzero_norm)
    exact pow_pos hpos_norm 2
  have h_norm_sq_ne_zero : ((‖Q0.eval z0‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast h_norm_sq_pos.ne'
  have h_lam_eq : (r : ℂ) = lam * ((‖Q0.eval z0‖ ^ 2 : ℝ) : ℂ) := by
    calc
      (r : ℂ) = (z0 ^ n)⁻¹ * H.eval z0 := hr_eq.symm
      _ = (z0 ^ n)⁻¹ * ((C lam * (Q0 * conjRecip n Q0)).eval z0) := by rw [hHeq, hQ0]
      _ = (z0 ^ n)⁻¹ * (lam * (Q0 * conjRecip n Q0).eval z0) := by simp
      _ = lam * ((z0 ^ n)⁻¹ * (Q0 * conjRecip n Q0).eval z0) := by ring
      _ = lam * ((‖Q0.eval z0‖ ^ 2 : ℝ) : ℂ) := by rw [hD_eq]
  set t := r / (‖Q0.eval z0‖ ^ 2) with ht_def
  have ht_pos : 0 < t := div_pos hr_pos h_norm_sq_pos
  have hlam_real : lam = (t : ℂ) := by
    have h_eq' : lam * ((‖Q0.eval z0‖ ^ 2 : ℝ) : ℂ) = (r : ℂ) := by
      symm; exact h_lam_eq
    calc
      lam = lam * 1 := by simp
      _ = lam * (((‖Q0.eval z0‖ ^ 2 : ℝ) : ℂ) * ((‖Q0.eval z0‖ ^ 2 : ℝ) : ℂ)⁻¹) := by
        field_simp [h_norm_sq_ne_zero]
      _ = (lam * ((‖Q0.eval z0‖ ^ 2 : ℝ) : ℂ)) * ((‖Q0.eval z0‖ ^ 2 : ℝ) : ℂ)⁻¹ := by ring
      _ = (r : ℂ) * ((‖Q0.eval z0‖ ^ 2 : ℝ) : ℂ)⁻¹ := by rw [h_eq']
      _ = ((r : ℂ) / ((‖Q0.eval z0‖ ^ 2 : ℝ) : ℂ)) := by
        simp [div_eq_mul_inv]
      _ = ((r / (‖Q0.eval z0‖ ^ 2) : ℝ) : ℂ) := by
        simp
      _ = (t : ℂ) := rfl
  exact ⟨t, ht_pos, hlam_real⟩

/-- The leading coefficient of `H` is a positive real multiple of `ω`, and `H = λ · Q₀ · Q₀^{†n}`. -/
theorem fr_positive_multiple (n : ℕ) (H : ℂ[X]) (hH0 : H ≠ 0) (hdeg : H.natDegree ≤ 2 * n)
    (hself : conjRecip (2 * n) H = H) (hpos : NonnegRealOnCircle n H)
    (S : Multiset ℂ) (hS : ∀ r ∈ S, r ≠ 0) (hcard : S.card = n)
    (hroots : H.roots = S + S.map invConj) :
    ∃ lam : ℝ, 0 < lam ∧
      H.leadingCoeff = (lam : ℂ) * starRingEnd ℂ ((S.map (fun r => -r)).prod) ∧
      H = C (lam : ℂ) * ((S.map (fun r => X - C r)).prod *
            conjRecip n (S.map (fun r => X - C r)).prod) := by
  set Q0 := (S.map (fun r => X - C r)).prod with hQ0_def
  set D := Q0 * conjRecip n Q0 with hD_def
  set ω := starRingEnd ℂ ((S.map (fun r => -r)).prod) with hω_def
  obtain ⟨hD0, hω0, hDroots, hDlc⟩ := fr_positive_multiple_D n S hS hcard
  -- Define the complex scalar `lamC := H.leadingCoeff / ω`.
  set lamC := H.leadingCoeff / ω with hlamC_def
  have hHlc_ne : H.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hH0
  have hHlc_eq : H.leadingCoeff = lamC * ω := by
    rw [hlamC_def, div_mul_cancel₀]
    exact hω0
  -- `H = C lamC * D` via equal leading coeff and equal roots.
  have hClamD_ne : C lamC * D ≠ 0 := by
    apply mul_ne_zero _ hD0
    rw [Polynomial.C_ne_zero]
    rw [hlamC_def]
    exact div_ne_zero hHlc_ne hω0
  have hlc_eq : H.leadingCoeff = (C lamC * D).leadingCoeff := by
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hDlc, hHlc_eq]
  have hroots_eq : H.roots = (C lamC * D).roots := by
    have hlamC_ne : lamC ≠ 0 := by rw [hlamC_def]; exact div_ne_zero hHlc_ne hω0
    rw [Polynomial.roots_C_mul D hlamC_ne, hDroots, hroots]
  have hHeq : H = C lamC * D :=
    eq_of_leadingCoeff_roots hH0 hClamD_ne hlc_eq hroots_eq
  -- `fr_positive_multiple_lambda` upgrades `lamC` to a positive real.
  have hHeq' : H = C lamC * (Q0 * conjRecip n Q0) := by rw [hHeq, hD_def]
  obtain ⟨lam, hlam_pos, hlam_eq⟩ :=
    fr_positive_multiple_lambda n H hH0 hdeg hself hpos S hS hcard.le hroots lamC hHeq'
  refine ⟨lam, hlam_pos, ?_, ?_⟩
  · rw [hHlc_eq, hlam_eq]
  · rw [hHeq, hD_def, hlam_eq]

/-- A scaling `c` making the leading coefficients of `Q · Q^{†n}` and `H` match. -/
theorem fr_leading_coeff (n : ℕ) (H : ℂ[X]) (hH0 : H ≠ 0) (hdeg : H.natDegree ≤ 2 * n)
    (hself : conjRecip (2 * n) H = H) (hpos : NonnegRealOnCircle n H)
    (S : Multiset ℂ) (hS : ∀ r ∈ S, r ≠ 0) (hcard : S.card = n)
    (hroots : H.roots = S + S.map invConj) :
    ∃ c : ℂ, c ≠ 0 ∧
      ((C c * (S.map (fun r => X - C r)).prod) *
          conjRecip n (C c * (S.map (fun r => X - C r)).prod)).leadingCoeff = H.leadingCoeff := by
  -- From fr_positive_multiple we obtain lam > 0 such that H.leadingCoeff = lam · ω
  obtain ⟨lam, hlam_pos, h_hlc, h_H_eq⟩ :=
    fr_positive_multiple n H hH0 hdeg hself hpos S hS hcard hroots
  set ω := starRingEnd ℂ ((S.map (fun r => -r)).prod) with hω_def
  -- Choose c := sqrt(lam) (as ℂ), which is nonzero because lam > 0
  set c := (Real.sqrt lam : ℂ) with hc_def
  have hc_ne_zero : c ≠ 0 := by
    rw [hc_def]
    have hsqrt_pos : Real.sqrt lam > 0 := Real.sqrt_pos.mpr hlam_pos
    exact_mod_cast hsqrt_pos.ne'
  set Q := C c * (S.map (fun r => X - C r)).prod with hQ_def
  have h_conj := fr_leadingCoeff_conjRecip n c hc_ne_zero S hS hcard.le Q rfl ω rfl
  rcases h_conj with ⟨hω_ne_zero, _, _, h_qlc⟩
  -- h_qlc : (Q * conjRecip n Q).leadingCoeff = ((‖c‖ ^ 2 : ℝ) : ℂ) * ω
  have h_norm_sq_eq : (‖c‖ ^ 2 : ℝ) = lam := by
    calc
      (‖c‖ ^ 2 : ℝ) = Complex.normSq c := by
        symm; exact Complex.normSq_eq_norm_sq c
      _ = Complex.normSq (Real.sqrt lam : ℂ) := rfl
      _ = (Real.sqrt lam : ℝ) * (Real.sqrt lam : ℝ) := by
        simp
      _ = lam := by
        rw [Real.mul_self_sqrt (show 0 ≤ lam from by linarith)]
  refine ⟨c, hc_ne_zero, ?_⟩
  calc
    (Q * conjRecip n Q).leadingCoeff = ((‖c‖ ^ 2 : ℝ) : ℂ) * ω := h_qlc
    _ = (lam : ℂ) * ω := by
      simp [h_norm_sq_eq]
    _ = H.leadingCoeff := h_hlc.symm

/-- Fejér–Riesz factorization, zero-free core (`H(0) ≠ 0`). -/
theorem fr_zero_free (n : ℕ) (H : ℂ[X]) (hH0 : H ≠ 0) (hdeg : H.natDegree ≤ 2 * n)
    (hself : conjRecip (2 * n) H = H) (h0 : H.eval 0 ≠ 0) (hpos : NonnegRealOnCircle n H) :
    ∃ Q : ℂ[X], Q.natDegree ≤ n ∧ Q * conjRecip n Q = H := by
  rcases fr_multiset n H hH0 hdeg hself hpos h0 with ⟨S, hcard, hSzero, hroots⟩
  -- Derive `S.card = n` exactly: `H(0) ≠ 0` and self-inversiveness force `natDegree H = 2n`.
  have hcoeff0 : H.coeff 0 ≠ 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]; exact h0
  have hcoeff2n : H.coeff (2 * n) ≠ 0 := by
    have hsymm : H.coeff (2 * n) = starRingEnd ℂ (H.coeff (2 * n - 2 * n)) :=
      selfInversive_coeff_symm n H hself (j := 2 * n) (le_refl _)
    rw [Nat.sub_self] at hsymm
    rw [hsymm]
    exact star_ne_zero.mpr hcoeff0
  have hnatdeg : H.natDegree = 2 * n :=
    le_antisymm hdeg (Polynomial.le_natDegree_of_ne_zero hcoeff2n)
  have hrootcard : H.roots.card = 2 * S.card := by
    rw [hroots, Multiset.card_add, Multiset.card_map, Nat.two_mul]
  have hcardroots : H.roots.card = H.natDegree :=
    IsAlgClosed.card_roots_eq_natDegree (p := H)
  have hcardeq : S.card = n := by omega
  rcases fr_leading_coeff n H hH0 hdeg hself hpos S hSzero hcardeq hroots with ⟨c, hc0, hlc⟩
  set Q := C c * (S.map (fun r => X - C r)).prod with hQdef
  have hQnatDeg : Q.natDegree ≤ n := by
    calc
      Q.natDegree = ((S.map (fun r => X - C r)).prod).natDegree := by
        rw [hQdef, Polynomial.natDegree_C_mul hc0]
      _ = S.card := Polynomial.natDegree_multiset_prod_X_sub_C_eq_card S
      _ ≤ n := hcard
  have hProd0 : Q * conjRecip n Q ≠ 0 := by
    intro hzero
    have hzeroLC : (Q * conjRecip n Q).leadingCoeff = 0 := by simp [hzero]
    have h0lc : H.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hH0
    apply h0lc
    calc
      H.leadingCoeff = (Q * conjRecip n Q).leadingCoeff := by symm; exact hlc
      _ = 0 := hzeroLC
  have hrootsProduct : (Q * conjRecip n Q).roots = H.roots := by
    calc
      (Q * conjRecip n Q).roots = S + S.map invConj := by
        rw [hQdef]
        exact fr_complementary n c hc0 S hSzero hcardeq
      _ = H.roots := by rw [hroots]
  have hEq : Q * conjRecip n Q = H :=
    eq_of_leadingCoeff_roots hProd0 hH0 hlc hrootsProduct
  exact ⟨Q, hQnatDeg, hEq⟩

/-- Zero-multiplicity of a self-inversive polynomial: `k ≤ n` and `deg H = 2n - k`. -/
theorem fr_zero_mult_le (n : ℕ) (H : ℂ[X]) (hH0 : H ≠ 0) (hdeg : H.natDegree ≤ 2 * n)
    (hself : conjRecip (2 * n) H = H) :
    H.rootMultiplicity 0 ≤ n ∧ H.natDegree = 2 * n - H.rootMultiplicity 0 := by
  set k := H.rootMultiplicity 0 with hk_def
  have hXk_dvd : X ^ k ∣ H := by
    have hle : k ≤ H.rootMultiplicity 0 := le_refl _
    rw [Polynomial.le_rootMultiplicity_iff hH0 (a := 0) (n := k)] at hle
    have : (X : ℂ[X]) - C (0 : ℂ) = X := by simp
    simpa [this] using hle
  have hcoeff_lt_k : ∀ d < k, coeff H d = 0 := by
    rw [← Polynomial.X_pow_dvd_iff]
    exact hXk_dvd
  have hcoeff_k_ne_zero : coeff H k ≠ 0 := by
    by_contra hzero
    have hXkp1_dvd : X ^ (k + 1) ∣ H := by
      rw [Polynomial.X_pow_dvd_iff]
      intro d hd
      by_cases hd_lt_k : d < k
      · exact hcoeff_lt_k d hd_lt_k
      · have : d = k := by omega
        subst this
        exact hzero
    have h_not_le : ¬ (k + 1 ≤ H.rootMultiplicity 0) := by omega
    apply h_not_le
    rw [Polynomial.le_rootMultiplicity_iff hH0 (a := 0) (n := k + 1)]
    simpa [sub_eq_add_neg] using hXkp1_dvd
  have h_symm : ∀ j, j ≤ 2 * n → coeff H j = starRingEnd ℂ (coeff H (2 * n - j)) :=
    λ j hj => selfInversive_coeff_symm n H hself hj
  have hk_le_natDegree : k ≤ H.natDegree := by
    have hXk_natDegree : ((X : ℂ[X]) ^ k).natDegree = k := by simp
    rcases hXk_dvd with ⟨G, hG⟩
    have hXk_ne_zero : ((X : ℂ[X]) ^ k) ≠ 0 := by
      intro hzero
      have : H = 0 := by
        calc
          H = ((X : ℂ[X]) ^ k) * G := hG
          _ = 0 * G := by rw [hzero]
          _ = 0 := by simp
      exact hH0 this
    have hG_ne_zero : G ≠ 0 := by
      intro hzero
      rw [hzero, mul_zero] at hG
      exact hH0 hG
    have h_natDegree_mul : (((X : ℂ[X]) ^ k) * G).natDegree =
        ((X : ℂ[X]) ^ k).natDegree + G.natDegree :=
      Polynomial.natDegree_mul (R := ℂ) hXk_ne_zero hG_ne_zero
    have : H.natDegree = k + G.natDegree := by
      calc
        H.natDegree = (((X : ℂ[X]) ^ k) * G).natDegree := by rw [hG]
        _ = ((X : ℂ[X]) ^ k).natDegree + G.natDegree := h_natDegree_mul
        _ = k + G.natDegree := by simp
    omega
  have hk_le_2n : k ≤ 2 * n := by
    calc
      k ≤ H.natDegree := hk_le_natDegree
      _ ≤ 2 * n := hdeg
  have h_natDegree_le : H.natDegree ≤ 2 * n - k := by
    by_contra! hgt
    have hcoeff_natDegree_ne_zero : coeff H (H.natDegree) ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hH0
    have hcoeff_natDegree_eq_zero : coeff H (H.natDegree) = 0 := by
      by_cases hn : H.natDegree ≤ 2 * n
      · rw [h_symm H.natDegree hn]
        have hsub_lt_k : 2 * n - H.natDegree < k := by
          omega
        simp [hcoeff_lt_k (2 * n - H.natDegree) hsub_lt_k]
      · omega
    exact hcoeff_natDegree_ne_zero hcoeff_natDegree_eq_zero
  have h_natDegree_ge : 2 * n - k ≤ H.natDegree := by
    have hcoeff_2n_sub_k_ne_zero : coeff H (2 * n - k) ≠ 0 := by
      have h2n_sub_k_le_2n : 2 * n - k ≤ 2 * n := Nat.sub_le _ _
      rw [h_symm (2 * n - k) h2n_sub_k_le_2n]
      have h_eq : 2 * n - (2 * n - k) = k := by omega
      rw [h_eq]
      exact star_ne_zero.mpr hcoeff_k_ne_zero
    by_contra! hlt
    have hcoeff_zero : coeff H (2 * n - k) = 0 :=
      coeff_eq_zero_of_natDegree_lt hlt
    exact hcoeff_2n_sub_k_ne_zero hcoeff_zero
  have h_natDegree_eq : H.natDegree = 2 * n - k :=
    le_antisymm h_natDegree_le h_natDegree_ge
  have hk_le_n : k ≤ n := by
    rw [h_natDegree_eq] at hk_le_natDegree
    omega
  exact ⟨hk_le_n, h_natDegree_eq⟩

/-- Self-inversiveness of the zero-free quotient `H₁` in `H = Xᵏ · H₁`. -/
theorem fr_zero_factor_selfInv (n k : ℕ) (H H1 : ℂ[X]) (hself : conjRecip (2 * n) H = H)
    (hk : k ≤ n) (_hH1 : H1 ≠ 0) (hdeg1 : H1.natDegree ≤ 2 * (n - k))
    (hfact : H = X ^ k * H1) :
    conjRecip (2 * (n - k)) H1 = H1 := by
  have hXk_deg : (X ^ k : ℂ[X]).natDegree ≤ 2 * k := by
    have hXk_natDegree : (X ^ k : ℂ[X]).natDegree = k := by simp
    rw [hXk_natDegree]
    omega
  have h_sum_eq : 2 * n = 2 * k + 2 * (n - k) := by omega
  have h_mul : conjRecip (2 * n) (X ^ k * H1) = conjRecip (2 * k) (X ^ k) * conjRecip (2 * (n - k)) H1 := by
    rw [h_sum_eq]
    exact conjRecip_mul (2 * k) (2 * (n - k)) (X ^ k) H1 hXk_deg hdeg1
  have hH_self : conjRecip (2 * n) (X ^ k * H1) = X ^ k * H1 := by
    calc
      conjRecip (2 * n) (X ^ k * H1) = conjRecip (2 * n) H := by rw [hfact]
      _ = H := hself
      _ = X ^ k * H1 := hfact
  have hXk_conj : conjRecip (2 * k) (X ^ k) = X ^ k := by
    simpa using conjRecip_X_pow k
  have h_eq : X ^ k * H1 = X ^ k * conjRecip (2 * (n - k)) H1 := by
    calc
      X ^ k * H1 = conjRecip (2 * n) (X ^ k * H1) := by symm; exact hH_self
      _ = conjRecip (2 * k) (X ^ k) * conjRecip (2 * (n - k)) H1 := h_mul
      _ = X ^ k * conjRecip (2 * (n - k)) H1 := by rw [hXk_conj]
  have hXk_ne_zero : (X : ℂ[X]) ^ k ≠ 0 := pow_ne_zero k (by
    exact Polynomial.X_ne_zero)
  exact (mul_left_cancel₀ hXk_ne_zero h_eq).symm

/-- Nonnegativity transports to the zero-free quotient. -/
theorem fr_zero_factor_nonneg (n k : ℕ) (H H1 : ℂ[X]) (hk : k ≤ n) (hfact : H = X ^ k * H1)
    (hpos : NonnegRealOnCircle n H) : NonnegRealOnCircle (n - k) H1 := by
  intro z hz
  have hz_ne_zero : z ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hz
    norm_num at hz
  rcases hpos z hz with ⟨r, hr_nonneg, hr_eq⟩
  have h_H_eval : H.eval z = z ^ k * H1.eval z := by
    rw [hfact, eval_mul, eval_pow, eval_X]
  have hzn : z ^ n = z ^ (n - k) * z ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  have h_eq : (z ^ (n - k))⁻¹ * H1.eval z = (r : ℂ) := by
    calc
      (z ^ (n - k))⁻¹ * H1.eval z = (z ^ n)⁻¹ * (z ^ k * H1.eval z) := by
        rw [hzn]
        field_simp [pow_ne_zero (n - k) hz_ne_zero, pow_ne_zero k hz_ne_zero]
      _ = (z ^ n)⁻¹ * H.eval z := by rw [h_H_eval]
      _ = (r : ℂ) := hr_eq
  exact ⟨r, hr_nonneg, h_eq⟩

/-- Factoring out the zero of a self-inversive polynomial. -/
theorem fr_zero_factor (n : ℕ) (H : ℂ[X]) (hH0 : H ≠ 0) (hdeg : H.natDegree ≤ 2 * n)
    (hself : conjRecip (2 * n) H = H) (hpos : NonnegRealOnCircle n H) :
    H.rootMultiplicity 0 ≤ n ∧
      ∃ H1 : ℂ[X], H = X ^ (H.rootMultiplicity 0) * H1 ∧ H1.eval 0 ≠ 0 ∧
        H1.natDegree = 2 * (n - H.rootMultiplicity 0) ∧
        conjRecip (2 * (n - H.rootMultiplicity 0)) H1 = H1 ∧
        NonnegRealOnCircle (n - H.rootMultiplicity 0) H1 := by
  set k := H.rootMultiplicity 0 with hk_def
  rcases fr_zero_mult_le n H hH0 hdeg hself with ⟨hk_le_n, h_nd_eq⟩
  rcases Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd H hH0 (0 : ℂ) with ⟨H1, h_eq, h_not⟩
  have h_H1_eval0_ne : H1.eval 0 ≠ 0 := by
    intro hzero
    have hX_dvd : (X - C (0 : ℂ)) ∣ H1 := by
      have hd : X ∣ H1 := by
        rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
        exact hzero
      simpa using hd
    exact h_not hX_dvd
  have h_H_eq : H = X ^ k * H1 := by
    simpa using h_eq
  have h_H1_ne_zero : H1 ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at h_H_eq
    exact hH0 h_H_eq
  have h_H1_natDegree : H1.natDegree = 2 * (n - k) := by
    have h_Xk_ne_zero : (X : ℂ[X]) ^ k ≠ 0 := by simp
    have h_nd_mul : H.natDegree = k + H1.natDegree := by
      calc
        H.natDegree = (X ^ k * H1).natDegree := by rw [h_H_eq]
        _ = (X ^ k).natDegree + H1.natDegree :=
          Polynomial.natDegree_mul h_Xk_ne_zero h_H1_ne_zero
        _ = k + H1.natDegree := by simp
    have hk_le_2n : k ≤ 2 * n := by omega
    have h_eq_from_nd : k + H1.natDegree = 2 * n - k := by
      calc
        k + H1.natDegree = H.natDegree := by rw [h_nd_mul]
        _ = 2 * n - k := h_nd_eq
    have h_calc : H1.natDegree = 2 * n - 2 * k := by
      omega
    have : 2 * n - 2 * k = 2 * (n - k) := by
      omega
    rw [this] at h_calc
    exact h_calc
  have h_H1_natDegree_le : H1.natDegree ≤ 2 * (n - k) := by
    rw [h_H1_natDegree]
  have h_H1_selfInv : conjRecip (2 * (n - k)) H1 = H1 :=
    fr_zero_factor_selfInv n k H H1 hself hk_le_n h_H1_ne_zero h_H1_natDegree_le h_H_eq
  have h_H1_nonneg : NonnegRealOnCircle (n - k) H1 :=
    fr_zero_factor_nonneg n k H H1 hk_le_n h_H_eq hpos
  refine ⟨hk_le_n, H1, h_H_eq, h_H1_eval0_ne, h_H1_natDegree, h_H1_selfInv, h_H1_nonneg⟩

/-- Recombining the factorization: `Q := Xᵏ · Q₁` factors `H = Xᵏ · H₁`. -/
theorem fr_recombine (n k : ℕ) (H H1 Q1 : ℂ[X]) (hk : k ≤ n) (hfact : H = X ^ k * H1)
    (hQ1deg : Q1.natDegree ≤ n - k) (hQ1 : Q1 * conjRecip (n - k) Q1 = H1) :
    (X ^ k * Q1).natDegree ≤ n ∧ (X ^ k * Q1) * conjRecip n (X ^ k * Q1) = H := by
  have hXk_deg : (X ^ k : ℂ[X]).natDegree ≤ k := by
    simp
  have h_sum_eq : k + (n - k) = n := Nat.add_sub_cancel' hk
  have h_conj_k_Xk : conjRecip k (X ^ k) = (1 : ℂ[X]) := by
    unfold conjRecip
    calc
      reflect k ((X ^ k : ℂ[X]).map (starRingEnd ℂ)) = reflect k (X ^ k) := by simp
      _ = X ^ revAt k k := by rw [Polynomial.reflect_monomial]
      _ = X ^ (0 : ℕ) := by
        have hk_le_k : k ≤ k := le_refl k
        rw [Polynomial.revAt_le hk_le_k, Nat.sub_self]
      _ = 1 := by simp
  have h_mul_conj : conjRecip n (X ^ k * Q1) = conjRecip (n - k) Q1 := by
    calc
      conjRecip n (X ^ k * Q1) = conjRecip (k + (n - k)) (X ^ k * Q1) := by rw [h_sum_eq]
      _ = conjRecip k (X ^ k) * conjRecip (n - k) Q1 :=
        conjRecip_mul k (n - k) (X ^ k) Q1 hXk_deg hQ1deg
      _ = (1 : ℂ[X]) * conjRecip (n - k) Q1 := by rw [h_conj_k_Xk]
      _ = conjRecip (n - k) Q1 := by simp
  have h_deg : (X ^ k * Q1).natDegree ≤ n := by
    calc
      (X ^ k * Q1).natDegree ≤ (X ^ k).natDegree + Q1.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ k + (n - k) := add_le_add hXk_deg hQ1deg
      _ = n := h_sum_eq
  have h_prod : (X ^ k * Q1) * conjRecip n (X ^ k * Q1) = H := by
    calc
      (X ^ k * Q1) * conjRecip n (X ^ k * Q1) = (X ^ k * Q1) * conjRecip (n - k) Q1 := by rw [h_mul_conj]
      _ = X ^ k * (Q1 * conjRecip (n - k) Q1) := by ring
      _ = X ^ k * H1 := by rw [hQ1]
      _ = H := by rw [hfact]
  exact And.intro h_deg h_prod

/-- **Fejér–Riesz factorization.** A nonzero self-inversive polynomial that is nonnegative on the
circle (after the `z⁻ⁿ` twist) factors as `Q · Q^{†n}` with `deg Q ≤ n`. The general case is
reduced to the zero-free core `fr_zero_free` by factoring out the zero at the origin. -/
theorem fejer_riesz (n : ℕ) (H : ℂ[X]) (hH0 : H ≠ 0) (hdeg : H.natDegree ≤ 2 * n)
    (hself : conjRecip (2 * n) H = H) (hpos : NonnegRealOnCircle n H) :
    ∃ Q : ℂ[X], Q.natDegree ≤ n ∧ Q * conjRecip n Q = H := by
  obtain ⟨hk, H1, hfact, hH1_0, hH1_deg, hH1_self, hH1_pos⟩ :=
    fr_zero_factor n H hH0 hdeg hself hpos
  have hH1_ne : H1 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hfact
    exact hH0 hfact
  obtain ⟨Q1, hQ1deg, hQ1fact⟩ :=
    fr_zero_free (n - H.rootMultiplicity 0) H1 hH1_ne hH1_deg.le hH1_self hH1_0 hH1_pos
  obtain ⟨hQdeg, hQfact⟩ :=
    fr_recombine n (H.rootMultiplicity 0) H H1 Q1 hk hfact hQ1deg hQ1fact
  exact ⟨X ^ (H.rootMultiplicity 0) * Q1, hQdeg, hQfact⟩

end ComplexAnalysis
end LeanEval
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



end ComplexAnalysis
end LeanEval
