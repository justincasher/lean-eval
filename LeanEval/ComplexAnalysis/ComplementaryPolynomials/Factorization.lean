import Mathlib
import EvalTools.Markers
import LeanEval.ComplexAnalysis.ComplementaryPolynomials.ConjugateReciprocal
import LeanEval.ComplexAnalysis.ComplementaryPolynomials.AuxiliaryG
import LeanEval.ComplexAnalysis.ComplementaryPolynomials.RootMultiplicity
import LeanEval.ComplexAnalysis.ComplementaryPolynomials.CircleRoots

/-!
The Fejér–Riesz factorization: a nonzero self-inversive polynomial that is nonnegative on the
circle (after the `z⁻ⁿ` twist) factors as `Q · Q^{†n}` with `deg Q ≤ n`. Helper file for
`LeanEval.ComplexAnalysis.ComplementaryPolynomials`.
-/

namespace LeanEval
namespace ComplexAnalysis

open Polynomial

/-- Two nonzero polynomials with equal leading coefficient and equal root multiset are equal. -/
theorem eq_of_leadingCoeff_roots {F G : ℂ[X]} (hF : F ≠ 0) (hG : G ≠ 0)
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
  sorry

/-- Halving the root multiset of a self-inversive, circle-nonnegative polynomial. -/
theorem fr_build_S (n : ℕ) (H : ℂ[X]) (hH0 : H ≠ 0) (hdeg : H.natDegree ≤ 2 * n)
    (hself : conjRecip (2 * n) H = H) (hpos : NonnegRealOnCircle n H) (h0 : H.eval 0 ≠ 0) :
    ∃ S : Multiset ℂ, (∀ r ∈ S, r ≠ 0) ∧ H.roots = S + S.map invConj := by
  sorry

/-- Size bound for the root half. -/
theorem fr_size_bound (n : ℕ) (H : ℂ[X]) (hH0 : H ≠ 0) (hdeg : H.natDegree ≤ 2 * n)
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

/-- The Fejér–Riesz root multiset. -/
theorem fr_multiset (n : ℕ) (H : ℂ[X]) (hH0 : H ≠ 0) (hdeg : H.natDegree ≤ 2 * n)
    (hself : conjRecip (2 * n) H = H) (hpos : NonnegRealOnCircle n H) :
    H.eval 0 ≠ 0 ∧
      ∃ S : Multiset ℂ, S.card ≤ n ∧ (∀ r ∈ S, r ≠ 0) ∧ H.roots = S + S.map invConj := by
  sorry

/-- Roots of `Q · Q^{†n}` for a scaled factor product `Q = c ∏ (X - r)`. -/
theorem fr_complementary (n : ℕ) (c : ℂ) (hc : c ≠ 0) (S : Multiset ℂ)
    (hS : ∀ r ∈ S, r ≠ 0) (hcard : S.card ≤ n) :
    ((C c * (S.map (fun r => X - C r)).prod) *
        conjRecip n (C c * (S.map (fun r => X - C r)).prod)).roots = S + S.map invConj := by
  sorry

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

/-- The leading coefficient of `H` is a positive real multiple of `ω`, and `H = λ · Q₀ · Q₀^{†n}`. -/
theorem fr_positive_multiple (n : ℕ) (H : ℂ[X]) (hH0 : H ≠ 0) (hdeg : H.natDegree ≤ 2 * n)
    (hself : conjRecip (2 * n) H = H) (hpos : NonnegRealOnCircle n H)
    (S : Multiset ℂ) (hS : ∀ r ∈ S, r ≠ 0) (hcard : S.card ≤ n)
    (hroots : H.roots = S + S.map invConj) :
    ∃ lam : ℝ, 0 < lam ∧
      H.leadingCoeff = (lam : ℂ) * starRingEnd ℂ ((S.map (fun r => -r)).prod) ∧
      H = C (lam : ℂ) * ((S.map (fun r => X - C r)).prod *
            conjRecip n (S.map (fun r => X - C r)).prod) := by
  sorry

/-- A scaling `c` making the leading coefficients of `Q · Q^{†n}` and `H` match. -/
theorem fr_leading_coeff (n : ℕ) (H : ℂ[X]) (hH0 : H ≠ 0) (hdeg : H.natDegree ≤ 2 * n)
    (hself : conjRecip (2 * n) H = H) (hpos : NonnegRealOnCircle n H)
    (S : Multiset ℂ) (hS : ∀ r ∈ S, r ≠ 0) (hcard : S.card ≤ n)
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
  have h_conj := fr_leadingCoeff_conjRecip n c hc_ne_zero S hS hcard Q rfl ω rfl
  rcases h_conj with ⟨hω_ne_zero, _, _, h_qlc⟩
  -- h_qlc : (Q * conjRecip n Q).leadingCoeff = ((‖c‖ ^ 2 : ℝ) : ℂ) * ω
  have h_norm_sq_eq : (‖c‖ ^ 2 : ℝ) = lam := by
    calc
      (‖c‖ ^ 2 : ℝ) = Complex.normSq c := by
        symm; exact Complex.normSq_eq_norm_sq c
      _ = Complex.normSq (Real.sqrt lam : ℂ) := rfl
      _ = (Real.sqrt lam : ℝ) * (Real.sqrt lam : ℝ) := by
        simpa using Complex.normSq_ofReal (Real.sqrt lam)
      _ = lam := by
        rw [Real.mul_self_sqrt (show 0 ≤ lam from by linarith)]
  refine ⟨c, hc_ne_zero, ?_⟩
  calc
    (Q * conjRecip n Q).leadingCoeff = ((‖c‖ ^ 2 : ℝ) : ℂ) * ω := h_qlc
    _ = (lam : ℂ) * ω := by
      simp [h_norm_sq_eq]
    _ = H.leadingCoeff := h_hlc.symm

/-- **Fejér–Riesz factorization.** A nonzero self-inversive polynomial that is nonnegative on the
circle (after the `z⁻ⁿ` twist) factors as `Q · Q^{†n}` with `deg Q ≤ n`. -/
theorem fejer_riesz (n : ℕ) (H : ℂ[X]) (hH0 : H ≠ 0) (hdeg : H.natDegree ≤ 2 * n)
    (hself : conjRecip (2 * n) H = H) (hpos : NonnegRealOnCircle n H) :
    ∃ Q : ℂ[X], Q.natDegree ≤ n ∧ Q * conjRecip n Q = H := by
  rcases fr_multiset n H hH0 hdeg hself hpos with ⟨h0ne, S, hcard, hSzero, hroots⟩
  rcases fr_leading_coeff n H hH0 hdeg hself hpos S hSzero hcard hroots with ⟨c, hc0, hlc⟩
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
        exact fr_complementary n c hc0 S hSzero hcard
      _ = H.roots := by rw [hroots]
  have hEq : Q * conjRecip n Q = H :=
    eq_of_leadingCoeff_roots hProd0 hH0 hlc hrootsProduct
  exact ⟨Q, hQnatDeg, hEq⟩

end ComplexAnalysis
end LeanEval
