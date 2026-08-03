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
