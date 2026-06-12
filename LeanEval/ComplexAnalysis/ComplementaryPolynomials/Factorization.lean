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
    (hself : conjRecip (2 * n) H = H) (hpos : NonnegRealOnCircle n H) (h0 : H.eval 0 ≠ 0) :
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

-- `fejer_riesz` (the general factorization) is defined at the end of this file, after the
-- zero-root reduction lemmas (`fr_zero_factor`, `fr_zero_free`, `fr_recombine`) it depends on.

/-- Count form of the root pairing: roots of a self-inversive `H` are nonzero and `σ`-paired. -/
theorem fr_build_S_root_pairing (n : ℕ) (H : ℂ[X]) (hH0 : H ≠ 0) (hdeg : H.natDegree ≤ 2 * n)
    (hself : conjRecip (2 * n) H = H) (h0 : H.eval 0 ≠ 0) :
    (∀ r ∈ H.roots, r ≠ 0) ∧
      ∀ w : ℂ, w ≠ 0 → H.roots.count w = H.roots.count (invConj w) := by
  sorry

/-- Partition of a multiset by modulus `< 1`, `= 1`, `> 1`. -/
theorem fr_build_S_partition (R : Multiset ℂ) :
    R = R.filter (fun r => ‖r‖ < 1) + R.filter (fun r => ‖r‖ = 1)
          + R.filter (fun r => ‖r‖ > 1) := by
  sorry

/-- Count transport across the modulus filters: `σ` carries the `> 1` part onto the `< 1` part and
fixes the circle part. -/
theorem fr_build_S_count_transport (R : Multiset ℂ) (hR : ∀ r ∈ R, r ≠ 0)
    (hcount : ∀ w : ℂ, w ≠ 0 → R.count w = R.count (invConj w)) :
    (∀ w : ℂ, (R.filter (fun r => ‖r‖ > 1)).count w
        = (R.filter (fun r => ‖r‖ < 1)).count (invConj w)) ∧
      ∀ w : ℂ, ‖w‖ = 1 → invConj w = w := by
  sorry

/-- A multiset with all-even counts has a half. -/
theorem exists_half_of_even_count {α : Type*} [DecidableEq α] (M : Multiset α)
    (h : ∀ w, Even (M.count w)) :
    ∃ T : Multiset α, T + T = M ∧ ∀ w, T.count w = M.count w / 2 := by
  sorry

/-- The circle part of the root multiset has all-even counts and a `σ`-invariant half. -/
theorem fr_build_S_circle_half (n : ℕ) (H : ℂ[X]) (hH0 : H ≠ 0) (hdeg : H.natDegree ≤ 2 * n)
    (hself : conjRecip (2 * n) H = H) (hpos : NonnegRealOnCircle n H) :
    (∀ w : ℂ, Even ((H.roots.filter (fun r => ‖r‖ = 1)).count w)) ∧
      ∃ T : Multiset ℂ, T + T = H.roots.filter (fun r => ‖r‖ = 1) ∧
        (∀ w : ℂ, T.count w = (H.roots.filter (fun r => ‖r‖ = 1)).count w / 2) ∧
        T.map invConj = T := by
  sorry

/-- Constant term of a top-degree self-inversive polynomial is the conjugate of its leading
coefficient (hence nonzero). -/
theorem fr_multiset_H0 (n : ℕ) (H : ℂ[X]) (hH0 : H ≠ 0) (hdeg : H.natDegree ≤ 2 * n)
    (hself : conjRecip (2 * n) H = H) (hdegeq : H.natDegree = 2 * n) :
    H.eval 0 = starRingEnd ℂ H.leadingCoeff ∧ H.eval 0 ≠ 0 := by
  sorry

/-- Multiplicity transport for the conjugate-reciprocal: mult of `w` in `Q^{†n}` equals mult of
`1/conj w = σ w` in `Q`. -/
theorem fr_complementary_mult (n : ℕ) (Q : ℂ[X]) (hQ0 : Q ≠ 0) (hQ : Q.natDegree ≤ n)
    {w : ℂ} (hw : w ≠ 0) :
    (conjRecip n Q).rootMultiplicity w = Q.rootMultiplicity (invConj w) := by
  sorry

/-- Roots of a scaled product of linear factors. -/
theorem fr_roots_scaled_prod (c : ℂ) (hc : c ≠ 0) (S : Multiset ℂ) :
    (C c * (S.map (fun r => X - C r)).prod) ≠ 0 ∧
      (C c * (S.map (fun r => X - C r)).prod).roots = S := by
  sorry

/-- Root multiset of a scaled factor product and of its conjugate-reciprocal. -/
theorem fr_complementary_roots (n : ℕ) (c : ℂ) (hc : c ≠ 0) (S : Multiset ℂ)
    (hS : ∀ r ∈ S, r ≠ 0) (hcard : S.card ≤ n) :
    (C c * (S.map (fun r => X - C r)).prod).roots = S ∧
      (conjRecip n (C c * (S.map (fun r => X - C r)).prod)).roots = S.map invConj := by
  sorry

/-- The matched factor `D = Q₀ · Q₀^{†n}`: nonzero, with `σ`-paired root multiset and leading
coefficient `ω`. -/
theorem fr_positive_multiple_D (n : ℕ) (S : Multiset ℂ) (hS : ∀ r ∈ S, r ≠ 0)
    (hcard : S.card ≤ n) :
    let Q0 := (S.map (fun r => X - C r)).prod
    let D := Q0 * conjRecip n Q0
    let ω := starRingEnd ℂ ((S.map (fun r => -r)).prod)
    D ≠ 0 ∧ ω ≠ 0 ∧ D.roots = S + S.map invConj ∧ D.leadingCoeff = ω := by
  sorry

/-- A circle point off the roots of a nonzero polynomial. -/
theorem fr_positive_multiple_point (H : ℂ[X]) (hH0 : H ≠ 0) :
    ∃ z0 : ℂ, ‖z0‖ = 1 ∧ H.eval z0 ≠ 0 := by
  sorry

/-- The matched factor is a squared modulus on the circle: `z⁻ⁿ D(z) = ‖Q₀(z)‖²`. -/
theorem fr_D_eval_circle (n : ℕ) (S : Multiset ℂ) (hcard : S.card ≤ n) {z : ℂ} (hz : ‖z‖ = 1) :
    let Q0 := (S.map (fun r => X - C r)).prod
    (z ^ n)⁻¹ * (Q0 * conjRecip n Q0).eval z = ((‖Q0.eval z‖ ^ 2 : ℝ) : ℂ) := by
  sorry

/-- Positivity of the scaling factor `λ` with `H = C λ · D`. -/
theorem fr_positive_multiple_lambda (n : ℕ) (H : ℂ[X]) (hH0 : H ≠ 0) (hdeg : H.natDegree ≤ 2 * n)
    (hself : conjRecip (2 * n) H = H) (hpos : NonnegRealOnCircle n H)
    (S : Multiset ℂ) (hS : ∀ r ∈ S, r ≠ 0) (hcard : S.card ≤ n)
    (hroots : H.roots = S + S.map invConj)
    (lam : ℂ)
    (hHeq : H = C lam *
      ((S.map (fun r => X - C r)).prod * conjRecip n (S.map (fun r => X - C r)).prod)) :
    ∃ r : ℝ, 0 < r ∧ lam = (r : ℂ) := by
  sorry

/-- Fejér–Riesz factorization, zero-free core (`H(0) ≠ 0`). -/
theorem fr_zero_free (n : ℕ) (H : ℂ[X]) (hH0 : H ≠ 0) (hdeg : H.natDegree ≤ 2 * n)
    (hself : conjRecip (2 * n) H = H) (h0 : H.eval 0 ≠ 0) (hpos : NonnegRealOnCircle n H) :
    ∃ Q : ℂ[X], Q.natDegree ≤ n ∧ Q * conjRecip n Q = H := by
  rcases fr_multiset n H hH0 hdeg hself hpos h0 with ⟨S, hcard, hSzero, hroots⟩
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

/-- Zero-multiplicity of a self-inversive polynomial: `k ≤ n` and `deg H = 2n - k`. -/
theorem fr_zero_mult_le (n : ℕ) (H : ℂ[X]) (hH0 : H ≠ 0) (hdeg : H.natDegree ≤ 2 * n)
    (hself : conjRecip (2 * n) H = H) :
    H.rootMultiplicity 0 ≤ n ∧ H.natDegree = 2 * n - H.rootMultiplicity 0 := by
  sorry

/-- Self-inversiveness of the zero-free quotient `H₁` in `H = Xᵏ · H₁`. -/
theorem fr_zero_factor_selfInv (n k : ℕ) (H H1 : ℂ[X]) (hself : conjRecip (2 * n) H = H)
    (hk : k ≤ n) (hH1 : H1 ≠ 0) (hdeg1 : H1.natDegree ≤ 2 * (n - k))
    (hfact : H = X ^ k * H1) :
    conjRecip (2 * (n - k)) H1 = H1 := by
  sorry

/-- Nonnegativity transports to the zero-free quotient. -/
theorem fr_zero_factor_nonneg (n k : ℕ) (H H1 : ℂ[X]) (hfact : H = X ^ k * H1)
    (hpos : NonnegRealOnCircle n H) : NonnegRealOnCircle (n - k) H1 := by
  sorry

/-- Factoring out the zero of a self-inversive polynomial. -/
theorem fr_zero_factor (n : ℕ) (H : ℂ[X]) (hH0 : H ≠ 0) (hdeg : H.natDegree ≤ 2 * n)
    (hself : conjRecip (2 * n) H = H) (hpos : NonnegRealOnCircle n H) :
    H.rootMultiplicity 0 ≤ n ∧
      ∃ H1 : ℂ[X], H = X ^ (H.rootMultiplicity 0) * H1 ∧ H1.eval 0 ≠ 0 ∧
        H1.natDegree = 2 * (n - H.rootMultiplicity 0) ∧
        conjRecip (2 * (n - H.rootMultiplicity 0)) H1 = H1 ∧
        NonnegRealOnCircle (n - H.rootMultiplicity 0) H1 := by
  sorry

/-- Recombining the factorization: `Q := Xᵏ · Q₁` factors `H = Xᵏ · H₁`. -/
theorem fr_recombine (n k : ℕ) (H H1 Q1 : ℂ[X]) (hk : k ≤ n) (hfact : H = X ^ k * H1)
    (hQ1deg : Q1.natDegree ≤ n - k) (hQ1 : Q1 * conjRecip (n - k) Q1 = H1) :
    (X ^ k * Q1).natDegree ≤ n ∧ (X ^ k * Q1) * conjRecip n (X ^ k * Q1) = H := by
  sorry

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
