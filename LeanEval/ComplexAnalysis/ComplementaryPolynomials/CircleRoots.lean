import Mathlib
import EvalTools.Markers
import LeanEval.ComplexAnalysis.ComplementaryPolynomials.ConjugateReciprocal
import LeanEval.ComplexAnalysis.ComplementaryPolynomials.AuxiliaryG
import LeanEval.ComplexAnalysis.ComplementaryPolynomials.RootMultiplicity

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
