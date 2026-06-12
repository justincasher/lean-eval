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
  simpa using hmem'

/-- Nonnegativity of `tᵐ φ(t)` near `0` (with `φ(0) > 0`) forces `m` even. -/
theorem nonneg_even_order_pos {φ : ℝ → ℝ} (hφ : Continuous φ) (h0 : 0 < φ 0) (m : ℕ)
    (hnn : ∀ᶠ t in nhds (0 : ℝ), 0 ≤ t ^ m * φ t) : Even m := by
  sorry

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

/-- The slope of `eⁱᵗ - 1` at `0`: `(eⁱᵗ - 1)/(i t) → 1` as `t → 0` along `t ≠ 0`. -/
theorem exp_slope_tendsto :
    Filter.Tendsto
      (fun t : ℝ => (Complex.exp (Complex.I * (t : ℂ)) - 1) / (Complex.I * (t : ℂ)))
      (nhdsWithin (0 : ℝ) {0}ᶜ) (nhds 1) := by
  sorry

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
  sorry

/-- The reduced circle factor `ψ`: continuous, nonzero at `0`, and reducing `(w eⁱᵗ)⁻ⁿ H(w eⁱᵗ)`
to `tᵐ ψ(t)` for `H = (X - C w)ᵐ g`. -/
theorem circle_root_even_psi (w : ℂ) (hw : ‖w‖ = 1) (n m : ℕ) (g : ℂ[X]) (hg : g.eval w ≠ 0)
    (u : ℝ → ℂ) (hu_cont : Continuous u) (hu0 : u 0 = 1)
    (hu_id : ∀ t : ℝ, Complex.exp (Complex.I * (t : ℂ)) - 1 = Complex.I * (t : ℂ) * u t) :
    ∃ ψ : ℝ → ℂ,
      (∀ t : ℝ, ψ t = (w * Complex.exp (Complex.I * (t : ℂ)))⁻¹ ^ n *
          (Complex.I * w) ^ m * u t ^ m * g.eval (w * Complex.exp (Complex.I * (t : ℂ)))) ∧
      Continuous ψ ∧
      ψ 0 = w⁻¹ ^ n * (Complex.I * w) ^ m * g.eval w ∧
      ψ 0 ≠ 0 ∧
      (∀ t : ℝ, (w * Complex.exp (Complex.I * (t : ℂ)))⁻¹ ^ n *
        ((X - C w) ^ m * g).eval (w * Complex.exp (Complex.I * (t : ℂ))) = (t : ℂ) ^ m * ψ t) := by
  sorry

/-- A circle root of a circle-nonnegative polynomial has even multiplicity. -/
theorem circle_root_even (n : ℕ) (H : ℂ[X]) (hH : H ≠ 0) (hpos : NonnegRealOnCircle n H)
    {w : ℂ} (hw : ‖w‖ = 1) : Even (H.rootMultiplicity w) := by
  sorry

end ComplexAnalysis
end LeanEval
