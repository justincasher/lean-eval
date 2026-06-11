import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace LeanEval
namespace Analysis
namespace ODE

open scoped Real Topology

/-! ## Forward direction, case `λ ≤ 0`: convexity of `y²` -/

/-- First derivative of `y²`: the function `t ↦ y t * y t` has derivative `2 y(x) y'(x)`
at every `x ∈ J`. -/
lemma y_sq_first_deriv {y : ℝ → ℝ} {J : Set ℝ}
    (hy : ∀ x ∈ J, HasDerivAt y (deriv y x) x) {x : ℝ} (hx : x ∈ J) :
    HasDerivAt (fun t => y t * y t) (2 * y x * deriv y x) x := by
  have h := hy x hx
  have prod := h.mul h
  convert prod using 1
  ring

/-- Second derivative formula for `y²`: with `h(t) = 2 y(t) y'(t)`, the function `h` has
derivative `2 y'(x)² - 2 λ y(x)²` at each `x ∈ J`. -/
lemma y_sq_second_deriv_formula {y : ℝ → ℝ} {J : Set ℝ} {lam : ℝ}
    (hy : ∀ x ∈ J, HasDerivAt y (deriv y x) x)
    (hyy : ∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x)
    {x : ℝ} (hx : x ∈ J) :
    HasDerivAt (fun t => 2 * y t * deriv y t)
      (2 * deriv y x ^ 2 - 2 * lam * y x ^ 2) x := by
  have hyx := hy x hx
  have hyyx := hyy x hx
  have prod := hyx.mul hyyx
  have prod_simp : HasDerivAt (fun t => y t * deriv y t) (deriv y x ^ 2 - lam * y x ^ 2) x := by
    have h_eq : deriv y x * deriv y x + -(y x * (lam * y x)) = deriv y x ^ 2 - lam * y x ^ 2 := by ring
    simpa [Pi.mul_apply, h_eq] using prod
  have h := prod_simp.const_mul 2
  have h_eq2 : 2 * (deriv y x ^ 2 - lam * y x ^ 2) = 2 * deriv y x ^ 2 - 2 * lam * y x ^ 2 := by ring
  simpa [h_eq2, mul_assoc, mul_comm, mul_left_comm] using h

/-- Second derivative of `y²` is nonnegative when `λ ≤ 0`. -/
lemma y_sq_second_deriv_nonneg {y : ℝ → ℝ} {J : Set ℝ} {lam : ℝ}
    (hy : ∀ x ∈ J, HasDerivAt y (deriv y x) x)
    (hyy : ∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x)
    (hlam : lam ≤ 0) {x : ℝ} (hx : x ∈ J) :
    0 ≤ deriv (fun t => 2 * y t * deriv y t) x := by
  have hformula := y_sq_second_deriv_formula hy hyy hx
  have hderiv_eq : deriv (fun t => 2 * y t * deriv y t) x = (2 * deriv y x ^ 2 - 2 * lam * y x ^ 2) :=
    hformula.deriv
  rw [hderiv_eq]
  have h1 : 0 ≤ deriv y x ^ 2 := sq_nonneg _
  have h2 : 0 ≤ y x ^ 2 := sq_nonneg _
  have hlam_mul_sq2 : lam * y x ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hlam h2
  nlinarith

/-- `y²` is differentiable on `J`, with `deriv (y²) x = 2 y(x) y'(x)`. -/
lemma y_sq_differentiableOn_J {y : ℝ → ℝ} {J : Set ℝ}
    (hy : ∀ x ∈ J, HasDerivAt y (deriv y x) x) :
    DifferentiableOn ℝ (fun x => y x * y x) J ∧
      ∀ x ∈ J, deriv (fun t => y t * y t) x = 2 * y x * deriv y x := by
  have hdiff : DifferentiableOn ℝ (fun t => y t * y t) J := by
    intro x hx
    have h := y_sq_first_deriv hy hx
    exact h.differentiableAt.differentiableWithinAt
  have hderiv : ∀ x ∈ J, deriv (fun t => y t * y t) x = 2 * y x * deriv y x := by
    intro x hx
    have h := y_sq_first_deriv hy hx
    exact h.deriv
  exact ⟨hdiff, hderiv⟩

/-- `deriv (y²)` is differentiable on `J`. -/
lemma y_sq_deriv_differentiableOn_J {y : ℝ → ℝ} {J : Set ℝ} {lam : ℝ}
    (hJ : IsOpen J)
    (hy : ∀ x ∈ J, HasDerivAt y (deriv y x) x)
    (hyy : ∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x) :
    DifferentiableOn ℝ (deriv (fun x => y x * y x)) J := by
  have h_sq := y_sq_differentiableOn_J hy
  rcases h_sq with ⟨_, hderiv⟩
  intro x hx
  have h_eq : deriv (fun t => y t * y t) =ᶠ[𝓝 x] (fun t => 2 * y t * deriv y t) := by
    have hJmem : J ∈ 𝓝 x := hJ.mem_nhds hx
    refine Filter.mem_of_superset hJmem fun z hz => ?_
    have hz_eq := hderiv z hz
    simpa [hz_eq]
  have h_diff : DifferentiableAt ℝ (fun t => 2 * y t * deriv y t) x := by
    have hf := y_sq_second_deriv_formula hy hyy hx
    exact hf.differentiableAt
  have h_diff' : DifferentiableAt ℝ (deriv (fun t => y t * y t)) x :=
    (h_eq.differentiableAt_iff.mpr h_diff)
  exact h_diff'.differentiableWithinAt

/-- `y²` is convex on `[0, π]` when `λ ≤ 0`. -/
lemma y_sq_convex {y : ℝ → ℝ} {J : Set ℝ} {lam : ℝ}
    (hJ : IsOpen J) (hsub : Set.Icc (0 : ℝ) Real.pi ⊆ J)
    (hy : ∀ x ∈ J, HasDerivAt y (deriv y x) x)
    (hyy : ∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x)
    (hlam : lam ≤ 0) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) Real.pi) (fun x => y x * y x) := by
  have hD : Convex ℝ (Set.Icc (0 : ℝ) Real.pi) := convex_Icc 0 Real.pi
  have h_interior : interior (Set.Icc (0 : ℝ) Real.pi) ⊆ J :=
    Set.Subset.trans interior_subset hsub
  have h_sq := y_sq_differentiableOn_J hy
  rcases h_sq with ⟨hdiff_J, hderiv⟩
  have h_cont : ContinuousOn (fun x => y x * y x) (Set.Icc (0 : ℝ) Real.pi) :=
    (hdiff_J.mono hsub).continuousOn
  have h_diff_int : DifferentiableOn ℝ (fun x => y x * y x) (interior (Set.Icc (0 : ℝ) Real.pi)) :=
    hdiff_J.mono h_interior
  have h_deriv_diff_int :
      DifferentiableOn ℝ (deriv (fun x => y x * y x)) (interior (Set.Icc (0 : ℝ) Real.pi)) :=
    (y_sq_deriv_differentiableOn_J hJ hy hyy).mono h_interior
  have h_nonneg : ∀ x ∈ interior (Set.Icc (0 : ℝ) Real.pi), 0 ≤ deriv^[2] (fun x => y x * y x) x := by
    intro x hx
    have hxJ : x ∈ J := h_interior hx
    have h_eq : deriv (fun t => y t * y t) =ᶠ[𝓝 x] (fun t => 2 * y t * deriv y t) := by
      apply Filter.eventually_of_mem (hJ.mem_nhds hxJ)
      intro z hz
      have hz_eq := hderiv z hz
      simpa [hz_eq]
    have h_deriv2_eq : deriv^[2] (fun t => y t * y t) x = deriv (fun t => 2 * y t * deriv y t) x := by
      calc
        deriv^[2] (fun t => y t * y t) x = deriv (deriv (fun t => y t * y t)) x := rfl
        _ = deriv (fun t => 2 * y t * deriv y t) x := h_eq.deriv_eq
    rw [h_deriv2_eq]
    exact y_sq_second_deriv_nonneg hy hyy hlam hxJ
  exact convexOn_of_deriv2_nonneg hD h_cont h_diff_int h_deriv_diff_int h_nonneg

/-- If `λ ≤ 0` and the boundary conditions `y 0 = y π = 0` hold, then `y ≡ 0` on `[0, π]`. -/
lemma no_eigen_nonpos {y : ℝ → ℝ} {J : Set ℝ} {lam : ℝ}
    (hJ : IsOpen J) (hsub : Set.Icc (0 : ℝ) Real.pi ⊆ J)
    (hy : ∀ x ∈ J, HasDerivAt y (deriv y x) x)
    (hyy : ∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x)
    (hlam : lam ≤ 0) (hy0 : y 0 = 0) (hypi : y Real.pi = 0) :
    ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, y x = 0 := by
  have h_nonneg_pi : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  have hconvex : ConvexOn ℝ (Set.Icc (0 : ℝ) Real.pi) (fun x => y x * y x) :=
    y_sq_convex hJ hsub hy hyy hlam
  intro x hx
  have hx0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) Real.pi := Set.left_mem_Icc.mpr h_nonneg_pi
  have hxpi : Real.pi ∈ Set.Icc (0 : ℝ) Real.pi := Set.right_mem_Icc.mpr h_nonneg_pi
  have hineq : y x * y x ≤ max (y 0 * y 0) (y Real.pi * y Real.pi) :=
    hconvex.le_max_of_mem_Icc hx0 hxpi hx
  have hy0sq : y 0 * y 0 = 0 := by rw [hy0, zero_mul]
  have hypisq : y Real.pi * y Real.pi = 0 := by rw [hypi, zero_mul]
  have hyx_sq_nonneg : 0 ≤ y x * y x := by
    simpa [sq] using sq_nonneg (y x)
  have hyx_sq_zero : y x * y x = 0 :=
    le_antisymm (by
      calc
        y x * y x ≤ max (y 0 * y 0) (y Real.pi * y Real.pi) := hineq
        _ = 0 := by rw [hy0sq, hypisq, max_self]
      ) hyx_sq_nonneg
  exact mul_self_eq_zero.mp hyx_sq_zero

end ODE
end Analysis
end LeanEval
