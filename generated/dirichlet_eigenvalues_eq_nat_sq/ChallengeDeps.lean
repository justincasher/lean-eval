import Mathlib

namespace LeanEval
namespace Analysis
namespace ODE

open scoped Real

/-! ## Preliminaries: derivatives of `sin(s·x)`, `cos(s·x)`, and their combinations -/

/-- Derivative of `t ↦ sin (s * t)` at `x` is `s * cos (s * x)`. -/
lemma sin_smul_hasDerivAt (s x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.sin (s * t)) (s * Real.cos (s * x)) x := by
  simpa [smul_eq_mul, mul_comm] using ((hasDerivAt_id x).const_smul s).sin

/-- Derivative of `t ↦ cos (s * t)` at `x` is `-(s * sin (s * x))`. -/
lemma cos_smul_hasDerivAt (s x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.cos (s * t)) (-(s * Real.sin (s * x))) x := by
  simpa [smul_eq_mul, mul_comm] using ((hasDerivAt_id x).const_smul s).cos

/-- First derivative of `t ↦ A * sin (s * t) + B * cos (s * t)`. -/
lemma sin_cos_combo_first_deriv (A B s x : ℝ) :
    HasDerivAt (fun t : ℝ => A * Real.sin (s * t) + B * Real.cos (s * t))
      (A * s * Real.cos (s * x) - B * s * Real.sin (s * x)) x := by
  have hsin := sin_smul_hasDerivAt s x
  have hcos := cos_smul_hasDerivAt s x
  have hA : HasDerivAt (fun t : ℝ => A * Real.sin (s * t)) (A * (s * Real.cos (s * x))) x :=
    hsin.const_mul A
  have hB : HasDerivAt (fun t : ℝ => B * Real.cos (s * t)) (B * (-(s * Real.sin (s * x)))) x :=
    hcos.const_mul B
  have hsum : HasDerivAt (fun t : ℝ => A * Real.sin (s * t) + B * Real.cos (s * t))
      (A * (s * Real.cos (s * x)) + B * (-(s * Real.sin (s * x)))) x :=
    hA.add hB
  simpa [mul_assoc, mul_comm, mul_left_comm, sub_eq_add_neg] using hsum

/-- Second derivative formula: the function `t ↦ A s cos (s t) - B s sin (s t)`, which is
the first derivative of `t ↦ A sin (s t) + B cos (s t)`, has at every `x` the value
`deriv _ x = -s² (A sin (s x) + B cos (s x))`. -/
lemma sin_cos_combo_second_deriv (A B s x : ℝ) :
    deriv (fun t : ℝ => A * s * Real.cos (s * t) - B * s * Real.sin (s * t)) x
      = -s ^ 2 * (A * Real.sin (s * x) + B * Real.cos (s * x)) := by
  have hcos := cos_smul_hasDerivAt s x
  have hsin := sin_smul_hasDerivAt s x
  have hcos_mul : HasDerivAt (fun t : ℝ => (A * s) * Real.cos (s * t)) ((A * s) * (-(s * Real.sin (s * x)))) x :=
    hcos.const_mul (A * s)
  have hsin_mul : HasDerivAt (fun t : ℝ => (-(B * s)) * Real.sin (s * t)) ((-(B * s)) * (s * Real.cos (s * x))) x :=
    hsin.const_mul (-(B * s))
  have hsum : HasDerivAt (fun t : ℝ => (A * s) * Real.cos (s * t) + (-(B * s)) * Real.sin (s * t))
      ((A * s) * (-(s * Real.sin (s * x))) + (-(B * s)) * (s * Real.cos (s * x))) x :=
    hcos_mul.add hsin_mul
  have hf : (fun t : ℝ => A * s * Real.cos (s * t) - B * s * Real.sin (s * t)) =
      (fun t : ℝ => (A * s) * Real.cos (s * t) + (-(B * s)) * Real.sin (s * t)) := by
    ext t; ring
  rw [hf]
  rw [hsum.deriv]
  ring

/-- Initial values of `g(x) = A sin(s·x) + B cos(s·x)`: `g 0 = B` and `deriv g 0 = A s`. -/
lemma sin_cos_combo_initial_values (A B s : ℝ) :
    let g : ℝ → ℝ := fun t => A * Real.sin (s * t) + B * Real.cos (s * t)
    g 0 = B ∧ deriv g 0 = A * s := by
  intro g
  have h0 : g 0 = B := by
    dsimp [g]
    simp [Real.sin_zero, Real.cos_zero]
  have hderiv : deriv g 0 = A * s := by
    have h := sin_cos_combo_first_deriv A B s 0
    have hderiv_eq : deriv g 0 = A * s * Real.cos (s * 0) - B * s * Real.sin (s * 0) := by
      simpa [g] using h.deriv
    simpa [Real.sin_zero, Real.cos_zero, mul_zero, mul_one] using hderiv_eq
  exact And.intro h0 hderiv

/-- `g(x) = A sin(s·x) + B cos(s·x)` solves the harmonic oscillator on `ℝ`:
its first derivative is `A s cos(s·x) - B s sin(s·x)`, its second derivative is
`-s² g(x)`, and the initial data are `g 0 = B`, `deriv g 0 = A s`. -/
lemma sin_cos_combo_solves_ode (A B s : ℝ) :
    let g : ℝ → ℝ := fun t => A * Real.sin (s * t) + B * Real.cos (s * t)
    (∀ x : ℝ, HasDerivAt g (deriv g x) x) ∧
      (∀ x : ℝ, deriv g x = A * s * Real.cos (s * x) - B * s * Real.sin (s * x)) ∧
      (∀ x : ℝ, HasDerivAt (deriv g) (-s ^ 2 * g x) x) ∧
      (∀ x : ℝ, deriv (deriv g) x = -s ^ 2 * g x) ∧
      g 0 = B ∧ deriv g 0 = A * s := by
  intro g
  have hfirst (x : ℝ) : HasDerivAt g (A * s * Real.cos (s * x) - B * s * Real.sin (s * x)) x :=
    sin_cos_combo_first_deriv A B s x
  have hderiv_eq (x : ℝ) : deriv g x = A * s * Real.cos (s * x) - B * s * Real.sin (s * x) :=
    (hfirst x).deriv
  have hsecond_has (x : ℝ) : HasDerivAt (deriv g) (-s ^ 2 * g x) x := by
    have hgen : HasDerivAt (fun t : ℝ => A * s * Real.cos (s * t) - B * s * Real.sin (s * t))
        (-s ^ 2 * g x) x := by
      have h := sin_cos_combo_first_deriv (-B * s) (A * s) s x
      have hval : (-B * s) * s * Real.cos (s * x) - (A * s) * s * Real.sin (s * x) = -s ^ 2 * g x := by
        dsimp [g]
        ring
      have hfun : (fun t : ℝ => (-B * s) * Real.sin (s * t) + (A * s) * Real.cos (s * t)) =
          (fun t : ℝ => A * s * Real.cos (s * t) - B * s * Real.sin (s * t)) := by
        ext t; ring
      rw [hfun, hval] at h
      exact h
    have heq : (fun t : ℝ => A * s * Real.cos (s * t) - B * s * Real.sin (s * t)) = deriv g := by
      ext x; exact (hderiv_eq x).symm
    simpa [heq] using hgen
  have hsecond_deriv (x : ℝ) : deriv (deriv g) x = -s ^ 2 * g x := by
    have h := sin_cos_combo_second_deriv A B s x
    have heq : (fun t : ℝ => A * s * Real.cos (s * t) - B * s * Real.sin (s * t)) = deriv g := by
      ext x; exact (hderiv_eq x).symm
    simpa [heq] using h
  have hinit : g 0 = B ∧ deriv g 0 = A * s := sin_cos_combo_initial_values A B s
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simpa [← (hfirst x).deriv] using hfirst x
  · exact hderiv_eq
  · exact hsecond_has
  · exact hsecond_deriv
  · exact hinit.1
  · exact hinit.2

/-! ## Backward direction: `sin(n·x)` is an eigenfunction -/

/-- For each positive natural `n`, there is `x₀ ∈ (0, π)` with `sin (n · x₀) ≠ 0`. -/
lemma sin_nx_nontrivial_witness (n : ℕ) (hn : 0 < n) :
    ∃ x₀ ∈ Set.Ioo (0 : ℝ) Real.pi, Real.sin ((n : ℝ) * x₀) ≠ 0 := by
  have hn_real : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := by linarith
  set x₀ := Real.pi / (2 * (n : ℝ)) with hx₀_def
  have hx₀_pos : 0 < x₀ := by
    dsimp [x₀]
    exact div_pos Real.pi_pos (by nlinarith)
  have hx₀_lt_pi : x₀ < Real.pi := by
    dsimp [x₀]
    have h_one_le_n : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_of_lt hn
    field_simp [hn_ne]
    nlinarith
  have hcalc : Real.sin ((n : ℝ) * x₀) = 1 := by
    calc
      Real.sin ((n : ℝ) * x₀) = Real.sin ((n : ℝ) * (Real.pi / (2 * (n : ℝ)))) := rfl
      _ = Real.sin (((n : ℝ) * Real.pi) / (2 * (n : ℝ))) := by ring_nf
      _ = Real.sin (Real.pi / 2) := by
        have h_eq : (n : ℝ) * Real.pi / (2 * (n : ℝ)) = Real.pi / 2 := by
          field_simp [hn_ne]
        rw [h_eq]
      _ = 1 := Real.sin_pi_div_two
  refine ⟨x₀, Set.mem_Ioo.mpr ⟨hx₀_pos, hx₀_lt_pi⟩, ?_⟩
  rw [hcalc]
  norm_num

/-- For each positive natural `n`, the function `y(x) = sin(n·x)` realises the
Dirichlet eigenvalue `n²` on `J = ℝ`. -/
lemma sin_eigenfunction (n : ℕ) (hn : 0 < n) :
    let y : ℝ → ℝ := fun x => Real.sin ((n : ℝ) * x)
    (∀ x : ℝ, HasDerivAt y (deriv y x) x) ∧
      (∀ x : ℝ, HasDerivAt (deriv y) (-((n : ℝ) ^ 2 * y x)) x) ∧
      y 0 = 0 ∧ y Real.pi = 0 ∧
      ∃ x₀ ∈ Set.Ioo (0 : ℝ) Real.pi, y x₀ ≠ 0 := by
  intro y
  have hy_deriv : ∀ x : ℝ, HasDerivAt y (deriv y x) x := by
    intro x
    have hfirst := sin_cos_combo_first_deriv 1 0 (n : ℝ) x
    have h_at : HasDerivAt y ((n : ℝ) * Real.cos ((n : ℝ) * x)) x := by
      simpa [y] using hfirst
    have hy_deriv_eq : deriv y x = (n : ℝ) * Real.cos ((n : ℝ) * x) := h_at.deriv
    simpa [hy_deriv_eq] using h_at
  have hy_second_deriv : ∀ x : ℝ, HasDerivAt (deriv y) (-((n : ℝ) ^ 2 * y x)) x := by
    intro x
    have hcos := cos_smul_hasDerivAt (n : ℝ) x
    have hy_deriv_eq : deriv y = fun t : ℝ => (n : ℝ) * Real.cos ((n : ℝ) * t) := by
      ext t
      have hfirst_t := sin_cos_combo_first_deriv 1 0 (n : ℝ) t
      simpa [y] using hfirst_t.deriv
    have h_deriv_y : HasDerivAt (fun t : ℝ => (n : ℝ) * Real.cos ((n : ℝ) * t))
        ((n : ℝ) * (-((n : ℝ) * Real.sin ((n : ℝ) * x)))) x :=
      hcos.const_mul (n : ℝ)
    have hval : (n : ℝ) * (-((n : ℝ) * Real.sin ((n : ℝ) * x))) = -((n : ℝ) ^ 2 * y x) := by
      dsimp [y]
      ring
    simpa [hy_deriv_eq, hval] using h_deriv_y
  have hy0 : y 0 = 0 := by
    dsimp [y]
    simp [Real.sin_zero]
  have hypi : y Real.pi = 0 := by
    dsimp [y]
    simp
  have h_nonzero : ∃ x₀ ∈ Set.Ioo (0 : ℝ) Real.pi, y x₀ ≠ 0 :=
    sin_nx_nontrivial_witness n hn
  exact ⟨hy_deriv, hy_second_deriv, hy0, hypi, h_nonzero⟩

end ODE
end Analysis
end LeanEval
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
  change HasDerivAt (y * y) (2 * y x * deriv y x) x
  convert prod using 1
  all_goals first | rfl | ring

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
    change HasDerivAt (y * deriv y) (deriv y x ^ 2 - lam * y x ^ 2) x
    convert prod using 1
    all_goals first | rfl | ring
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
    simp [hz_eq]
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
      simp [hz_eq]
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
namespace LeanEval
namespace Analysis
namespace ODE

open scoped Real Topology

/-! ## Forward direction, case `λ > 0`: energy method -/

/-- Derivative of `(y')²` at `x` under the ODE: equals `-2 λ y(x) y'(x)`. -/
lemma yprime_sq_hasDerivAt {y : ℝ → ℝ} {J : Set ℝ} {lam : ℝ}
    (hyy : ∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x)
    {x : ℝ} (hx : x ∈ J) :
    HasDerivAt (fun t => deriv y t * deriv y t) (-2 * lam * y x * deriv y x) x := by
  have prod := (hyy x hx).mul (hyy x hx)
  change HasDerivAt (deriv y * deriv y) (-2 * lam * y x * deriv y x) x
  convert prod using 1
  all_goals first | rfl | ring

/-- The energy `E(x) = λ y(x)² + y'(x)²` has derivative `0` at every `x ∈ J`. -/
lemma energy_hasDerivAt_zero {y : ℝ → ℝ} {J : Set ℝ} {lam : ℝ}
    (hy : ∀ x ∈ J, HasDerivAt y (deriv y x) x)
    (hyy : ∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x)
    {x : ℝ} (hx : x ∈ J) :
    HasDerivAt (fun t => lam * (y t * y t) + deriv y t * deriv y t) 0 x := by
  have hy_sq := y_sq_first_deriv hy hx
  have hyprime_sq := yprime_sq_hasDerivAt hyy hx
  have h_lam_sq : HasDerivAt (fun t => lam * (y t * y t)) (lam * (2 * y x * deriv y x)) x :=
    hy_sq.const_mul lam
  have hsum := h_lam_sq.add hyprime_sq
  have hcalc : lam * (2 * y x * deriv y x) + -2 * lam * y x * deriv y x = 0 := by ring
  rw [hcalc] at hsum
  exact hsum

/-- Energy conservation: `E(x) = E(0)` on `[0, π]`. -/
lemma energy_const {y : ℝ → ℝ} {J : Set ℝ} {lam : ℝ}
    (_hJ : IsOpen J) (hsub : Set.Icc (0 : ℝ) Real.pi ⊆ J)
    (hy : ∀ x ∈ J, HasDerivAt y (deriv y x) x)
    (hyy : ∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x) :
    ∀ x ∈ Set.Icc (0 : ℝ) Real.pi,
      lam * (y x * y x) + deriv y x * deriv y x
        = lam * (y 0 * y 0) + deriv y 0 * deriv y 0 := by
  let E : ℝ → ℝ := fun t => lam * (y t * y t) + deriv y t * deriv y t
  have hE_zero : ∀ x ∈ J, HasDerivAt E 0 x :=
    fun x hx => energy_hasDerivAt_zero hy hyy hx
  have hE_diff : DifferentiableOn ℝ E (Set.Icc (0 : ℝ) Real.pi) := by
    intro x hx
    have hxJ : x ∈ J := hsub hx
    exact (hE_zero x hxJ).differentiableAt.differentiableWithinAt
  have hE_deriv : ∀ x ∈ Set.Ico (0 : ℝ) Real.pi,
      derivWithin E (Set.Icc (0 : ℝ) Real.pi) x = 0 := by
    intro x hx
    have hxcc : x ∈ Set.Icc (0 : ℝ) Real.pi := ⟨hx.1, hx.2.le⟩
    have hxJ : x ∈ J := hsub hxcc
    have h_hasDerivWithin : HasDerivWithinAt E 0 (Set.Icc (0 : ℝ) Real.pi) x :=
      (hE_zero x hxJ).hasDerivWithinAt
    have h_unique : UniqueDiffWithinAt ℝ (Set.Icc (0 : ℝ) Real.pi) x :=
      uniqueDiffOn_Icc (by exact Real.pi_pos) x hxcc
    simpa using h_hasDerivWithin.derivWithin h_unique
  intro x hx
  exact constant_of_derivWithin_zero hE_diff hE_deriv x hx

/-- Zero initial conditions plus `λ > 0` force `y` and `y'` to vanish on `[0, π]`. -/
lemma zero_initial_zero_solution {y : ℝ → ℝ} {J : Set ℝ} {lam : ℝ}
    (hJ : IsOpen J) (hsub : Set.Icc (0 : ℝ) Real.pi ⊆ J)
    (hy : ∀ x ∈ J, HasDerivAt y (deriv y x) x)
    (hyy : ∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x)
    (hlam : 0 < lam) (hy0 : y 0 = 0) (hyprime0 : deriv y 0 = 0) :
    ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, y x = 0 ∧ deriv y x = 0 := by
  have hEconst := energy_const hJ hsub hy hyy
  have hE0 : lam * (y 0 * y 0) + deriv y 0 * deriv y 0 = 0 := by
    simp [hy0, hyprime0]
  intro x hx
  have hEx : lam * (y x * y x) + deriv y x * deriv y x = 0 := by
    rw [hEconst x hx, hE0]
  have hy_sq_nonneg : 0 ≤ y x * y x := by nlinarith [sq_nonneg (y x)]
  have hderiv_sq_nonneg : 0 ≤ deriv y x * deriv y x := by nlinarith [sq_nonneg (deriv y x)]
  have hlam_yx_sq_nonneg : 0 ≤ lam * (y x * y x) := mul_nonneg (by linarith) hy_sq_nonneg
  have hsum_nonneg : 0 ≤ lam * (y x * y x) + deriv y x * deriv y x := by nlinarith
  have hlam_yx_sq_zero : lam * (y x * y x) = 0 := by nlinarith
  have hderiv_sq_zero : deriv y x * deriv y x = 0 := by nlinarith
  have hyx0 : y x = 0 := by
    have hsq : y x * y x = 0 := by nlinarith
    exact (mul_self_eq_zero.mp hsq)
  have hderiv0 : deriv y x = 0 := by
    have hsq : deriv y x * deriv y x = 0 := by nlinarith
    exact (mul_self_eq_zero.mp hsq)
  exact ⟨hyx0, hderiv0⟩

/-- `g(x) = A sin(√λ · x) + B cos(√λ · x)` solves `-y'' = λ y` on `ℝ` when `λ ≥ 0`. -/
lemma sin_cos_combo_solves_ode_lambda (lam A B : ℝ) (hlam : 0 ≤ lam) :
    let s := Real.sqrt lam
    let g : ℝ → ℝ := fun x => A * Real.sin (s * x) + B * Real.cos (s * x)
    (∀ x : ℝ, HasDerivAt g (deriv g x) x) ∧
      (∀ x : ℝ, HasDerivAt (deriv g) (-(lam * g x)) x) := by
  intro s g
  have hsq : s ^ 2 = lam := Real.sq_sqrt hlam
  have h := sin_cos_combo_solves_ode A B s
  rcases h with ⟨h1, _, h3, _, _, _⟩
  refine ⟨h1, λ x => ?_⟩
  have h3x : HasDerivAt (deriv g) (-(s ^ 2) * g x) x := h3 x
  simpa [hsq, neg_mul] using h3x

/-- Initial data match for `g` when `A = y'(0)/s, B = y(0)` (with `s ≠ 0`):
`g 0 = y 0` and `deriv g 0 = deriv y 0`. -/
lemma g_match_initial_data (y : ℝ → ℝ) {s : ℝ} (hs : s ≠ 0) :
    let A := deriv y 0 / s
    let B := y 0
    let g : ℝ → ℝ := fun x => A * Real.sin (s * x) + B * Real.cos (s * x)
    g 0 = y 0 ∧ deriv g 0 = deriv y 0 := by
  intro A B g
  have h := sin_cos_combo_initial_values A B s
  rcases h with ⟨hg0, hderiv⟩
  refine ⟨?_, ?_⟩
  · dsimp [B] at hg0
    exact hg0
  · dsimp [A] at hderiv
    rw [hderiv]
    exact div_mul_cancel₀ (deriv y 0) hs

/-- Difference of two ODE solutions is again an ODE solution. -/
lemma diff_of_two_ode_solutions {y g : ℝ → ℝ} {J : Set ℝ} {lam : ℝ}
    (hJ : IsOpen J)
    (hy : ∀ x ∈ J, HasDerivAt y (deriv y x) x)
    (hyy : ∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x)
    (hg : ∀ x ∈ J, HasDerivAt g (deriv g x) x)
    (hgg : ∀ x ∈ J, HasDerivAt (deriv g) (-(lam * g x)) x) :
    (∀ x ∈ J, HasDerivAt (fun t => y t - g t) (deriv y x - deriv g x) x) ∧
      (∀ x ∈ J, HasDerivAt (deriv (fun t => y t - g t)) (-(lam * (y x - g x))) x) ∧
      (0 ∈ J → deriv (fun t => y t - g t) 0 = deriv y 0 - deriv g 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx; exact (hy x hx).sub (hg x hx)
  · intro x hx
    have hzz : HasDerivAt (fun t => deriv y t - deriv g t) (-(lam * (y x - g x))) x := by
      have h := (hyy x hx).sub (hgg x hx)
      change HasDerivAt (deriv y - deriv g) (-(lam * (y x - g x))) x
      convert h using 1
      all_goals first | rfl | ring
    have h_ev : deriv (fun t => y t - g t) =ᶠ[𝓝 x] (fun t => deriv y t - deriv g t) := by
      filter_upwards [hJ.mem_nhds hx] with t ht
      exact deriv_sub ((hy t ht).differentiableAt) ((hg t ht).differentiableAt)
    exact hzz.congr_of_eventuallyEq h_ev
  · intro h0J
    exact ((hy 0 h0J).sub (hg 0 h0J)).deriv

/-- For `λ > 0`, the difference `z = y - g` (with `A = y'(0)/s, B = y(0)`,
`g(x) = A sin(s·x) + B cos(s·x)`, `s = √λ`) has zero initial data and satisfies the ODE. -/
lemma solution_diff_is_zero_initial_solution {y : ℝ → ℝ} {J : Set ℝ} {lam : ℝ}
    (hJ : IsOpen J) (hsub : Set.Icc (0 : ℝ) Real.pi ⊆ J)
    (hy : ∀ x ∈ J, HasDerivAt y (deriv y x) x)
    (hyy : ∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x)
    (hlam : 0 < lam) :
    let s := Real.sqrt lam
    let A := deriv y 0 / s
    let B := y 0
    let g : ℝ → ℝ := fun x => A * Real.sin (s * x) + B * Real.cos (s * x)
    let z : ℝ → ℝ := fun x => y x - g x
    (∀ x ∈ J, HasDerivAt z (deriv z x) x) ∧
      (∀ x ∈ J, HasDerivAt (deriv z) (-(lam * z x)) x) ∧
      z 0 = 0 ∧ deriv z 0 = 0 := by
  intro s A B g z
  have hs_pos : s ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hlam)
  have hlam_nonneg : 0 ≤ lam := le_of_lt hlam
  have hg_solves := sin_cos_combo_solves_ode_lambda lam A B hlam_nonneg
  rcases hg_solves with ⟨hg_all, hgg_all⟩
  have hg : ∀ x ∈ J, HasDerivAt g (deriv g x) x := λ x _ => hg_all x
  have hgg : ∀ x ∈ J, HasDerivAt (deriv g) (-(lam * g x)) x := λ x _ => hgg_all x
  -- First conclusion: z is differentiable on J
  have hz_first : ∀ x ∈ J, HasDerivAt z (deriv z x) x := by
    intro x hx
    have hz_has : HasDerivAt (y - g) (deriv y x - deriv g x) x := (hy x hx).sub (hg x hx)
    have hderiv_zx : deriv z x = deriv y x - deriv g x := by
      dsimp [z]
      exact deriv_sub ((hy x hx).differentiableAt) ((hg x hx).differentiableAt)
    change HasDerivAt (y - g) (deriv z x) x
    convert hz_has using 1
  -- Second conclusion: deriv z also satisfies the ODE on J
  have hz_second : ∀ x ∈ J, HasDerivAt (deriv z) (-(lam * z x)) x := by
    intro x hx
    have hzz_has : HasDerivAt (deriv y - deriv g) (-(lam * (y x - g x))) x := by
      have h := (hyy x hx).sub (hgg x hx)
      have hcalc : -(lam * y x) - (-(lam * g x)) = -(lam * (y x - g x)) := by ring
      simpa [hcalc] using h
    -- Since J is open, deriv z and deriv y - deriv g agree in a neighbourhood of x
    have h_ev : deriv z =ᶠ[𝓝 x] (deriv y - deriv g) := by
      apply Filter.eventually_of_mem (hJ.mem_nhds hx)
      intro t ht
      have htJ : t ∈ J := ht
      dsimp [z]
      exact deriv_sub ((hy t htJ).differentiableAt) ((hg t htJ).differentiableAt)
    have hz_has_second : HasDerivAt (deriv z) (-(lam * (y x - g x))) x :=
      hzz_has.congr_of_eventuallyEq h_ev
    simpa [z, g] using hz_has_second
  -- Third conclusion: z 0 = 0
  have hz0val : z 0 = 0 := by
    have hg0val : g 0 = y 0 := by simp [g, B]
    dsimp [z]
    rw [hg0val, sub_self]
  -- Fourth conclusion: deriv z 0 = 0
  have hderivz0 : deriv z 0 = 0 := by
    have hderivg0 : deriv g 0 = deriv y 0 := by
      have h := sin_cos_combo_initial_values A B s
      rcases h with ⟨_, hderiv⟩
      have hcalc : deriv g 0 = (deriv y 0 / s) * s := by simpa [A, B, g] using hderiv
      calc
        deriv g 0 = (deriv y 0 / s) * s := hcalc
        _ = deriv y 0 := by field_simp [hs_pos]
    have h0J : (0 : ℝ) ∈ J := by
      have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) Real.pi :=
        Set.left_mem_Icc.mpr (by have := Real.pi_pos; linarith)
      exact hsub h0mem
    have hz_deriv0 : deriv z 0 = deriv y 0 - deriv g 0 := by
      dsimp [z]
      exact deriv_sub ((hy 0 h0J).differentiableAt) ((hg 0 h0J).differentiableAt)
    rw [hz_deriv0, hderivg0, sub_self]
  exact ⟨hz_first, hz_second, hz0val, hderivz0⟩

/-- Explicit form of solutions when `λ > 0`:
`y(x) = (y'(0)/√λ) sin(√λ · x) + y(0) cos(√λ · x)` for `x ∈ [0, π]`. -/
lemma solution_explicit {y : ℝ → ℝ} {J : Set ℝ} {lam : ℝ}
    (hJ : IsOpen J) (hsub : Set.Icc (0 : ℝ) Real.pi ⊆ J)
    (hy : ∀ x ∈ J, HasDerivAt y (deriv y x) x)
    (hyy : ∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x)
    (hlam : 0 < lam) :
    let s := Real.sqrt lam
    ∀ x ∈ Set.Icc (0 : ℝ) Real.pi,
      y x = deriv y 0 / s * Real.sin (s * x) + y 0 * Real.cos (s * x) := by
  intro s x hx
  let A := deriv y 0 / s
  let B := y 0
  let g : ℝ → ℝ := fun x => A * Real.sin (s * x) + B * Real.cos (s * x)
  let z : ℝ → ℝ := fun x => y x - g x
  have hz_props := solution_diff_is_zero_initial_solution hJ hsub hy hyy hlam
  rcases hz_props with ⟨hz, hzz, hz0, hzderiv0⟩
  have hz_zero_solution : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, z x = 0 ∧ deriv z x = 0 :=
    zero_initial_zero_solution hJ hsub hz hzz hlam hz0 hzderiv0
  have hz_eq0 : z x = 0 := (hz_zero_solution x hx).1
  dsimp [z, g, A, B] at hz_eq0
  linarith

/-- Solution form when `y(0) = 0` and `λ > 0`:
`y(x) = (y'(0)/√λ) sin(√λ · x)` on `[0, π]`. -/
lemma solution_form_when_y0_zero {y : ℝ → ℝ} {J : Set ℝ} {lam : ℝ}
    (hJ : IsOpen J) (hsub : Set.Icc (0 : ℝ) Real.pi ⊆ J)
    (hy : ∀ x ∈ J, HasDerivAt y (deriv y x) x)
    (hyy : ∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x)
    (hlam : 0 < lam) (hy0 : y 0 = 0) :
    let s := Real.sqrt lam
    ∀ x ∈ Set.Icc (0 : ℝ) Real.pi,
      y x = deriv y 0 / s * Real.sin (s * x) := by
  intro s
  have h_explicit := solution_explicit hJ hsub hy hyy hlam
  intro x hx
  have h := h_explicit x hx
  rw [hy0] at h
  simpa using h

/-- If `s > 0` and `sin (s · π) = 0`, then `s` is a positive natural number. -/
lemma sin_pi_smul_eq_zero_pos_to_nat {s : ℝ} (hs : 0 < s)
    (hsin : Real.sin (s * Real.pi) = 0) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) = s := by
  rcases Real.sin_eq_zero_iff.mp hsin with ⟨k, h⟩
  -- h : (k : ℝ) * Real.pi = s * Real.pi
  have hk_real : (k : ℝ) = s := by
    nlinarith [Real.pi_pos]
  have hk_int_pos : 0 < k := by
    have : (0 : ℝ) < (k : ℝ) := by rw [hk_real]; exact hs
    exact_mod_cast this
  set n := k.toNat with hn
  have hn_pos : 0 < n := by
    dsimp [n]
    exact (Int.pos_iff_toNat_pos.mp hk_int_pos)
  have hn_cast : (n : ℝ) = s := by
    calc
      (n : ℝ) = (k : ℝ) := by
        dsimp [n]
        have hk_nonneg : 0 ≤ k := by omega
        exact_mod_cast (Int.toNat_of_nonneg hk_nonneg)
      _ = s := hk_real
  exact ⟨n, hn_pos, hn_cast⟩

/-- For `λ > 0`, nontriviality of `y` (with `y 0 = 0`) forces `deriv y 0 ≠ 0`. -/
lemma yprime0_ne_zero_of_nontrivial {y : ℝ → ℝ} {J : Set ℝ} {lam : ℝ}
    (hJ : IsOpen J) (hsub : Set.Icc (0 : ℝ) Real.pi ⊆ J)
    (hy : ∀ x ∈ J, HasDerivAt y (deriv y x) x)
    (hyy : ∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x)
    (hlam : 0 < lam) (hy0 : y 0 = 0)
    (hnontriv : ∃ x₀ ∈ Set.Ioo (0 : ℝ) Real.pi, y x₀ ≠ 0) :
    deriv y 0 ≠ 0 := by
  rcases hnontriv with ⟨x₀, hx₀, hyx₀⟩
  intro hyprime0
  have hx₀_icc : x₀ ∈ Set.Icc (0 : ℝ) Real.pi := by
    rcases hx₀ with ⟨hx₀_left, hx₀_right⟩
    exact ⟨hx₀_left.le, hx₀_right.le⟩
  have h_formula := solution_form_when_y0_zero hJ hsub hy hyy hlam hy0
  have hyx₀_formula : y x₀ = deriv y 0 / Real.sqrt lam * Real.sin (Real.sqrt lam * x₀) :=
    h_formula x₀ hx₀_icc
  rw [hyprime0] at hyx₀_formula
  have hyx₀_zero : y x₀ = 0 := by
    simpa using hyx₀_formula
  exact hyx₀ hyx₀_zero

/-- For `λ > 0`, a Dirichlet eigenvalue is `n²` for some positive natural `n`. -/
lemma pos_eigen_nat_sq {y : ℝ → ℝ} {J : Set ℝ} {lam : ℝ}
    (hJ : IsOpen J) (hsub : Set.Icc (0 : ℝ) Real.pi ⊆ J)
    (hy : ∀ x ∈ J, HasDerivAt y (deriv y x) x)
    (hyy : ∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x)
    (hy0 : y 0 = 0) (hypi : y Real.pi = 0)
    (hnontriv : ∃ x₀ ∈ Set.Ioo (0 : ℝ) Real.pi, y x₀ ≠ 0)
    (hlam : 0 < lam) :
    ∃ n : ℕ, 0 < n ∧ lam = (n : ℝ) ^ 2 := by
  let s := Real.sqrt lam
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hlam
  have hy_form : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, y x = deriv y 0 / s * Real.sin (s * x) :=
    solution_form_when_y0_zero hJ hsub hy hyy hlam hy0
  have hy_pi_form : y Real.pi = deriv y 0 / s * Real.sin (s * Real.pi) :=
    hy_form Real.pi ⟨by linarith [Real.pi_pos], le_refl _⟩
  rw [hypi] at hy_pi_form
  have hderiv_ne_zero : deriv y 0 ≠ 0 :=
    yprime0_ne_zero_of_nontrivial hJ hsub hy hyy hlam hy0 hnontriv
  have hs_ne_zero : s ≠ 0 := by linarith
  have hdiv_ne_zero : deriv y 0 / s ≠ 0 := by
    intro hzero
    apply hderiv_ne_zero
    exact (div_eq_zero_iff.mp hzero).resolve_right hs_ne_zero
  have hsin_zero : Real.sin (s * Real.pi) = 0 := by
    have hprod_zero : deriv y 0 / s * Real.sin (s * Real.pi) = 0 := by
      simpa using hy_pi_form
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hprod_zero with (hdiv | hsin)
    · exfalso; exact hdiv_ne_zero hdiv
    · exact hsin
  rcases sin_pi_smul_eq_zero_pos_to_nat hs_pos hsin_zero with ⟨n, hn_pos, hn_eq⟩
  have h_s_sq_eq : s ^ 2 = lam := by
    dsimp [s]
    exact Real.sq_sqrt (by linarith : 0 ≤ lam)
  refine ⟨n, hn_pos, ?_⟩
  rw [h_s_sq_eq.symm, hn_eq]

end ODE
end Analysis
end LeanEval
