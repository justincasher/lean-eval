import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import LeanEval.Analysis.ODE.DirichletEigenvalues.Helpers
import LeanEval.Analysis.ODE.DirichletEigenvalues.Nonpositive

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
  have hcalc : -(lam * y x * deriv y x) + -(deriv y x * (lam * y x)) = -2 * lam * y x * deriv y x := by ring
  simpa [hcalc] using prod

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
    (hJ : IsOpen J) (hsub : Set.Icc (0 : ℝ) Real.pi ⊆ J)
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
      have hcalc : -(lam * y x) - (-(lam * g x)) = -(lam * (y x - g x)) := by ring
      simpa [hcalc] using h
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
    simpa [hderiv_zx] using hz_has
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
    have hg0val : g 0 = y 0 := by
      have h := sin_cos_combo_initial_values A B s
      simpa [A, B, g] using h.1
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
