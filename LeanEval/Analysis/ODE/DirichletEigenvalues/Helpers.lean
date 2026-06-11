import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

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
      _ = Real.sin (((n : ℝ) * Real.pi) / (2 * (n : ℝ))) := by ring
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
    simpa using Real.sin_nat_mul_pi n
  have h_nonzero : ∃ x₀ ∈ Set.Ioo (0 : ℝ) Real.pi, y x₀ ≠ 0 :=
    sin_nx_nontrivial_witness n hn
  exact ⟨hy_deriv, hy_second_deriv, hy0, hypi, h_nonzero⟩

end ODE
end Analysis
end LeanEval
