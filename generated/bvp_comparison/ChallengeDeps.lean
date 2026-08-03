import Mathlib

namespace LeanEval
namespace Analysis
namespace ODE

/-!
Comparison principle for the second-order Dirichlet boundary value problem.

If `u, v` are `C²` on an open interval `J` containing `[0, 1]` and satisfy
  `-u''(x) ≤ -v''(x)` on `(0, 1)`,
together with the boundary inequalities `u 0 ≤ v 0` and `u 1 ≤ v 1`, then `u ≤ v` on
`[0, 1]`.

This is the simplest 1D maximum principle. Direct convex argument: `(u - v)'' ≥ 0` on
`(0, 1)` so `u - v` is convex on `[0, 1]`, hence bounded above by its chord, which is
non-positive at the endpoints.

We work with the explicit difference function `w := u - v` and take the first/second
derivative functions `deriv u - deriv v` and `deriv (deriv u) - deriv (deriv v)` as
data, so that no identification of `deriv (u - v)` with `deriv u - deriv v` is needed.
-/

/-- **Difference function.** Given `u, v : ℝ → ℝ`, define `w := u - v`, i.e.
`w x = u x - v x` for all `x`. -/
def w (u v : ℝ → ℝ) : ℝ → ℝ := u - v

/-- **Continuity of the difference.** Under the `C²` hypotheses, `w = u - v` is
continuous on `[0, 1]`. -/
theorem w_continuousOn
    (J : Set ℝ) (hJ_sub : Set.Icc (0 : ℝ) 1 ⊆ J)
    (u v : ℝ → ℝ)
    (hu : ∀ x ∈ J, HasDerivAt u (deriv u x) x)
    (hv : ∀ x ∈ J, HasDerivAt v (deriv v x) x) :
    ContinuousOn (w u v) (Set.Icc (0 : ℝ) 1) := by
  refine continuousOn_of_forall_continuousAt ?_
  intro x hx
  have hxJ : x ∈ J := hJ_sub hx
  have h_cont_u : ContinuousAt u x := (hu x hxJ).continuousAt
  have h_cont_v : ContinuousAt v x := (hv x hxJ).continuousAt
  have h_cont_w : ContinuousAt (w u v) x := by
    simpa [w] using h_cont_u.sub h_cont_v
  exact h_cont_w

/-- **First derivative of the difference on the interior.** For every `x ∈ (0, 1)`,
the function `w = u - v` has derivative `deriv u x - deriv v x` within `(0, 1)` at
`x`. -/
theorem w_hasDerivWithinAt_first
    (J : Set ℝ) (hJ_sub : Set.Icc (0 : ℝ) 1 ⊆ J)
    (u v : ℝ → ℝ)
    (hu : ∀ x ∈ J, HasDerivAt u (deriv u x) x)
    (hv : ∀ x ∈ J, HasDerivAt v (deriv v x) x) :
    ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt (w u v) (deriv u x - deriv v x) (Set.Ioo (0 : ℝ) 1) x := by
  intro x hx
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by
    rcases hx with ⟨hx0, hx1⟩
    exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  have hxJ : x ∈ J := hJ_sub hxIcc
  have hderiv_u : HasDerivAt u (deriv u x) x := hu x hxJ
  have hderiv_v : HasDerivAt v (deriv v x) x := hv x hxJ
  have hderiv_sub : HasDerivAt (u - v) (deriv u x - deriv v x) x :=
    hderiv_u.sub hderiv_v
  simpa [w] using hderiv_sub.hasDerivWithinAt

/-- **Second derivative of the difference on the interior.** For every `x ∈ (0, 1)`,
the function `deriv u - deriv v` has derivative
`deriv (deriv u) x - deriv (deriv v) x` within `(0, 1)` at `x`. -/
theorem w_hasDerivWithinAt_second
    (J : Set ℝ) (hJ_sub : Set.Icc (0 : ℝ) 1 ⊆ J)
    (u v : ℝ → ℝ)
    (hu' : ∀ x ∈ J, HasDerivAt (deriv u) (deriv (deriv u) x) x)
    (hv' : ∀ x ∈ J, HasDerivAt (deriv v) (deriv (deriv v) x) x) :
    ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt (deriv u - deriv v)
        (deriv (deriv u) x - deriv (deriv v) x) (Set.Ioo (0 : ℝ) 1) x := by
  intro x hx
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by
    rcases hx with ⟨hx_left, hx_right⟩
    exact ⟨by linarith, by linarith⟩
  have hxJ : x ∈ J := hJ_sub hxIcc
  have h_deriv_u : HasDerivAt (deriv u) (deriv (deriv u) x) x := hu' x hxJ
  have h_deriv_v : HasDerivAt (deriv v) (deriv (deriv v) x) x := hv' x hxJ
  have h_sub : HasDerivAt (deriv u - deriv v) (deriv (deriv u) x - deriv (deriv v) x) x :=
    h_deriv_u.sub h_deriv_v
  exact h_sub.hasDerivWithinAt

/-- **Nonnegativity of the second derivative.** For every `x ∈ (0, 1)`,
`0 ≤ deriv (deriv u) x - deriv (deriv v) x`. -/
theorem w_second_deriv_nonneg
    (u v : ℝ → ℝ)
    (hineq : ∀ x ∈ Set.Ioo (0 : ℝ) 1, -deriv (deriv u) x ≤ -deriv (deriv v) x) :
    ∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ deriv (deriv u) x - deriv (deriv v) x := by
  intro x hx
  have h := hineq x hx
  have h' : deriv (deriv v) x ≤ deriv (deriv u) x := by
    linarith
  rw [sub_nonneg]
  exact h'

/-- **The difference is convex on `[0, 1]`.** Under the `C²` and second-derivative
sign hypotheses, `w = u - v` is convex on `[0, 1]`. -/
theorem w_convexOn
    (J : Set ℝ) (hJ_sub : Set.Icc (0 : ℝ) 1 ⊆ J)
    (u v : ℝ → ℝ)
    (hu : ∀ x ∈ J, HasDerivAt u (deriv u x) x)
    (hu' : ∀ x ∈ J, HasDerivAt (deriv u) (deriv (deriv u) x) x)
    (hv : ∀ x ∈ J, HasDerivAt v (deriv v x) x)
    (hv' : ∀ x ∈ J, HasDerivAt (deriv v) (deriv (deriv v) x) x)
    (hineq : ∀ x ∈ Set.Ioo (0 : ℝ) 1, -deriv (deriv u) x ≤ -deriv (deriv v) x) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (w u v) := by
  have hD : Convex ℝ (Set.Icc (0 : ℝ) 1) := convex_Icc (0 : ℝ) 1
  have hf : ContinuousOn (w u v) (Set.Icc (0 : ℝ) 1) :=
    w_continuousOn J hJ_sub u v hu hv
  set f' := fun x : ℝ => deriv u x - deriv v x with hf'
  set f'' := fun x : ℝ => deriv (deriv u) x - deriv (deriv v) x with hf''
  have hf'_deriv : ∀ x ∈ interior (Set.Icc (0 : ℝ) 1),
      HasDerivWithinAt (w u v) (f' x) (interior (Set.Icc (0 : ℝ) 1)) x := by
    intro x hx
    rw [interior_Icc] at hx ⊢
    exact w_hasDerivWithinAt_first J hJ_sub u v hu hv x hx
  have hf''_deriv : ∀ x ∈ interior (Set.Icc (0 : ℝ) 1),
      HasDerivWithinAt f' (f'' x) (interior (Set.Icc (0 : ℝ) 1)) x := by
    intro x hx
    rw [interior_Icc] at hx ⊢
    exact w_hasDerivWithinAt_second J hJ_sub u v hu' hv' x hx
  have hf''_nonneg : ∀ x ∈ interior (Set.Icc (0 : ℝ) 1), 0 ≤ f'' x := by
    intro x hx
    rw [interior_Icc] at hx
    exact w_second_deriv_nonneg u v hineq x hx
  exact convexOn_of_hasDerivWithinAt2_nonneg hD hf hf'_deriv hf''_deriv hf''_nonneg

/-- **A convex function nonpositive at the endpoints is nonpositive.** A function `f`
convex on `[0, 1]` with `f 0 ≤ 0` and `f 1 ≤ 0` satisfies `f x ≤ 0` for all
`x ∈ [0, 1]`. -/
theorem convexOn_Icc_nonpos_of_endpoints
    (f : ℝ → ℝ) (hf : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) f)
    (h0 : f 0 ≤ 0) (h1 : f 1 ≤ 0) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, f x ≤ 0 := by
  intro x hx
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨by norm_num, by norm_num⟩
  have h1mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨by norm_num, by norm_num⟩
  have hxmax : f x ≤ max (f 0) (f 1) :=
    hf.le_max_of_mem_Icc h0mem h1mem hx
  have hmax0 : max (f 0) (f 1) ≤ 0 := max_le h0 h1
  exact le_trans hxmax hmax0



end ODE
end Analysis
end LeanEval
