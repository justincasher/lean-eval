import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.Convex.Function
import EvalTools.Markers

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
  sorry

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
  sorry

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
  sorry

/-- **Nonnegativity of the second derivative.** For every `x ∈ (0, 1)`,
`0 ≤ deriv (deriv u) x - deriv (deriv v) x`. -/
theorem w_second_deriv_nonneg
    (u v : ℝ → ℝ)
    (hineq : ∀ x ∈ Set.Ioo (0 : ℝ) 1, -deriv (deriv u) x ≤ -deriv (deriv v) x) :
    ∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ deriv (deriv u) x - deriv (deriv v) x := by
  sorry

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
  sorry

/-- **A convex function nonpositive at the endpoints is nonpositive.** A function `f`
convex on `[0, 1]` with `f 0 ≤ 0` and `f 1 ≤ 0` satisfies `f x ≤ 0` for all
`x ∈ [0, 1]`. -/
theorem convexOn_Icc_nonpos_of_endpoints
    (f : ℝ → ℝ) (hf : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) f)
    (h0 : f 0 ≤ 0) (h1 : f 1 ≤ 0) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, f x ≤ 0 := by
  sorry

/-- **Comparison principle for the Dirichlet BVP.** If two functions are `C²` on an open
interval `J` containing `[0, 1]`, satisfy `-u'' ≤ -v''` on the interior, and are ordered
at the boundary, then `u ≤ v` throughout `[0, 1]`. -/
@[eval_problem]
theorem bvp_comparison
    (J : Set ℝ) (hJ_open : IsOpen J) (hJ_sub : Set.Icc (0 : ℝ) 1 ⊆ J)
    (u v : ℝ → ℝ)
    (hu : ∀ x ∈ J, HasDerivAt u (deriv u x) x)
    (hu' : ∀ x ∈ J, HasDerivAt (deriv u) (deriv (deriv u) x) x)
    (hv : ∀ x ∈ J, HasDerivAt v (deriv v x) x)
    (hv' : ∀ x ∈ J, HasDerivAt (deriv v) (deriv (deriv v) x) x)
    (hineq : ∀ x ∈ Set.Ioo (0 : ℝ) 1, -deriv (deriv u) x ≤ -deriv (deriv v) x)
    (hu0 : u 0 ≤ v 0) (hu1 : u 1 ≤ v 1) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, u x ≤ v x := by
  sorry

end ODE
end Analysis
end LeanEval
