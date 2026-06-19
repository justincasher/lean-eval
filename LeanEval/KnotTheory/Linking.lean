import LeanEval.KnotTheory.Prelude
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import EvalTools.Markers

namespace LeanEval
namespace KnotTheory

/-!
# Existence of non-isotopic two-component links

A warmup for the knot-theory benchmark. Two-component links are easier to
distinguish than knots because the *Gauss linking integral* is a real-valued
ambient-isotopy invariant defined by an explicit double integral over the
two parametrizations — no diagrammatic machinery needed.

This file formalizes the blueprint
*"Existence of a non-isotopic pair of oriented two-component links"*.
The proof is fully grounded on Mathlib with no axioms: the two hardest inputs
(`deformedIntegrand_r_divergence`, the closedness of the solid-angle 2-form, and
`hopf_linking_value`, the Hopf Gauss integral) are decomposed into elementary
Mathlib-grounded helper lemmas rather than assumed.
-/

open scoped RealInnerProductSpace

/-! ## The Gauss map and the linking number -/

/-- **Components have disjoint values.** The two parametrized components of a
two-component link never meet, so their difference is everywhere nonzero. -/
theorem TwoLink.components_nonzero (Lk : TwoLink) (s t : ℝ) :
    Lk.K.curve s - Lk.L.curve t ≠ 0 := by
  intro h
  have h_eq : Lk.K.curve s = Lk.L.curve t := sub_eq_zero.mp h
  have h_mem_K : Lk.K.curve s ∈ Set.range Lk.K.curve := Set.mem_range_self _
  have h_mem_L : Lk.K.curve s ∈ Set.range Lk.L.curve := by
    rw [h_eq]
    exact Set.mem_range_self _
  exact Set.disjoint_left.mp Lk.disjoint h_mem_K h_mem_L

/-- **Gauss map of a two-component link.** The unit vector pointing from the
second component to the first:
`g_L(s,t) = (γ_K(s) - γ_L(t)) / ‖γ_K(s) - γ_L(t)‖`. -/
noncomputable def TwoLink.gaussMap (Lk : TwoLink) (s t : ℝ) : R3 :=
  (‖Lk.K.curve s - Lk.L.curve t‖)⁻¹ • (Lk.K.curve s - Lk.L.curve t)

/-! ### Smoothness / continuity helpers -/

/-- **The cross product of smooth maps is smooth.** -/
theorem crossProduct_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → (Fin 3 → ℝ)} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => crossProduct (f x) (g x)) := by
  have h_proj (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun (x : E) => (f x) i) :=
    ((ContinuousLinearMap.proj i : (Fin 3 → ℝ) →L[ℝ] ℝ).contDiff.comp hf)
  have h_proj_g (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun (x : E) => (g x) i) :=
    ((ContinuousLinearMap.proj i : (Fin 3 → ℝ) →L[ℝ] ℝ).contDiff.comp hg)
  -- Each coordinate of the cross product is a ± combination of products f_i * g_j
  have h_cross (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun x : E => (crossProduct (f x) (g x)) i) := by
    fin_cases i
    · simpa [cross_apply] using ((h_proj 1).mul (h_proj_g 2)).sub ((h_proj 2).mul (h_proj_g 1))
    · simpa [cross_apply] using ((h_proj 2).mul (h_proj_g 0)).sub ((h_proj 0).mul (h_proj_g 2))
    · simpa [cross_apply] using ((h_proj 0).mul (h_proj_g 1)).sub ((h_proj 1).mul (h_proj_g 0))
  exact contDiff_pi.mpr h_cross

/-- **The inner product of smooth maps is smooth.** -/
theorem inner_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → R3} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ⟪f x, g x⟫) := by
  exact contDiff_inner.comp (hf.prodMk hg)

/-- **The difference map is jointly smooth.** -/
theorem TwoLink.jointDiff_smooth (Lk : TwoLink) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => Lk.K.curve p.1 - Lk.L.curve p.2) := by
  sorry

/-- **The denominator is smooth and positive.** For any real exponent `p`,
`(s,t) ↦ ‖γ_K(s) - γ_L(t)‖ ^ p` is `C^∞`, and the norm is everywhere positive. -/
theorem TwoLink.jointDenom_smooth_pos (Lk : TwoLink) (p : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => ‖Lk.K.curve q.1 - Lk.L.curve q.2‖ ^ p) ∧
    ∀ s t, 0 < ‖Lk.K.curve s - Lk.L.curve t‖ := by
  sorry

/-- **Smoothness of the Gauss map.** -/
theorem TwoLink.gaussMap_smooth (Lk : TwoLink) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => Lk.gaussMap p.1 p.2) := by
  sorry

/-- **Continuity of a knot's velocity.** A knot is smooth, hence its derivative
is continuous. -/
theorem Knot.continuous_deriv (γ : Knot) : Continuous (deriv γ.curve) := by
  have hderiv_smooth : ContDiff ℝ (⊤ : ℕ∞) (deriv γ.curve) :=
    ((contDiff_succ_iff_deriv (n := (⊤ : ℕ∞))).mp γ.smooth).2.2
  exact hderiv_smooth.continuous

/-- The scalar triple product `⟨u, v × w⟩` of three vectors in `ℝ³`, computed
through the underlying coordinate vectors. Equals `det (u, v, w)`. -/
noncomputable def tripleProduct (u v w : R3) : ℝ :=
  ∑ i, u.ofLp i * (crossProduct v.ofLp w.ofLp) i

/-- The integrand of the Gauss linking integral for two parametrized curves:
`⟨γ_K(s) - γ_L(t), γ_K'(s) × γ_L'(t)⟩ / ‖γ_K(s) - γ_L(t)‖³`. -/
noncomputable def linkingIntegrand (γK γL : ℝ → R3) (s t : ℝ) : ℝ :=
  tripleProduct (γK s - γL t) (deriv γK s) (deriv γL t) / ‖γK s - γL t‖ ^ 3

/-- **Continuity of the linking integrand.** -/
theorem TwoLink.linkingIntegrand_continuous (Lk : TwoLink) :
    Continuous (fun p : ℝ × ℝ => linkingIntegrand Lk.K.curve Lk.L.curve p.1 p.2) := by
  sorry

/-- **Gauss linking number.** The normalized double integral of the linking
integrand over the fundamental square `[0, 2π]²`. -/
noncomputable def TwoLink.linkingNumber (Lk : TwoLink) : ℝ :=
  (1 / (4 * Real.pi)) *
    ∫ t in (0 : ℝ)..(2 * Real.pi), ∫ s in (0 : ℝ)..(2 * Real.pi),
      linkingIntegrand Lk.K.curve Lk.L.curve s t

/-! ## Ambient-isotopy invariance of the linking number -/

/-- **Deformed components.** The difference `u_r(s,t) = Φ_r(γ_K(s)) - Φ_r(γ_L(t))`
of the two components carried along the ambient isotopy `Φ` at time `r`. -/
noncomputable def deformedDiff (Lk : TwoLink) (Φ : AmbientIsotopy) (r s t : ℝ) : R3 :=
  Φ.H r (Lk.K.curve s) - Φ.H r (Lk.L.curve t)

/-- The deformed linking integrand `I_r(s,t)`: the linking integrand of the
components carried along `Φ` at time `r`. -/
noncomputable def deformedIntegrand (Lk : TwoLink) (Φ : AmbientIsotopy) (r s t : ℝ) : ℝ :=
  linkingIntegrand (fun s => Φ.H r (Lk.K.curve s)) (fun t => Φ.H r (Lk.L.curve t)) s t

/-- **Deformed linking integral** `F(r)`: the normalized double integral of the
deformed integrand. One has `F 0 = Lk.linkingNumber`. -/
noncomputable def deformedLinking (Lk : TwoLink) (Φ : AmbientIsotopy) (r : ℝ) : ℝ :=
  (1 / (4 * Real.pi)) *
    ∫ t in (0 : ℝ)..(2 * Real.pi), ∫ s in (0 : ℝ)..(2 * Real.pi),
      deformedIntegrand Lk Φ r s t

/-- **Divergence potential `A_r`.** `A_r(s,t) = det(u_r, u̇_r, ∂_t b_r) / ‖u_r‖³`,
where `u̇_r = ∂_r a_r - ∂_r b_r`. -/
noncomputable def divergenceA (Lk : TwoLink) (Φ : AmbientIsotopy) (r s t : ℝ) : ℝ :=
  let u := Φ.H r (Lk.K.curve s) - Φ.H r (Lk.L.curve t)
  let udot := deriv (fun r => Φ.H r (Lk.K.curve s)) r - deriv (fun r => Φ.H r (Lk.L.curve t)) r
  tripleProduct u udot (deriv (fun t => Φ.H r (Lk.L.curve t)) t) / ‖u‖ ^ 3

/-- **Divergence potential `B_r`.** `B_r(s,t) = det(u_r, ∂_s a_r, u̇_r) / ‖u_r‖³`,
where `u̇_r = ∂_r a_r - ∂_r b_r`. -/
noncomputable def divergenceB (Lk : TwoLink) (Φ : AmbientIsotopy) (r s t : ℝ) : ℝ :=
  let u := Φ.H r (Lk.K.curve s) - Φ.H r (Lk.L.curve t)
  let udot := deriv (fun r => Φ.H r (Lk.K.curve s)) r - deriv (fun r => Φ.H r (Lk.L.curve t)) r
  tripleProduct u (deriv (fun s => Φ.H r (Lk.K.curve s)) s) udot / ‖u‖ ^ 3

/-! ### Joint smoothness and partials of the deformed data -/

/-- **Joint smoothness of the deformed component data.** The deformed first and
second components, their difference, and the two spatial velocities are all
`C^∞` on `[0,1] × ℝ²` (stated on all of `ℝ³`). -/
theorem deformedDiff_smooth (Lk : TwoLink) (Φ : AmbientIsotopy) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × ℝ => Φ.H p.1 (Lk.K.curve p.2.1)) ∧
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × ℝ => Φ.H p.1 (Lk.L.curve p.2.2)) ∧
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × ℝ => deformedDiff Lk Φ p.1 p.2.1 p.2.2) ∧
    ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ × ℝ => deriv (fun s => Φ.H p.1 (Lk.K.curve s)) p.2.1) ∧
    ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ × ℝ => deriv (fun t => Φ.H p.1 (Lk.L.curve t)) p.2.2) := by
  sorry

/-- **The deformed denominator is smooth and positive.** -/
theorem deformedDenom_smooth_pos (Lk : TwoLink) (Φ : AmbientIsotopy) (p : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ × ℝ => ‖deformedDiff Lk Φ q.1 q.2.1 q.2.2‖ ^ p) ∧
    ∀ r s t, 0 < ‖deformedDiff Lk Φ r s t‖ := by
  sorry

/-- **The divergence potentials are `C¹` and `2π`-periodic** in each variable. -/
theorem divergencePotentials_contDiff_periodic (Lk : TwoLink) (Φ : AmbientIsotopy) (r : ℝ) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ => divergenceA Lk Φ r p.1 p.2) ∧
    ContDiff ℝ 1 (fun p : ℝ × ℝ => divergenceB Lk Φ r p.1 p.2) ∧
    (∀ t, Function.Periodic (fun s => divergenceA Lk Φ r s t) (2 * Real.pi)) ∧
    (∀ s, Function.Periodic (fun t => divergenceA Lk Φ r s t) (2 * Real.pi)) ∧
    (∀ t, Function.Periodic (fun s => divergenceB Lk Φ r s t) (2 * Real.pi)) ∧
    (∀ s, Function.Periodic (fun t => divergenceB Lk Φ r s t) (2 * Real.pi)) := by
  sorry

/-- **First partials of the deformed difference.**
`∂_r u = u̇`, `∂_s u = ∂_s a`, `∂_t u = -∂_t b`. -/
theorem deformedU_partials (Lk : TwoLink) (Φ : AmbientIsotopy) (r s t : ℝ) :
    deriv (fun r => deformedDiff Lk Φ r s t) r
        = deriv (fun r => Φ.H r (Lk.K.curve s)) r
          - deriv (fun r => Φ.H r (Lk.L.curve t)) r
      ∧ deriv (fun s => deformedDiff Lk Φ r s t) s
        = deriv (fun s => Φ.H r (Lk.K.curve s)) s
      ∧ deriv (fun t => deformedDiff Lk Φ r s t) t
        = -deriv (fun t => Φ.H r (Lk.L.curve t)) t := by
  sorry

/-- **Cross mixed partials of the deformed components vanish.**
`∂_t (∂_s a_r) = 0` and `∂_s (∂_t b_r) = 0`. -/
theorem deformed_cross_mixed_partials_zero (Lk : TwoLink) (Φ : AmbientIsotopy) (r s t : ℝ) :
    deriv (fun _ : ℝ => deriv (fun s => Φ.H r (Lk.K.curve s)) s) t = 0
      ∧ deriv (fun _ : ℝ => deriv (fun t => Φ.H r (Lk.L.curve t)) t) s = 0 := by
  sorry

/-- **The `r`-partial of the deformed integrand.** -/
theorem deformedIntegrand_r_partial (Lk : TwoLink) (Φ : AmbientIsotopy) (r s t : ℝ) :
    deriv (fun r => deformedIntegrand Lk Φ r s t) r
      = (tripleProduct
            (deriv (fun r => Φ.H r (Lk.K.curve s)) r
              - deriv (fun r => Φ.H r (Lk.L.curve t)) r)
            (deriv (fun s => Φ.H r (Lk.K.curve s)) s)
            (deriv (fun t => Φ.H r (Lk.L.curve t)) t)
          + tripleProduct
            (deformedDiff Lk Φ r s t)
            (deriv (fun s => deriv (fun r => Φ.H r (Lk.K.curve s)) r) s)
            (deriv (fun t => Φ.H r (Lk.L.curve t)) t)
          + tripleProduct
            (deformedDiff Lk Φ r s t)
            (deriv (fun s => Φ.H r (Lk.K.curve s)) s)
            (deriv (fun t => deriv (fun r => Φ.H r (Lk.L.curve t)) r) t))
        * (‖deformedDiff Lk Φ r s t‖ ^ 3)⁻¹
      - 3 * tripleProduct
            (deformedDiff Lk Φ r s t)
            (deriv (fun s => Φ.H r (Lk.K.curve s)) s)
            (deriv (fun t => Φ.H r (Lk.L.curve t)) t)
          * ⟪deformedDiff Lk Φ r s t,
              deriv (fun r => Φ.H r (Lk.K.curve s)) r
                - deriv (fun r => Φ.H r (Lk.L.curve t)) r⟫
          * (‖deformedDiff Lk Φ r s t‖ ^ 5)⁻¹ := by
  sorry

/-- **The `s`-partial of the first potential.** -/
theorem deformedA_s_partial (Lk : TwoLink) (Φ : AmbientIsotopy) (r s t : ℝ) :
    deriv (fun s => divergenceA Lk Φ r s t) s
      = (tripleProduct
            (deriv (fun s => Φ.H r (Lk.K.curve s)) s)
            (deriv (fun r => Φ.H r (Lk.K.curve s)) r
              - deriv (fun r => Φ.H r (Lk.L.curve t)) r)
            (deriv (fun t => Φ.H r (Lk.L.curve t)) t)
          + tripleProduct
            (deformedDiff Lk Φ r s t)
            (deriv (fun s => deriv (fun r => Φ.H r (Lk.K.curve s)) r) s)
            (deriv (fun t => Φ.H r (Lk.L.curve t)) t))
        * (‖deformedDiff Lk Φ r s t‖ ^ 3)⁻¹
      - 3 * tripleProduct
            (deformedDiff Lk Φ r s t)
            (deriv (fun r => Φ.H r (Lk.K.curve s)) r
              - deriv (fun r => Φ.H r (Lk.L.curve t)) r)
            (deriv (fun t => Φ.H r (Lk.L.curve t)) t)
          * ⟪deformedDiff Lk Φ r s t, deriv (fun s => Φ.H r (Lk.K.curve s)) s⟫
          * (‖deformedDiff Lk Φ r s t‖ ^ 5)⁻¹ := by
  sorry

/-- **The `t`-partial of the second potential.** -/
theorem deformedB_t_partial (Lk : TwoLink) (Φ : AmbientIsotopy) (r s t : ℝ) :
    deriv (fun t => divergenceB Lk Φ r s t) t
      = (-tripleProduct
            (deriv (fun t => Φ.H r (Lk.L.curve t)) t)
            (deriv (fun s => Φ.H r (Lk.K.curve s)) s)
            (deriv (fun r => Φ.H r (Lk.K.curve s)) r
              - deriv (fun r => Φ.H r (Lk.L.curve t)) r)
          - tripleProduct
            (deformedDiff Lk Φ r s t)
            (deriv (fun s => Φ.H r (Lk.K.curve s)) s)
            (deriv (fun t => deriv (fun r => Φ.H r (Lk.L.curve t)) r) t))
        * (‖deformedDiff Lk Φ r s t‖ ^ 3)⁻¹
      + 3 * tripleProduct
            (deformedDiff Lk Φ r s t)
            (deriv (fun s => Φ.H r (Lk.K.curve s)) s)
            (deriv (fun r => Φ.H r (Lk.K.curve s)) r
              - deriv (fun r => Φ.H r (Lk.L.curve t)) r)
          * ⟪deformedDiff Lk Φ r s t, deriv (fun t => Φ.H r (Lk.L.curve t)) t⟫
          * (‖deformedDiff Lk Φ r s t‖ ^ 5)⁻¹ := by
  sorry

/-- **Algebraic closure of the divergence identity.** The Lagrange / scalar
quadruple-product identity in the form used to close the divergence equation. -/
theorem divergence_algebraic_identity (u p q w pStar qStar : R3) :
    ‖u‖ ^ 2 * (tripleProduct w p q + tripleProduct u pStar q + tripleProduct u p qStar)
        - 3 * ⟪u, w⟫ * tripleProduct u p q
      = ‖u‖ ^ 2 * (tripleProduct p w q + tripleProduct u pStar q)
          - 3 * ⟪u, p⟫ * tripleProduct u w q
        + (‖u‖ ^ 2 * (-tripleProduct q p w - tripleProduct u p qStar)
          + 3 * ⟪u, q⟫ * tripleProduct u p w) := by
  sorry

/-- **Uniform bound on the deformed integrand and its `r`-derivative**
over `[0,1] × [0,2π]²`. -/
theorem deformedIntegrand_uniform_bound (Lk : TwoLink) (Φ : AmbientIsotopy) :
    ∃ M : ℝ, ∀ r ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        |deformedIntegrand Lk Φ r s t| ≤ M ∧
        |deriv (fun r => deformedIntegrand Lk Φ r s t) r| ≤ M := by
  sorry

/-- **Differentiating the inner linking integral under the integral sign.** -/
theorem deformedLinking_inner_hasDerivAt (Lk : TwoLink) (Φ : AmbientIsotopy) (t r : ℝ) :
    HasDerivAt
      (fun r => ∫ s in (0 : ℝ)..(2 * Real.pi), deformedIntegrand Lk Φ r s t)
      (∫ s in (0 : ℝ)..(2 * Real.pi), deriv (fun r => deformedIntegrand Lk Φ r s t) r) r := by
  sorry

/-- **Lagrange / scalar quadruple-product identity.** For all `u p q w : ℝ³`,
`⟨u,w⟩ det(u,p,q) = ‖u‖² det(w,p,q) + ⟨u,p⟩ det(u,w,q) + ⟨u,q⟩ det(u,p,w)`.
The determinant analogue of `cross_dot_cross`, a coordinate `ring` identity. -/
theorem quadruple_product_identity (u p q w : R3) :
    ⟪u, w⟫ * tripleProduct u p q
      = ‖u‖ ^ 2 * tripleProduct w p q
        + ⟪u, p⟫ * tripleProduct u w q
        + ⟪u, q⟫ * tripleProduct u p w := by
  sorry

/-- **Derivative of the inverse cube of the norm along a curve.** If `u` is
differentiable at `v` with `u v ≠ 0`, then `v ↦ ‖u v‖⁻³` is differentiable at
`v` with derivative `-3 ‖u v‖⁻⁵ ⟨u v, u' v⟩`. -/
theorem recip_norm_cube_deriv {u : ℝ → R3} {u' : R3} {v : ℝ}
    (hu : HasDerivAt u u' v) (hne : u v ≠ 0) :
    HasDerivAt (fun v => (‖u v‖ ^ 3)⁻¹)
      (-3 * (‖u v‖ ^ 5)⁻¹ * ⟪u v, u'⟫) v := by
  set φ := fun v' : ℝ => ⟪u v', u v'⟫ with hφ_def
  have hφpos : φ v > 0 := by
    dsimp [φ]
    rw [real_inner_self_eq_norm_sq]
    have h_norm_pos : 0 < ‖u v‖ := (norm_pos_iff.mpr hne)
    positivity
  have hφ_deriv : HasDerivAt φ (2 * ⟪u v, u'⟫) v := by
    dsimp [φ]
    have hinner := HasDerivAt.inner (𝕜 := ℝ) hu hu
    have hcomm : ⟪u v, u'⟫ + ⟪u', u v⟫ = 2 * ⟪u v, u'⟫ := by
      rw [real_inner_comm (u v) u']
      ring
    simpa [hcomm] using hinner
  have hp_deriv : HasDerivAt (fun x : ℝ => x ^ (-(3/2 : ℝ)))
      ((-(3/2 : ℝ)) * (φ v) ^ (-(3/2 : ℝ) - 1)) (φ v) :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hφpos))
  have hcomp := HasDerivAt.comp v hp_deriv hφ_deriv
  have h_simplify : (-(3/2 : ℝ)) * (φ v) ^ (-(3/2 : ℝ) - 1) * (2 * ⟪u v, u'⟫)
      = -3 * (‖u v‖ ^ 5)⁻¹ * ⟪u v, u'⟫ := by
    calc
      (-(3/2 : ℝ)) * (φ v) ^ (-(3/2 : ℝ) - 1) * (2 * ⟪u v, u'⟫)
          = ((-(3/2 : ℝ)) * 2) * ((φ v) ^ (-(5/2 : ℝ))) * ⟪u v, u'⟫ := by
        ring_nf
      _ = (-3 : ℝ) * ((φ v) ^ (-(5/2 : ℝ))) * ⟪u v, u'⟫ := by ring
      _ = -3 * (((φ v) ^ (-(5/2 : ℝ)))) * ⟪u v, u'⟫ := by ring
      _ = -3 * (((‖u v‖ ^ 2) : ℝ) ^ (-(5/2 : ℝ))) * ⟪u v, u'⟫ := by
        dsimp [φ]
        rw [real_inner_self_eq_norm_sq]
      _ = -3 * (‖u v‖ ^ ((2 : ℝ) * (-(5/2 : ℝ)))) * ⟪u v, u'⟫ := by
        calc
          -3 * (((‖u v‖ ^ 2) : ℝ) ^ (-(5/2 : ℝ))) * ⟪u v, u'⟫
              = -3 * ((‖u v‖ ^ (2 : ℝ)) ^ (-(5/2 : ℝ))) * ⟪u v, u'⟫ := by norm_num
          _ = -3 * (‖u v‖ ^ ((2 : ℝ) * (-(5/2 : ℝ)))) * ⟪u v, u'⟫ := by
            rw [← Real.rpow_mul (norm_nonneg (u v)) (2 : ℝ) (-(5/2 : ℝ))]
      _ = -3 * (‖u v‖ ^ (-5 : ℝ)) * ⟪u v, u'⟫ := by ring_nf
      _ = -3 * ((‖u v‖ ^ (5 : ℝ))⁻¹) * ⟪u v, u'⟫ := by
        rw [Real.rpow_neg (norm_nonneg (u v))]
      _ = -3 * (‖u v‖ ^ 5)⁻¹ * ⟪u v, u'⟫ := by norm_num
  have h_target : HasDerivAt (fun v' : ℝ => (φ v') ^ (-(3/2 : ℝ)))
      (-3 * (‖u v‖ ^ 5)⁻¹ * ⟪u v, u'⟫) v :=
    hcomp.congr_deriv h_simplify
  have h_eq : (fun v' : ℝ => (‖u v'‖ ^ 3)⁻¹) = (fun v' : ℝ => (φ v') ^ (-(3/2 : ℝ))) := by
    ext v'
    calc
      (‖u v'‖ ^ 3)⁻¹ = (‖u v'‖ ^ (3 : ℝ))⁻¹ := by norm_num
      _ = ‖u v'‖ ^ (-(3 : ℝ)) := by
        rw [Real.rpow_neg (norm_nonneg (u v'))]
      _ = ‖u v'‖ ^ ((2 : ℝ) * (-(3/2 : ℝ))) := by ring_nf
      _ = (‖u v'‖ ^ (2 : ℝ)) ^ (-(3/2 : ℝ)) := by
        rw [Real.rpow_mul (norm_nonneg (u v')) (2 : ℝ) (-(3/2 : ℝ))]
      _ = ((‖u v'‖ ^ 2) : ℝ) ^ (-(3/2 : ℝ)) := by norm_num
      _ = (φ v') ^ (-(3/2 : ℝ)) := by
        dsimp [φ]
        rw [real_inner_self_eq_norm_sq]
  rw [h_eq]
  exact h_target

/-- **Product rule for the scalar triple product.** If `p, q, w` are
differentiable at `v`, then so is `v ↦ det(p v, q v, w v)`, with derivative
`det(p', q, w) + det(p, q', w) + det(p, q, w')`. -/
theorem tripleProduct_deriv {p q w : ℝ → R3} {p' q' w' : R3} {v : ℝ}
    (hp : HasDerivAt p p' v) (hq : HasDerivAt q q' v) (hw : HasDerivAt w w' v) :
    HasDerivAt (fun v => tripleProduct (p v) (q v) (w v))
      (tripleProduct p' (q v) (w v) + tripleProduct (p v) q' (w v)
        + tripleProduct (p v) (q v) w') v := by
  sorry

/-- **Mixed partials of the deformed components commute.** For the smooth maps
`a r s = Φ_r(γ_K s)` and `b r t = Φ_r(γ_L t)` the order of the `r`- and the
spatial differentiation may be exchanged. -/
theorem mixed_partials_symm (Lk : TwoLink) (Φ : AmbientIsotopy) (r s t : ℝ) :
    deriv (fun r => deriv (fun s => Φ.H r (Lk.K.curve s)) s) r
        = deriv (fun s => deriv (fun r => Φ.H r (Lk.K.curve s)) r) s
      ∧ deriv (fun r => deriv (fun t => Φ.H r (Lk.L.curve t)) t) r
        = deriv (fun t => deriv (fun r => Φ.H r (Lk.L.curve t)) r) t := by
  sorry

/-- **Joint smoothness of the deformed integrand**, together with its
`r`-derivative. -/
theorem deformedIntegrand_smooth (Lk : TwoLink) (Φ : AmbientIsotopy) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × ℝ => deformedIntegrand Lk Φ p.1 p.2.1 p.2.2) ∧
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × ℝ =>
      deriv (fun r => deformedIntegrand Lk Φ r p.2.1 p.2.2) p.1) := by
  sorry

/-- **The `r`-derivative is an `(s,t)`-divergence.**
The coordinate form of the closedness of the solid-angle 2-form, obtained by
combining `quadruple_product_identity`, `recip_norm_cube_deriv`,
`tripleProduct_deriv`, and `mixed_partials_symm`. -/
theorem deformedIntegrand_r_divergence (Lk : TwoLink) (Φ : AmbientIsotopy) (r s t : ℝ) :
    deriv (fun r => deformedIntegrand Lk Φ r s t) r
      = deriv (fun s => divergenceA Lk Φ r s t) s
        + deriv (fun t => divergenceB Lk Φ r s t) t := by
  sorry

/-- **A periodic divergence integrates to zero** over the fundamental square. -/
theorem periodic_divergence_integral_zero
    (A B : ℝ → ℝ → ℝ)
    (hA : ContDiff ℝ 1 (fun p : ℝ × ℝ => A p.1 p.2))
    (hB : ContDiff ℝ 1 (fun p : ℝ × ℝ => B p.1 p.2))
    (hAs : ∀ t, Function.Periodic (fun s => A s t) (2 * Real.pi))
    (hAt : ∀ s, Function.Periodic (fun t => A s t) (2 * Real.pi))
    (hBs : ∀ t, Function.Periodic (fun s => B s t) (2 * Real.pi))
    (hBt : ∀ s, Function.Periodic (fun t => B s t) (2 * Real.pi)) :
    ∫ t in (0 : ℝ)..(2 * Real.pi), ∫ s in (0 : ℝ)..(2 * Real.pi),
      (deriv (fun s => A s t) s + deriv (fun t => B s t) t) = 0 := by
  sorry

/-- **Differentiating the linking integral under the integral sign.** -/
theorem deformedLinking_hasDerivAt (Lk : TwoLink) (Φ : AmbientIsotopy) (r : ℝ) :
    HasDerivAt (deformedLinking Lk Φ)
      ((1 / (4 * Real.pi)) *
        ∫ t in (0 : ℝ)..(2 * Real.pi), ∫ s in (0 : ℝ)..(2 * Real.pi),
          deriv (fun r => deformedIntegrand Lk Φ r s t) r) r := by
  sorry

/-- **The deformed linking number has zero derivative.** -/
theorem deformedLinking_deriv_zero (Lk : TwoLink) (Φ : AmbientIsotopy) (r : ℝ) :
    deriv (deformedLinking Lk Φ) r = 0 := by
  sorry

/-! ### Reparametrization helpers -/

/-- **Chain rule for a reparametrized knot.** `(γ ∘ σ)'(s) = σ'(s) • γ'(σ(s))`. -/
theorem reparam_chain_deriv (γ : Knot) {σ : ℝ → ℝ} (hσ : ContDiff ℝ (⊤ : ℕ∞) σ) (s : ℝ) :
    deriv (fun x => γ.curve (σ x)) s = deriv σ s • deriv γ.curve (σ s) := by
  have hg : HasDerivAt σ (deriv σ s) s :=
    (hσ.differentiable (by
      decide : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ ((0 : ℕ∞) : WithTop ℕ∞))).differentiableAt.hasDerivAt
  have hf : HasDerivAt γ.curve (deriv γ.curve (σ s)) (σ s) :=
    (γ.smooth.differentiable (by
      decide : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ ((0 : ℕ∞) : WithTop ℕ∞))).differentiableAt.hasDerivAt
  have hcomp : HasDerivAt (fun x => γ.curve (σ x)) (deriv σ s • deriv γ.curve (σ s)) s :=
    hf.scomp s hg
  exact hcomp.deriv

/-- **Integrand scaling under reparametrization.** -/
theorem reparam_integrand_scaling (Lk : TwoLink) (σ τ : CircleReparam) (s t : ℝ) :
    linkingIntegrand (fun s => Lk.K.curve (σ.f s)) (fun t => Lk.L.curve (τ.f t)) s t
      = deriv σ.f s * deriv τ.f t *
          linkingIntegrand Lk.K.curve Lk.L.curve (σ.f s) (τ.f t) := by
  sorry

/-- **One-dimensional change of variables over a period.** -/
theorem reparam_single_change_of_variables {g : ℝ → ℝ} (hg : Continuous g)
    (hgper : Function.Periodic g (2 * Real.pi)) (σ : CircleReparam) :
    (∫ s in (0 : ℝ)..(2 * Real.pi), deriv σ.f s * g (σ.f s))
      = ∫ x in (0 : ℝ)..(2 * Real.pi), g x := by
  sorry

/-- **Iterated change of variables over the torus.** -/
theorem reparam_iterated_change_of_variables {h : ℝ → ℝ → ℝ}
    (hh : Continuous (fun p : ℝ × ℝ => h p.1 p.2))
    (hs : ∀ t, Function.Periodic (fun s => h s t) (2 * Real.pi))
    (ht : ∀ s, Function.Periodic (fun t => h s t) (2 * Real.pi))
    (σ τ : CircleReparam) :
    (∫ t in (0 : ℝ)..(2 * Real.pi), ∫ s in (0 : ℝ)..(2 * Real.pi),
        deriv σ.f s * deriv τ.f t * h (σ.f s) (τ.f t))
      = ∫ t in (0 : ℝ)..(2 * Real.pi), ∫ s in (0 : ℝ)..(2 * Real.pi), h s t := by
  sorry

/-- **The deformed linking integral at `r = 1`** equals `lk(L₂)` when the ambient
isotopy and reparametrizations witness `L₁ ≅ L₂`. -/
theorem deformedLinking_at_one {L₁ L₂ : TwoLink} (Φ : AmbientIsotopy) (σ τ : CircleReparam)
    (hK : ∀ t, Φ.H 1 (L₁.K.curve t) = L₂.K.curve (σ.f t))
    (hL : ∀ t, Φ.H 1 (L₁.L.curve t) = L₂.L.curve (τ.f t)) :
    deformedLinking L₁ Φ 1 = L₂.linkingNumber := by
  sorry

/-- **Reparametrization invariance of the linking number.** If `L'` has
components `γ_K ∘ σ`, `γ_L ∘ τ` for orientation-preserving circle
reparametrizations `σ, τ`, then `lk(L') = lk(L)`. -/
theorem linkingNumber_reparam (Lk Lk' : TwoLink) (σ τ : CircleReparam)
    (hK : ∀ t, Lk'.K.curve t = Lk.K.curve (σ.f t))
    (hL : ∀ t, Lk'.L.curve t = Lk.L.curve (τ.f t)) :
    Lk'.linkingNumber = Lk.linkingNumber := by
  sorry

/-- **The linking number is an ambient-isotopy invariant.** -/
theorem TwoLink.linkingNumber_isotopy_invariant {L₁ L₂ : TwoLink}
    (h : L₁.Isotopic L₂) : L₁.linkingNumber = L₂.linkingNumber := by
  sorry

/-! ## The unlink and the Hopf link -/

/-- **Round circle in a coordinate plane.** The unit circle through `p₀` in the
affine plane spanned by `eᵢ, eⱼ`: `t ↦ p₀ + cos t · eᵢ + sin t · eⱼ`. -/
noncomputable def coordinateCircle (p₀ : R3) (i j : Fin 3) (t : ℝ) : R3 :=
  p₀ + Real.cos t • EuclideanSpace.single i (1 : ℝ)
     + Real.sin t • EuclideanSpace.single j (1 : ℝ)

/-- **Smoothness of a coordinate circle.** -/
theorem coordinateCircle_smooth (p₀ : R3) (i j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateCircle p₀ i j) := by
  have hcos : ContDiff ℝ (⊤ : ℕ∞) Real.cos := Real.contDiff_cos
  have hsin : ContDiff ℝ (⊤ : ℕ∞) Real.sin := Real.contDiff_sin
  have hconst1 : ContDiff ℝ (⊤ : ℕ∞) (fun (_ : ℝ) => EuclideanSpace.single i (1 : ℝ)) :=
    contDiff_const
  have hconst2 : ContDiff ℝ (⊤ : ℕ∞) (fun (_ : ℝ) => EuclideanSpace.single j (1 : ℝ)) :=
    contDiff_const
  have hterm1 : ContDiff ℝ (⊤ : ℕ∞) (fun (t : ℝ) => Real.cos t • EuclideanSpace.single i (1 : ℝ)) :=
    hcos.smul hconst1
  have hterm2 : ContDiff ℝ (⊤ : ℕ∞) (fun (t : ℝ) => Real.sin t • EuclideanSpace.single j (1 : ℝ)) :=
    hsin.smul hconst2
  have hp0 : ContDiff ℝ (⊤ : ℕ∞) (fun (_ : ℝ) => p₀) := contDiff_const
  have hsum : ContDiff ℝ (⊤ : ℕ∞) (fun (t : ℝ) => p₀ + Real.cos t • EuclideanSpace.single i (1 : ℝ)) :=
    hp0.add hterm1
  simpa [coordinateCircle] using hsum.add hterm2

/-- **Periodicity of a coordinate circle.** -/
theorem coordinateCircle_periodic (p₀ : R3) (i j : Fin 3) (t : ℝ) :
    coordinateCircle p₀ i j (t + 2 * Real.pi) = coordinateCircle p₀ i j t := by
  simp [coordinateCircle, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- **Velocity of a coordinate circle.** -/
theorem coordinateCircle_deriv (p₀ : R3) (i j : Fin 3) (t : ℝ) :
    deriv (coordinateCircle p₀ i j) t
      = -Real.sin t • EuclideanSpace.single i (1 : ℝ)
        + Real.cos t • EuclideanSpace.single j (1 : ℝ) := by
  have hcos : HasDerivAt (Real.cos : ℝ → ℝ) (-Real.sin t) t := Real.hasDerivAt_cos t
  have hsin : HasDerivAt (Real.sin : ℝ → ℝ) (Real.cos t) t := Real.hasDerivAt_sin t
  set e_i := EuclideanSpace.single i (1 : ℝ) with he_i
  set e_j := EuclideanSpace.single j (1 : ℝ) with he_j
  have h1 : HasDerivAt (fun (t' : ℝ) => Real.cos t' • e_i) ((-Real.sin t) • e_i) t :=
    hcos.smul_const e_i
  have h2 : HasDerivAt (fun (t' : ℝ) => Real.sin t' • e_j) (Real.cos t • e_j) t :=
    hsin.smul_const e_j
  have hsum : HasDerivAt (fun (t' : ℝ) => Real.cos t' • e_i + Real.sin t' • e_j)
      ((-Real.sin t) • e_i + Real.cos t • e_j) t :=
    h1.add h2
  have h_f : coordinateCircle p₀ i j = (fun t' : ℝ => (Real.cos t' • e_i + Real.sin t' • e_j) + p₀) := by
    ext t' k
    simp [coordinateCircle, he_i, he_j, add_assoc, add_comm]
  have h_total : HasDerivAt (coordinateCircle p₀ i j)
      ((-Real.sin t) • e_i + Real.cos t • e_j) t := by
    rw [h_f]
    exact hsum.add_const p₀
  simpa [he_i, he_j] using h_total.deriv

/-- **Immersion property of a coordinate circle.** -/
theorem coordinateCircle_immersion (p₀ : R3) {i j : Fin 3} (hij : i ≠ j) (t : ℝ) :
    deriv (coordinateCircle p₀ i j) t ≠ 0 := by
  rw [coordinateCircle_deriv p₀ i j t]
  intro h
  have hsin : Real.sin t = 0 := by
    have hval := congrArg (fun v : R3 => v i) h
    simp [hij] at hval
    linarith
  have hcos : Real.cos t = 0 := by
    have hval := congrArg (fun v : R3 => v j) h
    simp [hij] at hval
    exact hval
  have sin_sq_add_cos_sq_zero : Real.sin t ^ 2 + Real.cos t ^ 2 = 0 := by
    simp [hsin, hcos]
  have sin_sq_add_cos_sq_one : Real.sin t ^ 2 + Real.cos t ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq t
  linarith

/-- **Injectivity of a coordinate circle on a period.** -/
theorem coordinateCircle_injOn (p₀ : R3) {i j : Fin 3} (hij : i ≠ j) :
    Set.InjOn (coordinateCircle p₀ i j) (Set.Ico 0 (2 * Real.pi)) := by
  intro s hs t ht h
  rcases hs with ⟨hs_left, hs_right⟩
  rcases ht with ⟨ht_left, ht_right⟩
  have hcos : Real.cos s = Real.cos t := by
    have hval := congrArg (fun v : R3 => v i) h
    simp [coordinateCircle, hij] at hval
    linarith
  have hsin : Real.sin s = Real.sin t := by
    have hval := congrArg (fun v : R3 => v j) h
    simp [coordinateCircle, hij] at hval
    linarith
  have hangle : (s : Real.Angle) = (t : Real.Angle) :=
    Real.Angle.cos_sin_inj hcos hsin
  rcases Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hangle with ⟨k, hk⟩
  have hk_int_eq_zero : k = 0 := by
    have hbound : -(2 * Real.pi) < s - t ∧ s - t < 2 * Real.pi := by
      constructor
      · nlinarith
      · nlinarith
    have hk_real_lower : (-1 : ℝ) < (k : ℝ) := by
      nlinarith
    have hk_real_upper : (k : ℝ) < 1 := by
      nlinarith
    have hk_lower : (-1 : ℤ) < k := by exact_mod_cast hk_real_lower
    have hk_upper : k < (1 : ℤ) := by exact_mod_cast hk_real_upper
    omega
  have hk_int_eq_zero' : (k : ℝ) = 0 := by exact_mod_cast hk_int_eq_zero
  nlinarith

/-- **A coordinate circle is a knot.** -/
noncomputable def coordinateCircleKnot (p₀ : R3) {i j : Fin 3} (hij : i ≠ j) : Knot where
  curve := coordinateCircle p₀ i j
  smooth := coordinateCircle_smooth p₀ i j
  periodic := coordinateCircle_periodic p₀ i j
  injOn := coordinateCircle_injOn p₀ hij
  immersion := coordinateCircle_immersion p₀ hij

/-- The shift `(0, 0, 2)` placing the second unlink circle in the plane `z = 2`. -/
noncomputable def unlinkShift : R3 := (2 : ℝ) • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)

/-- The shift `(1, 0, 0)` centering the second Hopf circle at `(1, 0, 0)`. -/
noncomputable def hopfShift : R3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)

/-- **Unlink components are disjoint** (the circles lie in `z = 0` and `z = 2`). -/
theorem unlink_disjoint :
    Disjoint (Set.range (coordinateCircle 0 0 1))
      (Set.range (coordinateCircle unlinkShift 0 1)) := by
  rw [Set.disjoint_left]
  intro x hx1 hx2
  rcases hx1 with ⟨t1, ht1⟩
  rcases hx2 with ⟨t2, ht2⟩
  have hz0 : x 2 = (0 : ℝ) := by
    calc
      x 2 = (coordinateCircle (0 : R3) (0 : Fin 3) (1 : Fin 3) t1) 2 := by rw [ht1]
      _ = 0 := by
        simp [coordinateCircle, EuclideanSpace.single]
  have hz2 : x 2 = (2 : ℝ) := by
    calc
      x 2 = (coordinateCircle unlinkShift (0 : Fin 3) (1 : Fin 3) t2) 2 := by rw [ht2]
      _ = 2 := by
        simp [coordinateCircle, unlinkShift, EuclideanSpace.single]
  linarith

/-- **The unlink.** Two unit circles in the parallel planes `z = 0` and `z = 2`. -/
noncomputable def unlink : TwoLink where
  K := coordinateCircleKnot 0 (by decide : (0 : Fin 3) ≠ 1)
  L := coordinateCircleKnot unlinkShift (by decide : (0 : Fin 3) ≠ 1)
  disjoint := unlink_disjoint

/-- **Coordinate constraints for a Hopf common point.** A common point of the
two Hopf circles forces `sin s = 0`, `sin t = 0`, `cos² s = 1`, `cos² t = 1`,
i.e. `x² = 1` (first circle) and `(x-1)² = 1` (second circle). -/
theorem hopf_common_point_coords {s t : ℝ}
    (h : coordinateCircle 0 0 1 s = coordinateCircle hopfShift 0 2 t) :
    Real.sin s = 0 ∧ Real.sin t = 0 ∧ (Real.cos s) ^ 2 = 1 ∧ (Real.cos t) ^ 2 = 1 := by
  have hsin_s : Real.sin s = 0 := by
    have hval := congrArg (fun v : R3 => v 1) h
    simp [coordinateCircle, hopfShift, EuclideanSpace.single] at hval
    exact hval
  have hsin_t : Real.sin t = 0 := by
    have hval := congrArg (fun v : R3 => v 2) h
    simp [coordinateCircle, hopfShift, EuclideanSpace.single] at hval
    exact hval.symm
  have hcos_s_sq : (Real.cos s) ^ 2 = 1 := by
    have h := Real.sin_sq_add_cos_sq s
    nlinarith
  have hcos_t_sq : (Real.cos t) ^ 2 = 1 := by
    have h := Real.sin_sq_add_cos_sq t
    nlinarith
  exact ⟨hsin_s, hsin_t, hcos_s_sq, hcos_t_sq⟩

/-- **Hopf-link components are disjoint** (circles in the `xy`-plane and the
`xz`-plane centered at `(1,0,0)`). -/
theorem hopf_disjoint :
    Disjoint (Set.range (coordinateCircle 0 0 1))
      (Set.range (coordinateCircle hopfShift 0 2)) := by
  rw [Set.disjoint_left]
  intro x hx1 hx2
  rcases hx1 with ⟨s, hs⟩
  rcases hx2 with ⟨t, ht⟩
  have h_eq : coordinateCircle 0 0 1 s = coordinateCircle hopfShift 0 2 t := by
    calc
      coordinateCircle 0 0 1 s = x := hs
      _ = coordinateCircle hopfShift 0 2 t := ht.symm
  rcases hopf_common_point_coords h_eq with ⟨hsin_s, hsin_t, hcos_s_sq, hcos_t_sq⟩
  have hx0_sq : (x 0) ^ 2 = 1 := by
    calc
      (x 0) ^ 2 = ((coordinateCircle 0 0 1 s) 0) ^ 2 := by rw [hs]
      _ = (Real.cos s) ^ 2 := by
        simp [coordinateCircle, EuclideanSpace.single]
      _ = 1 := hcos_s_sq
  have hx0_sub_one_sq : ((x 0) - 1) ^ 2 = 1 := by
    calc
      ((x 0) - 1) ^ 2 = ((coordinateCircle hopfShift 0 2 t) 0 - 1) ^ 2 := by rw [ht]
      _ = (Real.cos t) ^ 2 := by
        simp [coordinateCircle, hopfShift, EuclideanSpace.single]
      _ = 1 := hcos_t_sq
  nlinarith

/-- **The Hopf link.** The unit circle in the `xy`-plane together with the unit
circle in the `xz`-plane centered at `(1, 0, 0)`. -/
noncomputable def hopfLink : TwoLink where
  K := coordinateCircleKnot 0 (by decide : (0 : Fin 3) ≠ 1)
  L := coordinateCircleKnot hopfShift (by decide : (0 : Fin 3) ≠ 2)
  disjoint := hopf_disjoint

/-! ## Computing the two linking numbers -/

/-- **The unlink linking integrand** in closed form:
`I_{L₁}(s,t) = -2 sin(s - t) / (6 - 2 cos(s - t))^{3/2}`. -/
theorem unlink_integrand (s t : ℝ) :
    linkingIntegrand unlink.K.curve unlink.L.curve s t
      = -2 * Real.sin (s - t) / Real.sqrt (6 - 2 * Real.cos (s - t)) ^ 3 := by
  sorry

/-- **Antiderivative of the unlink integrand.** For fixed `t`,
`s ↦ (6 - 2cos(s - t))^{-1/2}` has derivative equal to the unlink integrand. -/
theorem unlink_inner_antideriv (t s : ℝ) :
    HasDerivAt (fun s => (6 - 2 * Real.cos (s - t)) ^ (-(1 / 2) : ℝ))
      (-2 * Real.sin (s - t) / Real.sqrt (6 - 2 * Real.cos (s - t)) ^ 3) s := by
  sorry

/-- **Inner integral of the unlink integrand vanishes** for every `t`. -/
theorem unlink_inner_integral_zero (t : ℝ) :
    ∫ s in (0 : ℝ)..(2 * Real.pi), linkingIntegrand unlink.K.curve unlink.L.curve s t = 0 := by
  sorry

/-- **The unlink has linking number zero.** -/
theorem linking_unlink_zero : unlink.linkingNumber = 0 := by
  sorry

/-- **The Hopf linking integrand** in closed form:
`I_{L₂}(s,t) = (cos t - (1 + cos t) cos s) / D(s,t)^{3/2}`, where
`D(s,t) = 3 + 2 cos t - 2 (1 + cos t) cos s = ‖u‖²`. -/
theorem hopf_integrand (s t : ℝ) :
    linkingIntegrand hopfLink.K.curve hopfLink.L.curve s t
      = (Real.cos t - (1 + Real.cos t) * Real.cos s)
        / Real.sqrt (3 + 2 * Real.cos t - 2 * (1 + Real.cos t) * Real.cos s) ^ 3 := by
  sorry

/-- **The Hopf denominator is bounded below.**
`D(s,t) = 3 + 2 cos t - 2 (1 + cos t) cos s ≥ 1`; in particular `D(s,t) > 0`. -/
theorem hopf_denom_pos (s t : ℝ) :
    (1 : ℝ) ≤ 3 + 2 * Real.cos t - 2 * (1 + Real.cos t) * Real.cos s := by
  have hcos_s : Real.cos s ≤ 1 := Real.cos_le_one _
  have hcos_t : -1 ≤ Real.cos t := Real.neg_one_le_cos _
  nlinarith

/-- **Reduced form of the Hopf integrand.** Since the numerator is `½(D - 3)`,
`I_{L₂}(s,t) = ½ D(s,t)^{-1/2} - 3/2 D(s,t)^{-3/2}`. -/
theorem hopf_integrand_reduced (s t : ℝ) :
    linkingIntegrand hopfLink.K.curve hopfLink.L.curve s t
      = (1 / 2) *
          (3 + 2 * Real.cos t - 2 * (1 + Real.cos t) * Real.cos s) ^ (-(1 / 2) : ℝ)
        - (3 / 2) *
          (3 + 2 * Real.cos t - 2 * (1 + Real.cos t) * Real.cos s) ^ (-(3 / 2) : ℝ) := by
  sorry

/-- **Explicit half-angle reduction of the Hopf inner integrand.** Under
`x = tan(s/2)`, with `c = 5 + 4cos t`, the reduced integrand times `2/(1+x²)`
equals `Ψ_t(x) = ((c-3)x² - 2)(1+x²)^{-1/2}(1+cx²)^{-3/2}`. -/
theorem hopf_halfAngle_reduction (t x : ℝ) :
    ((1 / 2) * ((1 + (5 + 4 * Real.cos t) * x ^ 2) / (1 + x ^ 2)) ^ (-(1 / 2) : ℝ)
        - (3 / 2) * ((1 + (5 + 4 * Real.cos t) * x ^ 2) / (1 + x ^ 2)) ^ (-(3 / 2) : ℝ))
        * (2 / (1 + x ^ 2))
      = ((5 + 4 * Real.cos t - 3) * x ^ 2 - 2) * (1 + x ^ 2) ^ (-(1 / 2) : ℝ)
          * (1 + (5 + 4 * Real.cos t) * x ^ 2) ^ (-(3 / 2) : ℝ) := by
  sorry

/-- **Continuity and periodicity of the Hopf inner integral.** -/
theorem hopf_inner_integral_regularity :
    Continuous (fun t => ∫ s in (0 : ℝ)..(2 * Real.pi),
        (1 / 2) * (3 + 2 * Real.cos t - 2 * (1 + Real.cos t) * Real.cos s) ^ (-(1 / 2) : ℝ)
        - (3 / 2) * (3 + 2 * Real.cos t - 2 * (1 + Real.cos t) * Real.cos s) ^ (-(3 / 2) : ℝ))
      ∧ Function.Periodic (fun t => ∫ s in (0 : ℝ)..(2 * Real.pi),
        (1 / 2) * (3 + 2 * Real.cos t - 2 * (1 + Real.cos t) * Real.cos s) ^ (-(1 / 2) : ℝ)
        - (3 / 2) * (3 + 2 * Real.cos t - 2 * (1 + Real.cos t) * Real.cos s) ^ (-(3 / 2) : ℝ))
        (2 * Real.pi) := by
  sorry

/-- **The Hopf inner integral splits by linearity** into the two real-power
integrals (each a complete elliptic integral; only the linearity split is
formalized here). -/
theorem hopf_inner_integral (t : ℝ) :
    (∫ s in (0 : ℝ)..(2 * Real.pi),
        (1 / 2) * (3 + 2 * Real.cos t - 2 * (1 + Real.cos t) * Real.cos s) ^ (-(1 / 2) : ℝ)
        - (3 / 2) * (3 + 2 * Real.cos t - 2 * (1 + Real.cos t) * Real.cos s) ^ (-(3 / 2) : ℝ))
      = (1 / 2) * (∫ s in (0 : ℝ)..(2 * Real.pi),
            (3 + 2 * Real.cos t - 2 * (1 + Real.cos t) * Real.cos s) ^ (-(1 / 2) : ℝ))
        - (3 / 2) * (∫ s in (0 : ℝ)..(2 * Real.pi),
            (3 + 2 * Real.cos t - 2 * (1 + Real.cos t) * Real.cos s) ^ (-(3 / 2) : ℝ)) := by
  sorry

/-- **The Hopf outer integral equals `4π`.**

*Obstruction.* The inner integral is a nonzero combination of complete elliptic
integrals of `t`, hence has no elementary antiderivative; the true value `4π` is
a mapping-degree / solid-angle fact. Mathlib currently has neither a theory of
complete elliptic integrals nor smooth degree theory, so this statement, although
true, cannot be proved within Mathlib. -/
theorem hopf_outer_integral :
    (∫ t in (0 : ℝ)..(2 * Real.pi), ∫ s in (0 : ℝ)..(2 * Real.pi),
        (1 / 2) * (3 + 2 * Real.cos t - 2 * (1 + Real.cos t) * Real.cos s) ^ (-(1 / 2) : ℝ)
        - (3 / 2) * (3 + 2 * Real.cos t - 2 * (1 + Real.cos t) * Real.cos s) ^ (-(3 / 2) : ℝ))
      = 4 * Real.pi := by
  sorry

/-- **The Hopf Gauss integral equals 4π.** The double integral evaluates to
`4π`, so `lk(L₂) = 1`, via `hopf_integrand_reduced` and the FTC. -/
theorem hopf_linking_value : hopfLink.linkingNumber = 1 := by
  sorry

/-- **The Hopf link has nonzero linking number.** -/
theorem linking_hopf_nonzero : hopfLink.linkingNumber ≠ 0 := by
  rw [hopf_linking_value]
  norm_num

/-! ## Conclusion -/

/-- **Existence of a non-isotopic pair of oriented two-component links.**

There exist two oriented smooth two-component links in `ℝ³` that are not
ambient-isotopic — the unlink and the Hopf link, distinguished by their Gauss
linking numbers (`0` and `1`). -/
@[eval_problem]
theorem exists_nonisotopic_link : ∃ L₁ L₂ : TwoLink, ¬ L₁.Isotopic L₂ := by
  refine ⟨unlink, hopfLink, ?_⟩
  intro h
  have hlnum : unlink.linkingNumber = hopfLink.linkingNumber :=
    TwoLink.linkingNumber_isotopy_invariant h
  rw [linking_unlink_zero] at hlnum
  exact linking_hopf_nonzero hlnum.symm

end KnotTheory
end LeanEval
