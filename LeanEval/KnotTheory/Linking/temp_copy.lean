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
# Linking number: foundations

The Gauss map, the scalar triple product, the linking integrand and the Gauss
linking number, together with the foundational smoothness/continuity helpers and
the pointwise algebraic and differentiation identities used throughout the
ambient-isotopy-invariance proof.
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
  have hK : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => Lk.K.curve p.1) :=
    Lk.K.smooth.comp contDiff_fst
  have hL : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => Lk.L.curve p.2) :=
    Lk.L.smooth.comp contDiff_snd
  exact ContDiff.sub hK hL

/-- **The denominator is smooth and positive.** For any real exponent `p`,
`(s,t) ↦ ‖γ_K(s) - γ_L(t)‖ ^ p` is `C^∞`, and the norm is everywhere positive. -/
theorem TwoLink.jointDenom_smooth_pos (Lk : TwoLink) (p : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => ‖Lk.K.curve q.1 - Lk.L.curve q.2‖ ^ p) ∧
    ∀ s t, 0 < ‖Lk.K.curve s - Lk.L.curve t‖ := by
  have hpos : ∀ s t, 0 < ‖Lk.K.curve s - Lk.L.curve t‖ := by
    intro s t
    rw [norm_pos_iff]
    exact TwoLink.components_nonzero Lk s t
  have h_diff_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => Lk.K.curve q.1 - Lk.L.curve q.2) :=
    Lk.jointDiff_smooth
  have h_norm_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => ‖Lk.K.curve q.1 - Lk.L.curve q.2‖) := by
    refine (contDiff_iff_contDiffAt.mpr ?_)
    intro q
    have h_nonzero : Lk.K.curve q.1 - Lk.L.curve q.2 ≠ 0 :=
      norm_pos_iff.mp (hpos q.1 q.2)
    have h_diff_at : ContDiffAt ℝ (⊤ : ℕ∞) (fun q' : ℝ × ℝ => Lk.K.curve q'.1 - Lk.L.curve q'.2) q :=
      (contDiff_iff_contDiffAt.mp h_diff_smooth) q
    have h_norm_at : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => ‖(fun q' : ℝ × ℝ => Lk.K.curve q'.1 - Lk.L.curve q'.2) y‖) q :=
      (contDiffAt_norm (𝕜 := ℝ) h_nonzero).comp q h_diff_at
    simpa using h_norm_at
  have h_rpow_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => ‖Lk.K.curve q.1 - Lk.L.curve q.2‖ ^ p) := by
    refine (contDiff_iff_contDiffAt.mpr ?_)
    intro q
    have h_nz : ‖Lk.K.curve q.1 - Lk.L.curve q.2‖ ≠ 0 := by
      linarith [hpos q.1 q.2]
    have h_norm_at : ContDiffAt ℝ (⊤ : ℕ∞) (fun q' : ℝ × ℝ => ‖Lk.K.curve q'.1 - Lk.L.curve q'.2‖) q :=
      (contDiff_iff_contDiffAt.mp h_norm_smooth) q
    exact h_norm_at.rpow (contDiffAt_const (c := p) (x := q)) h_nz
  exact ⟨h_rpow_smooth, hpos⟩

/-- **Smoothness of the Gauss map.** -/
theorem TwoLink.gaussMap_smooth (Lk : TwoLink) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => Lk.gaussMap p.1 p.2) := by
  have h_diff := Lk.jointDiff_smooth
  have ⟨h_norm_smooth, h_norm_pos⟩ := Lk.jointDenom_smooth_pos (-1)
  have h_norm_inv_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => (‖Lk.K.curve p.1 - Lk.L.curve p.2‖)⁻¹) := by
    -- ‖u‖ ^ (-1 : ℝ) = (‖u‖ ^ (1 : ℝ))⁻¹ = ‖u‖⁻¹
    simpa [Real.rpow_neg (norm_nonneg _), Real.rpow_one] using h_norm_smooth
  refine h_norm_inv_smooth.smul h_diff

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

/-! ## Pointwise algebraic and differentiation identities -/

/-- **Lagrange / scalar quadruple-product identity.** For all `u p q w : ℝ³`,
`⟨u,w⟩ det(u,p,q) = ‖u‖² det(w,p,q) + ⟨u,p⟩ det(u,w,q) + ⟨u,q⟩ det(u,p,w)`.
The determinant analogue of `cross_dot_cross`, a coordinate `ring` identity. -/
theorem quadruple_product_identity (u p q w : R3) :
    ⟪u, w⟫ * tripleProduct u p q
      = ‖u‖ ^ 2 * tripleProduct w p q
        + ⟪u, p⟫ * tripleProduct u w q
        + ⟪u, q⟫ * tripleProduct u p w := by
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

end KnotTheory
end LeanEval
