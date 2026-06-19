import LeanEval.KnotTheory.Linking

/-!
# Supporting lemmas for the linking-number invariance proof

This file collects the auxiliary declarations of the blueprint
*"Existence of a non-isotopic pair of oriented two-component links"* that are
referenced by name but do not fit in `Linking.lean` without pushing it well past
the size guideline. Every statement here is `sorry`'d; the proofs are the
concern of later prover agents.

The two genuinely non-Mathlib facts (`hopf_outer_integral` and, in
`Linking.lean`, `hopf_linking_value`) require a theory of complete elliptic
integrals or smooth degree theory, neither currently available in Mathlib; the
blueprint flags them explicitly as obstructions.
-/

namespace LeanEval
namespace KnotTheory

open scoped RealInnerProductSpace

/-! ## Smoothness / continuity helpers -/

/-- **The cross product of smooth maps is smooth.** -/
theorem crossProduct_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → (Fin 3 → ℝ)} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => crossProduct (f x) (g x)) := by
  sorry

/-- **The inner product of smooth maps is smooth.** -/
theorem inner_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → R3} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ⟪f x, g x⟫) := by
  sorry

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

/-! ## Joint smoothness of the deformed data -/

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

/-! ## Partial derivatives of the deformed difference -/

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

/-! ## The divergence identity -/

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

/-! ## Differentiating under the integral sign -/

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

/-! ## Reparametrization invariance -/

/-- **Chain rule for a reparametrized knot.** `(γ ∘ σ)'(s) = σ'(s) • γ'(σ(s))`. -/
theorem reparam_chain_deriv (γ : Knot) {σ : ℝ → ℝ} (hσ : ContDiff ℝ (⊤ : ℕ∞) σ) (s : ℝ) :
    deriv (fun x => γ.curve (σ x)) s = deriv σ s • deriv γ.curve (σ s) := by
  sorry

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

/-! ## Unlink and Hopf computations -/

/-- **Antiderivative of the unlink integrand.** For fixed `t`,
`s ↦ (6 - 2cos(s - t))^{-1/2}` has derivative equal to the unlink integrand. -/
theorem unlink_inner_antideriv (t s : ℝ) :
    HasDerivAt (fun s => (6 - 2 * Real.cos (s - t)) ^ (-(1 / 2) : ℝ))
      (-2 * Real.sin (s - t) / Real.sqrt (6 - 2 * Real.cos (s - t)) ^ 3) s := by
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

end KnotTheory
end LeanEval
