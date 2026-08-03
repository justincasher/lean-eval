import Mathlib
import EvalTools.Markers

namespace LeanEval
namespace Analysis

/-!
# Euler–Lagrange equation

§44 of Oliver Knill's *Some Fundamental Theorems in Mathematics* (the additional
statement of the calculus-of-variations section). A sufficiently regular
stationary path `x` of the action `I(y) = ∫_a^b L(t, y(t), y'(t)) dt` satisfies
the Euler–Lagrange equation `∂L/∂x = (d/dt)(∂L/∂x')` pointwise on `(a, b)`.

mathlib has the fundamental lemma of the calculus of variations
(`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` and neighbours), but it
has no notion of a variational extremum of an action functional and no
Euler–Lagrange theorem (`grep -i 'euler.*lagrange'` in mathlib finds nothing in
the analytic sense). Here a path is a variational extremum when the first
variation of the action vanishes against every smooth compactly supported
perturbation, and the conclusion is the classical pointwise equation for `C²`
data.
-/

open MeasureTheory Set
open scoped ContDiff

/-- `∂L/∂x` along the path `x` at time `t`: the derivative of the partial map
`y ↦ L t y (x' t)` at `y = x t`. -/
noncomputable def lagrangianPartialX
    (L : ℝ → ℝ → ℝ → ℝ) (x : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv (fun y => L t y (deriv x t)) (x t)

/-- `∂L/∂x'` along the path `x` at time `t`: the derivative of the partial map
`z ↦ L t (x t) z` at `z = x' t`. -/
noncomputable def lagrangianPartialV
    (L : ℝ → ℝ → ℝ → ℝ) (x : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv (fun z => L t (x t) z) (deriv x t)

/-- A `C¹` path `x : ℝ → ℝ` is a **variational extremum** of the action
`I(y) := ∫_a^b L(t, y(t), y'(t)) dt` on `(a, b)` if for every smooth compactly
supported variation `h` with `tsupport h ⊆ (a, b)`, the first variation
`d/dε|_{ε=0} ∫_a^b L(t, x(t) + ε h(t), x'(t) + ε h'(t)) dt` vanishes. -/
def IsVariationalExtremum
    (a b : ℝ) (L : ℝ → ℝ → ℝ → ℝ) (x : ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 x ∧
  ∀ h : ℝ → ℝ, ContDiff ℝ ∞ h → HasCompactSupport h →
    tsupport h ⊆ Set.Ioo a b →
    deriv (fun ε : ℝ => ∫ t in Set.Ioo a b,
        L t (x t + ε * h t) (deriv x t + ε * deriv h t)) 0 = 0

/-- Shifted spatial partial `∂_x L_ε` along the configuration `x + ε h`: the
derivative of `y ↦ L t y (x' t + ε h' t)` at `y = x t + ε h t`. At `ε = 0` it
reduces to `lagrangianPartialX L x`. -/
noncomputable def lagrangianPartialXShifted
    (L : ℝ → ℝ → ℝ → ℝ) (x h : ℝ → ℝ) (ε t : ℝ) : ℝ :=
  deriv (fun y => L t y (deriv x t + ε * deriv h t)) (x t + ε * h t)

/-- Shifted velocity partial `∂_{x'} L_ε` along the configuration `x + ε h`: the
derivative of `z ↦ L t (x t + ε h t) z` at `z = x' t + ε h' t`. At `ε = 0` it
reduces to `lagrangianPartialV L x`. -/
noncomputable def lagrangianPartialVShifted
    (L : ℝ → ℝ → ℝ → ℝ) (x h : ℝ → ℝ) (ε t : ℝ) : ℝ :=
  deriv (fun z => L t (x t + ε * h t) z) (deriv x t + ε * deriv h t)

/-! ### Regularity of the partials along the path -/

/-- **Directional derivative equals the Fréchet derivative on that direction.**
For `f` differentiable at `p` and a direction `d`, the derivative of the line
`ε ↦ f (p + ε • d)` at `0` is `fderiv ℝ f p d`. -/
theorem directional_deriv_eq_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (p d : E) (hf : DifferentiableAt ℝ f p) :
    deriv (fun ε : ℝ => f (p + ε • d)) 0 = fderiv ℝ f p d := by
  have h_curve : HasDerivAt (fun ε : ℝ => p + ε • d) d 0 := by
    have h_id : HasDerivAt (fun ε : ℝ => ε) (1 : ℝ) 0 := hasDerivAt_id (0 : ℝ)
    have h_smul : HasDerivAt (fun ε : ℝ => ε • d) d 0 := by
      simpa using h_id.smul_const d
    simpa using h_smul.const_add p
  have h_fderiv' : HasFDerivAt f (fderiv ℝ f p) ((fun ε : ℝ => p + ε • d) 0) := by
    simpa using hf.hasFDerivAt
  have h_comp : HasDerivAt (fun ε : ℝ => f (p + ε • d)) (fderiv ℝ f p d) 0 :=
    h_fderiv'.comp_hasDerivAt (x := 0) (hf := h_curve)
  exact h_comp.deriv

/-- **A partial derivative of a `C²` function is `C¹`.** For a `C²` function
`F : ℝ × ℝ × ℝ → ℝ` and a fixed direction `e`, the map `p ↦ fderiv ℝ F p e`
(which, for `e` a basis vector, is the slice/partial derivative in that slot) is
`C¹` on `ℝ³`; in particular it is continuous. -/
theorem partialDeriv_contDiff
    (F : ℝ × ℝ × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (e : ℝ × ℝ × ℝ) :
    ContDiff ℝ 1 (fun p => fderiv ℝ F p e) := by
  have hfderiv : ContDiff ℝ 1 (fderiv ℝ F) :=
    hF.fderiv_right (by
      have : (1 : ℕ∞ω) + 1 ≤ (2 : ℕ∞ω) := by decide
      exact this)
  have hconst : ContDiff ℝ 1 fun (_ : ℝ × ℝ × ℝ) => e :=
    contDiff_const
  exact (hfderiv.clm_apply hconst)

/-- **The curve `(t, x(t), x'(t))` is `C¹`.** -/
theorem curve_contDiff (x : ℝ → ℝ) (hx : ContDiff ℝ 2 x) :
    ContDiff ℝ 1 (fun t : ℝ => (t, x t, deriv x t)) := by
  have h_id : ContDiff ℝ 1 (fun t : ℝ => t) := contDiff_id
  have h_x : ContDiff ℝ 1 x :=
    hx.of_le (by
      have : (1 : ℕ) ≤ (2 : ℕ) := by norm_num
      exact_mod_cast this)
  have h_deriv : ContDiff ℝ 1 (deriv x) := hx.deriv'
  have h_pair : ContDiff ℝ 1 (fun t : ℝ => (x t, deriv x t)) :=
    h_x.prodMk h_deriv
  exact h_id.prodMk h_pair

/-- **The velocity partial along `x` is `C¹`.** If `L` and `x` are `C²`, then
`t ↦ ∂_{x'} L(t)` is `C¹`; in particular it is differentiable everywhere and its
derivative is continuous. -/
theorem lagrangianPartialV_contDiff
    (L : ℝ → ℝ → ℝ → ℝ) (x : ℝ → ℝ)
    (hL : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2))
    (hx : ContDiff ℝ 2 x) :
    ContDiff ℝ 1 (lagrangianPartialV L x) := by
  set F : ℝ × ℝ × ℝ → ℝ := fun p => L p.1 p.2.1 p.2.2 with hFdef
  have hF_contDiff : ContDiff ℝ 2 F := hL
  set e : ℝ × ℝ × ℝ := (0, 0, 1) with hedef
  -- the map p ↦ fderiv ℝ F p e (partial derivative in the third slot) is C¹
  have hPartial : ContDiff ℝ 1 (fun (p : ℝ × ℝ × ℝ) => fderiv ℝ F p e) :=
    partialDeriv_contDiff F hF_contDiff e
  -- the curve t ↦ (t, x t, deriv x t) is C¹
  have hCurve : ContDiff ℝ 1 (fun t : ℝ => (t, x t, deriv x t)) :=
    curve_contDiff x hx
  -- show lagrangianPartialV L x = (p ↦ fderiv ℝ F p e) ∘ (t ↦ (t, x t, deriv x t))
  have h_eq : lagrangianPartialV L x = (fun p : ℝ × ℝ × ℝ => fderiv ℝ F p e) ∘ (fun t : ℝ => (t, x t, deriv x t)) := by
    ext t
    dsimp [lagrangianPartialV]
    let a := t
    let b := x t
    let c := deriv x t
    have hF_contDiffAt : ContDiffAt ℝ 2 F (a, b, c) :=
      hF_contDiff.contDiffAt
    have hF_diff : DifferentiableAt ℝ F (a, b, c) :=
      hF_contDiffAt.differentiableAt (by decide)
    set g : ℝ → ℝ × ℝ × ℝ := fun s => (a, b, s) with hgdef
    have hg_deriv : HasDerivAt g (0, (0, 1)) c := by
      have h1 : HasDerivAt (fun _ : ℝ => a) 0 c := hasDerivAt_const (c := a) (x := c)
      have h2 : HasDerivAt (fun _ : ℝ => b) 0 c := hasDerivAt_const (c := b) (x := c)
      have h3 : HasDerivAt (fun s : ℝ => s) 1 c := hasDerivAt_id c
      -- g(s) = (a, b, s) = (a, (b, s))
      have h23 : HasDerivAt (fun s : ℝ => (b, s)) (0, 1) c := h2.prodMk h3
      have h123 : HasDerivAt (fun s : ℝ => (a, (b, s))) (0, (0, 1)) c := h1.prodMk h23
      simpa [g] using h123
    have h_comp : HasDerivAt (F ∘ g) ((fderiv ℝ F (a, b, c)) (0, (0, 1))) c :=
      hF_diff.hasFDerivAt.comp_hasDerivAt (f := g) (x := c) (hf := hg_deriv)
    have h_comp' : HasDerivAt (fun (z : ℝ) => L a b z) ((fderiv ℝ F (a, b, c)) (0, (0, 1))) c := by
      change HasDerivAt (F ∘ g) ((fderiv ℝ F (a, b, c)) (0, (0, 1))) c
      exact h_comp
    have h_deriv : deriv (fun (z : ℝ) => L a b z) c = (fderiv ℝ F (a, b, c)) (0, (0, 1)) :=
      h_comp'.deriv
    simpa [e, a, b, c] using h_deriv
  rw [h_eq]
  exact hPartial.comp hCurve

/-- **The spatial partial along `x` is continuous.** -/
theorem lagrangianPartialX_continuous
    (L : ℝ → ℝ → ℝ → ℝ) (x : ℝ → ℝ)
    (hL : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2))
    (hx : ContDiff ℝ 2 x) :
    Continuous (lagrangianPartialX L x) := by
  set F := (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2) with hF
  set e : ℝ × ℝ × ℝ := (0, 1, 0) with he
  -- Function g(p) = fderiv ℝ F p e is C¹, hence continuous
  have hg_contdiff : ContDiff ℝ 1 (fun p : ℝ × ℝ × ℝ => fderiv ℝ F p e) :=
    partialDeriv_contDiff F hL e
  have hg_cont : Continuous (fun p : ℝ × ℝ × ℝ => fderiv ℝ F p e) :=
    hg_contdiff.continuous
  -- Curve γ(t) = (t, x t, deriv x t) is C¹, hence continuous
  have hγ_contdiff : ContDiff ℝ 1 (fun t : ℝ => (t, x t, deriv x t)) :=
    curve_contDiff x hx
  have hγ_cont : Continuous (fun t : ℝ => (t, x t, deriv x t)) :=
    hγ_contdiff.continuous
  -- Equality: lagrangianPartialX L x = (fun p => fderiv ℝ F p e) ∘ γ
  have h_eq : lagrangianPartialX L x = (fun p : ℝ × ℝ × ℝ => fderiv ℝ F p e) ∘ (fun t : ℝ => (t, x t, deriv x t)) := by
    ext t
    dsimp [lagrangianPartialX, F, e]
    -- Since ContDiff ℝ 2 F, F is differentiable at (t, x t, deriv x t)
    have hF_diffAt : DifferentiableAt ℝ F (t, x t, deriv x t) :=
      (hL.contDiffAt (x := (t, x t, deriv x t))).differentiableAt (by
        have h : (2 : ℕ∞ω) ≠ 0 := by decide
        exact h)
    calc
      deriv (fun y : ℝ => L t y (deriv x t)) (x t)
          = deriv (fun ε : ℝ => L t (x t + ε) (deriv x t)) 0 := by
        -- translation invariance of the derivative
        rw [deriv_comp_const_add (f := fun y : ℝ => L t y (deriv x t)) (a := x t) (x := 0)]
        simp
      _ = deriv (fun ε : ℝ => F ((t, x t, deriv x t) + ε • e)) 0 := by
        simp [F, e]
      _ = fderiv ℝ F (t, x t, deriv x t) e := by
        refine directional_deriv_eq_fderiv F (t, x t, deriv x t) e hF_diffAt
  rw [h_eq]
  exact hg_cont.comp hγ_cont

/-- **The Euler–Lagrange defect is continuous.** The defect
`D(t) = ∂_x L(t) - (d/dt) ∂_{x'} L(t)` is continuous on `ℝ`. -/
theorem el_defect_continuous
    (L : ℝ → ℝ → ℝ → ℝ) (x : ℝ → ℝ)
    (hL : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2))
    (hx : ContDiff ℝ 2 x) :
    Continuous (fun t => lagrangianPartialX L x t - deriv (lagrangianPartialV L x) t) := by
  have hx_cont : Continuous (lagrangianPartialX L x) :=
    lagrangianPartialX_continuous L x hL hx
  have hv_contDiff : ContDiff ℝ 1 (lagrangianPartialV L x) :=
    lagrangianPartialV_contDiff L x hL hx
  have hderiv_cont : Continuous (deriv (lagrangianPartialV L x)) :=
    hv_contDiff.continuous_deriv (le_refl (1 : ℕ∞ω))
  exact hx_cont.sub hderiv_cont

/-! ### The first variation -/

/-- **Continuous with compact support is integrable.** (A restatement of
`Continuous.integrable_of_hasCompactSupport`.) -/
theorem continuous_compactSupport_integrable
    {f : ℝ → ℝ} (hf : Continuous f) (hsupp : HasCompactSupport f) :
    Integrable f :=
  hf.integrable_of_hasCompactSupport hsupp

/-- **Coordinate decomposition of a bivariate Fréchet derivative.** For
`Φ : ℝ × ℝ → ℝ` differentiable at `(y₀, z₀)`, the Fréchet derivative on `(u, v)`
splits into the two slice (partial) derivatives. -/
theorem fderiv_decomp
    (Φ : ℝ × ℝ → ℝ) (y₀ z₀ : ℝ) (hΦ : DifferentiableAt ℝ Φ (y₀, z₀)) (u v : ℝ) :
    fderiv ℝ Φ (y₀, z₀) (u, v)
      = deriv (fun y => Φ (y, z₀)) y₀ * u + deriv (fun z => Φ (y₀, z)) z₀ * v := by
  calc
    fderiv ℝ Φ (y₀, z₀) (u, v)
        = fderiv ℝ Φ (y₀, z₀) ((u, 0) + (0, v)) := by
      simp
    _ = fderiv ℝ Φ (y₀, z₀) (u, 0) + fderiv ℝ Φ (y₀, z₀) (0, v) := by
      rw [ContinuousLinearMap.map_add]
    _ = fderiv ℝ Φ (y₀, z₀) (u • (1, 0)) + fderiv ℝ Φ (y₀, z₀) (v • (0, 1)) := by
      simp
    _ = u • fderiv ℝ Φ (y₀, z₀) (1, 0) + v • fderiv ℝ Φ (y₀, z₀) (0, 1) := by
      rw [ContinuousLinearMap.map_smul (fderiv ℝ Φ (y₀, z₀)) u (1, 0),
        ContinuousLinearMap.map_smul (fderiv ℝ Φ (y₀, z₀)) v (0, 1)]
    _ = u * fderiv ℝ Φ (y₀, z₀) (1, 0) + v * fderiv ℝ Φ (y₀, z₀) (0, 1) := by
      simp
    _ = u * deriv (fun y => Φ (y, z₀)) y₀ + v * deriv (fun z => Φ (y₀, z)) z₀ := by
      have h1 : fderiv ℝ Φ (y₀, z₀) (1, 0) = deriv (fun y => Φ (y, z₀)) y₀ := by
        calc
          fderiv ℝ Φ (y₀, z₀) (1, 0) = deriv (fun ε : ℝ => Φ ((y₀, z₀) + ε • (1, 0))) 0 := by
            rw [directional_deriv_eq_fderiv Φ (y₀, z₀) (1, 0) hΦ]
          _ = deriv (fun ε : ℝ => Φ (y₀ + ε, z₀)) 0 := by simp
          _ = deriv (fun y : ℝ => Φ (y, z₀)) (y₀ + 0) := by
            rw [deriv_comp_const_add (fun y : ℝ => Φ (y, z₀)) y₀ 0]
          _ = deriv (fun y : ℝ => Φ (y, z₀)) y₀ := by simp
      have h2 : fderiv ℝ Φ (y₀, z₀) (0, 1) = deriv (fun z => Φ (y₀, z)) z₀ := by
        calc
          fderiv ℝ Φ (y₀, z₀) (0, 1) = deriv (fun ε : ℝ => Φ ((y₀, z₀) + ε • (0, 1))) 0 := by
            rw [directional_deriv_eq_fderiv Φ (y₀, z₀) (0, 1) hΦ]
          _ = deriv (fun ε : ℝ => Φ (y₀, z₀ + ε)) 0 := by simp
          _ = deriv (fun z : ℝ => Φ (y₀, z)) (z₀ + 0) := by
            rw [deriv_comp_const_add (fun z : ℝ => Φ (y₀, z)) z₀ 0]
          _ = deriv (fun z : ℝ => Φ (y₀, z)) z₀ := by simp
      rw [h1, h2]
    _ = deriv (fun y => Φ (y, z₀)) y₀ * u + deriv (fun z => Φ (y₀, z)) z₀ * v := by ring

/-- **Derivative of the shifted-configuration curve.** For fixed `t` and `h`, the
curve `ε ↦ (x t + ε h t, x' t + ε h' t)` has derivative `(h t, h' t)` at every
`ε`. -/
theorem variation_curve_hasDerivAt (x h : ℝ → ℝ) (t ε : ℝ) :
    HasDerivAt (fun e : ℝ => (x t + e * h t, deriv x t + e * deriv h t))
      (h t, deriv h t) ε := by
  have h_id : HasDerivAt (fun e : ℝ => e) (1 : ℝ) ε := hasDerivAt_id ε
  have h1 : HasDerivAt (fun e : ℝ => e * h t) (h t) ε := by
    simpa using h_id.mul_const (h t)
  have h2 : HasDerivAt (fun e : ℝ => e * deriv h t) (deriv h t) ε := by
    simpa using h_id.mul_const (deriv h t)
  have h1' : HasDerivAt (fun e : ℝ => x t + e * h t) (h t) ε :=
    h1.const_add (x t)
  have h2' : HasDerivAt (fun e : ℝ => deriv x t + e * deriv h t) (deriv h t) ε :=
    h2.const_add (deriv x t)
  exact h1'.prodMk h2'

/-- **Pointwise `ε`-derivative of the integrand at a shifted configuration.** If
`L` is differentiable at the shifted configuration, then
`ε ↦ L(t, x t + ε h t, x' t + ε h' t)` has derivative
`∂_x L_{ε₀}(t) · h t + ∂_{x'} L_{ε₀}(t) · h' t` at `ε = ε₀`. -/
theorem integrand_hasDerivAt
    (L : ℝ → ℝ → ℝ → ℝ) (x h : ℝ → ℝ) (t ε₀ : ℝ)
    (hL : DifferentiableAt ℝ (fun p : ℝ × ℝ => L t p.1 p.2)
            (x t + ε₀ * h t, deriv x t + ε₀ * deriv h t)) :
    HasDerivAt (fun ε : ℝ => L t (x t + ε * h t) (deriv x t + ε * deriv h t))
      (lagrangianPartialXShifted L x h ε₀ t * h t
        + lagrangianPartialVShifted L x h ε₀ t * deriv h t) ε₀ := by
  -- Write the integrand as Φ ∘ σ, where
  -- σ(ε) = (x t + ε * h t, deriv x t + ε * deriv h t),
  -- Φ(y,z) = L t y z.
  let σ : ℝ → ℝ × ℝ := fun ε => (x t + ε * h t, deriv x t + ε * deriv h t)
  let Φ : ℝ × ℝ → ℝ := fun p : ℝ × ℝ => L t p.1 p.2
  have hσ : HasDerivAt σ (h t, deriv h t) ε₀ :=
    variation_curve_hasDerivAt x h t ε₀
  have hFDerivΦ : HasFDerivAt Φ (fderiv ℝ Φ (σ ε₀)) (σ ε₀) :=
    hL.hasFDerivAt
  have hChain : HasDerivAt (Φ ∘ σ) ((fderiv ℝ Φ (σ ε₀)) (h t, deriv h t)) ε₀ := by
    apply hFDerivΦ.comp_hasDerivAt
    exact hσ
  -- Use fderiv_decomp to rewrite the Fréchet derivative into partial derivatives
  have h_fderiv_decomp : (fderiv ℝ Φ (σ ε₀)) (h t, deriv h t) =
      lagrangianPartialXShifted L x h ε₀ t * h t
        + lagrangianPartialVShifted L x h ε₀ t * deriv h t := by
    calc
      (fderiv ℝ Φ (σ ε₀)) (h t, deriv h t)
          = fderiv ℝ Φ (x t + ε₀ * h t, deriv x t + ε₀ * deriv h t) (h t, deriv h t) := rfl
      _ = deriv (fun y => Φ (y, deriv x t + ε₀ * deriv h t)) (x t + ε₀ * h t) * (h t)
          + deriv (fun z => Φ (x t + ε₀ * h t, z)) (deriv x t + ε₀ * deriv h t) * (deriv h t) :=
        fderiv_decomp Φ (x t + ε₀ * h t) (deriv x t + ε₀ * deriv h t) hL (h t) (deriv h t)
      _ = lagrangianPartialXShifted L x h ε₀ t * h t
          + lagrangianPartialVShifted L x h ε₀ t * deriv h t := by
        simp [lagrangianPartialXShifted, lagrangianPartialVShifted, Φ]
  -- Combine the chain rule with the decomposition
  change HasDerivAt (Φ ∘ σ)
    (lagrangianPartialXShifted L x h ε₀ t * h t
      + lagrangianPartialVShifted L x h ε₀ t * deriv h t) ε₀
  exact hChain.congr_deriv h_fderiv_decomp

/-- **The `ε`-derivative integrand is supported in `tsupport h`.** For each `ε`
the integrand `t ↦ ∂_x L_ε(t) · h t + ∂_{x'} L_ε(t) · h' t` is supported in
`tsupport h`. -/
theorem deriv_integrand_support
    (L : ℝ → ℝ → ℝ → ℝ) (x h : ℝ → ℝ) (_hh : HasCompactSupport h) (ε : ℝ) :
    Function.support (fun t => lagrangianPartialXShifted L x h ε t * h t
        + lagrangianPartialVShifted L x h ε t * deriv h t) ⊆ tsupport h := by
  intro t ht
  by_contra! ht_not
  have hh_zero : h t = 0 := image_eq_zero_of_notMem_tsupport ht_not
  have hderiv_zero : deriv h t = 0 := by
    have hsubset : tsupport (deriv h) ⊆ tsupport h :=
      tsupport_deriv_subset (f := h)
    have ht_not_deriv : t ∉ tsupport (deriv h) :=
      fun htd => ht_not (hsubset htd)
    exact image_eq_zero_of_notMem_tsupport ht_not_deriv
  have hF_zero : (fun t : ℝ => lagrangianPartialXShifted L x h ε t * h t
    + lagrangianPartialVShifted L x h ε t * deriv h t) t = 0 := by
    simp [hh_zero, hderiv_zero]
  exact ht hF_zero

/-- **Shifted partials as Fréchet derivatives on basis vectors.** For a `C²`
Lagrangian, each shifted slice partial along the configuration `x + ε h` equals
the Fréchet derivative of `(t, y, z) ↦ L t y z` at that configuration applied to
the corresponding standard basis vector: `(0, 1, 0)` for the spatial partial and
`(0, 0, 1)` for the velocity partial. This is the bridge from the one-variable
`deriv` definitions to the multivariable `fderiv`, used to get continuity and
boundedness of the shifted partials. -/
theorem shiftedPartials_eq_fderiv
    (L : ℝ → ℝ → ℝ → ℝ) (x h : ℝ → ℝ) (ε t : ℝ)
    (hL : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2)) :
    lagrangianPartialXShifted L x h ε t
        = fderiv ℝ (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2)
            (t, x t + ε * h t, deriv x t + ε * deriv h t) (0, 1, 0)
    ∧ lagrangianPartialVShifted L x h ε t
        = fderiv ℝ (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2)
            (t, x t + ε * h t, deriv x t + ε * deriv h t) (0, 0, 1) := by
  set F : ℝ × ℝ × ℝ → ℝ := fun p => L p.1 p.2.1 p.2.2 with hFdef
  set p₀ : ℝ × ℝ × ℝ := (t, x t + ε * h t, deriv x t + ε * deriv h t) with hp₀def
  have hF_diff : DifferentiableAt ℝ F p₀ :=
    (hL.differentiable (by decide : (2 : ℕ∞ω) ≠ 0)).differentiableAt
  have hX : lagrangianPartialXShifted L x h ε t = fderiv ℝ F p₀ (0, 1, 0) := by
    calc
      lagrangianPartialXShifted L x h ε t
          = deriv (fun y => L t y (deriv x t + ε * deriv h t)) (x t + ε * h t) := rfl
      _ = deriv (fun y => L t y (deriv x t + ε * deriv h t)) ((x t + ε * h t) + 0) := by simp
      _ = deriv (fun e' : ℝ => L t ((x t + ε * h t) + e') (deriv x t + ε * deriv h t)) 0 := by
        rw [← deriv_comp_const_add (fun y => L t y (deriv x t + ε * deriv h t)) (x t + ε * h t) 0]
      _ = deriv (fun e' : ℝ => F (p₀ + e' • (0, 1, 0))) 0 := by
        simp [F, p₀]
      _ = fderiv ℝ F p₀ (0, 1, 0) :=
        directional_deriv_eq_fderiv F p₀ (0, 1, 0) hF_diff
  have hV : lagrangianPartialVShifted L x h ε t = fderiv ℝ F p₀ (0, 0, 1) := by
    calc
      lagrangianPartialVShifted L x h ε t
          = deriv (fun z => L t (x t + ε * h t) z) (deriv x t + ε * deriv h t) := rfl
      _ = deriv (fun z => L t (x t + ε * h t) z) ((deriv x t + ε * deriv h t) + 0) := by simp
      _ = deriv (fun e' : ℝ => L t (x t + ε * h t) ((deriv x t + ε * deriv h t) + e')) 0 := by
        rw [← deriv_comp_const_add (fun z => L t (x t + ε * h t) z) (deriv x t + ε * deriv h t) 0]
      _ = deriv (fun e' : ℝ => F (p₀ + e' • (0, 0, 1))) 0 := by
        simp [F, p₀]
      _ = fderiv ℝ F p₀ (0, 0, 1) :=
        directional_deriv_eq_fderiv F p₀ (0, 0, 1) hF_diff
  exact And.intro hX hV

/-- **Uniform bound of the shifted partials over the `ε`-tube.** For `L, x` `C²`,
`h` smooth with compact support, and `r > 0`, there is a single constant `M`
bounding both shifted partials over `tsupport h × [-r, r]`. -/
theorem tube_bound
    (L : ℝ → ℝ → ℝ → ℝ) (x h : ℝ → ℝ)
    (hL : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2))
    (hx : ContDiff ℝ 2 x) (hh : ContDiff ℝ ∞ h) (hhsupp : HasCompactSupport h)
    {r : ℝ} (_hr : 0 < r) :
    ∃ M : ℝ, ∀ ε : ℝ, |ε| ≤ r → ∀ t ∈ tsupport h,
      |lagrangianPartialXShifted L x h ε t| ≤ M
        ∧ |lagrangianPartialVShifted L x h ε t| ≤ M := by
  -- The set Icc (-r) r × tsupport h is compact
  have hK : IsCompact (tsupport h) := hhsupp.isCompact
  have hIcc : IsCompact (Set.Icc (-r) r) := isCompact_Icc
  have hK_prod : IsCompact ((Set.Icc (-r) r) ×ˢ (tsupport h)) := hIcc.prod hK
  -- Abbreviation for the uncurried Lagrangian
  set F := fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2 with hFdef
  -- Rewrite the shifted partials as fderiv expressions (using the helper lemma)
  have h_eq_fderiv : ∀ ε t,
      lagrangianPartialXShifted L x h ε t
        = fderiv ℝ F (t, x t + ε * h t, deriv x t + ε * deriv h t) (0, 1, 0)
      ∧ lagrangianPartialVShifted L x h ε t
        = fderiv ℝ F (t, x t + ε * h t, deriv x t + ε * deriv h t) (0, 0, 1) :=
    fun ε t => shiftedPartials_eq_fderiv L x h ε t hL
  -- The maps p ↦ fderiv ℝ F p d (for d = (0,1,0) and d = (0,0,1)) are continuous
  have h_fderiv_x_cont : Continuous (fun p : ℝ × ℝ × ℝ => fderiv ℝ F p (0, 1, 0)) :=
    (partialDeriv_contDiff F hL (0, 1, 0)).continuous
  have h_fderiv_v_cont : Continuous (fun p : ℝ × ℝ × ℝ => fderiv ℝ F p (0, 0, 1)) :=
    (partialDeriv_contDiff F hL (0, 0, 1)).continuous
  -- The configuration map (ε, t) ↦ (t, x t + ε h t, deriv x t + ε deriv h t) is continuous
  let φ : ℝ × ℝ → ℝ × ℝ × ℝ := fun (ε, t) => (t, x t + ε * h t, deriv x t + ε * deriv h t)
  have hφ_cont : Continuous φ := by
    dsimp [φ]
    refine Continuous.prodMk continuous_snd ?_
    refine Continuous.prodMk ?_ ?_
    · -- (ε,t) ↦ x t + ε * h t
      refine Continuous.add (hx.continuous.comp continuous_snd) ?_
      refine Continuous.mul continuous_fst (hh.continuous.comp continuous_snd)
    · -- (ε,t) ↦ deriv x t + ε * deriv h t
      have h_deriv_x_cont : Continuous (deriv x) :=
        hx.continuous_deriv (by decide : (1 : ℕ∞ω) ≤ (2 : ℕ∞ω))
      refine Continuous.add (h_deriv_x_cont.comp continuous_snd) ?_
      refine Continuous.mul continuous_fst ?_
      exact (ContDiff.continuous_deriv hh (by simp : (1 : ℕ∞ω) ≤ ∞)).comp continuous_snd
  -- Compose: the maps (ε,t) ↦ fderiv ℝ F (φ (ε,t)) d are continuous on the product
  have h_f_x_cont : ContinuousOn (fun (p : ℝ × ℝ) => fderiv ℝ F (φ p) (0, 1, 0))
      ((Set.Icc (-r) r) ×ˢ (tsupport h)) :=
    (h_fderiv_x_cont.comp hφ_cont).continuousOn
  have h_f_v_cont : ContinuousOn (fun (p : ℝ × ℝ) => fderiv ℝ F (φ p) (0, 0, 1))
      ((Set.Icc (-r) r) ×ˢ (tsupport h)) :=
    (h_fderiv_v_cont.comp hφ_cont).continuousOn
  -- A continuous function on a compact set is bounded
  obtain ⟨Mx, hMx⟩ := hK_prod.exists_bound_of_continuousOn h_f_x_cont
  obtain ⟨Mv, hMv⟩ := hK_prod.exists_bound_of_continuousOn h_f_v_cont
  refine ⟨max Mx Mv, ?_⟩
  intro ε hε t ht
  have hp_mem : (ε, t) ∈ (Set.Icc (-r) r) ×ˢ (tsupport h) := by
    refine ⟨?_, ht⟩
    rw [Set.mem_Icc]
    have h_abs := abs_le.mp hε
    exact ⟨h_abs.1, h_abs.2⟩
  rcases h_eq_fderiv ε t with ⟨h_x_eq, h_v_eq⟩
  have hx_bound : |fderiv ℝ F (φ (ε, t)) (0, 1, 0)| ≤ Mx := by
    simpa using hMx (ε, t) hp_mem
  have hv_bound : |fderiv ℝ F (φ (ε, t)) (0, 0, 1)| ≤ Mv := by
    simpa using hMv (ε, t) hp_mem
  dsimp [φ] at hx_bound hv_bound
  constructor
  · calc
      |lagrangianPartialXShifted L x h ε t|
          = |fderiv ℝ F (t, x t + ε * h t, deriv x t + ε * deriv h t) (0, 1, 0)| := by rw [h_x_eq]
      _ ≤ Mx := hx_bound
      _ ≤ max Mx Mv := le_max_left _ _
  · calc
      |lagrangianPartialVShifted L x h ε t|
          = |fderiv ℝ F (t, x t + ε * h t, deriv x t + ε * deriv h t) (0, 0, 1)| := by rw [h_v_eq]
      _ ≤ Mv := hv_bound
      _ ≤ max Mx Mv := le_max_right _ _

/-- **Integrable dominating bound for the `ε`-derivative.** Under the standing
hypotheses there is an integrable `g ≥ 0` dominating the `ε`-derivative integrand
pointwise, uniformly for `|ε| ≤ r`. -/
theorem dominating_bound
    {a b : ℝ} (L : ℝ → ℝ → ℝ → ℝ) (x h : ℝ → ℝ)
    (hL : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2))
    (hx : ContDiff ℝ 2 x) (hh : ContDiff ℝ ∞ h) (hhsupp : HasCompactSupport h)
    (_hsub : tsupport h ⊆ Set.Ioo a b) {r : ℝ} (hr : 0 < r) :
    ∃ g : ℝ → ℝ, Integrable g ∧ (∀ t, 0 ≤ g t) ∧
      ∀ ε : ℝ, |ε| ≤ r → ∀ t,
        |lagrangianPartialXShifted L x h ε t * h t
            + lagrangianPartialVShifted L x h ε t * deriv h t| ≤ g t := by
  have hK : IsCompact (tsupport h) := hhsupp.isCompact
  have hKmeas : MeasurableSet (tsupport h) :=
    hK.isClosed.measurableSet
  have hK_fin : volume (tsupport h) < (⊤ : ENNReal) := hK.measure_lt_top
  have hK_fin' : volume (tsupport h) ≠ (⊤ : ENNReal) := ne_of_lt hK_fin
  obtain ⟨M, hM⟩ := tube_bound L x h hL hx hh hhsupp hr
  have h_cont : Continuous h := hh.continuous
  have h_deriv_cont : Continuous (deriv h) :=
    ContDiff.continuous_deriv hh (by decide : (1 : ℕ∞ω) ≤ ∞)
  have h_bound : ∃ H : ℝ, ∀ t ∈ tsupport h, |h t| ≤ H ∧ |deriv h t| ≤ H := by
    obtain ⟨Hh, hh_bound⟩ := hK.exists_bound_of_continuousOn h_cont.continuousOn
    obtain ⟨Hderiv, hderiv_bound⟩ := hK.exists_bound_of_continuousOn h_deriv_cont.continuousOn
    refine ⟨max Hh Hderiv, fun t ht => ⟨?_, ?_⟩⟩
    · calc
        |h t| ≤ Hh := hh_bound t ht
        _ ≤ max Hh Hderiv := le_max_left _ _
    · calc
        |deriv h t| ≤ Hderiv := hderiv_bound t ht
        _ ≤ max Hh Hderiv := le_max_right _ _
  rcases h_bound with ⟨H, hH⟩
  set M' := |M| with hM'_def
  set H' := |H| with hH'_def
  have hM'_nonneg : 0 ≤ M' := abs_nonneg _
  have hH'_nonneg : 0 ≤ H' := abs_nonneg _
  have hMM' : M ≤ M' := le_abs_self M
  have hHH' : H ≤ H' := le_abs_self H
  set C := 2 * M' * H' with hC_def
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    nlinarith
  set g := indicator (tsupport h) (fun _ : ℝ => C) with hg_def
  have hg_int : Integrable g := by
    have h_intOn : IntegrableOn (fun _ : ℝ => C) (tsupport h) := by
      refine integrableOn_const (hs := ?_) (hC := ?_)
      · exact hK_fin'
      · simp
    exact h_intOn.integrable_indicator hKmeas
  have hg_nonneg : ∀ t, 0 ≤ g t := by
    intro t
    dsimp [g]
    refine Set.indicator_nonneg (fun x hx => hC_nonneg) t
  refine ⟨g, hg_int, hg_nonneg, ?_⟩
  intro ε hε t
  by_cases ht : t ∈ tsupport h
  · have hM_ε_t := hM ε hε t ht
    rcases hM_ε_t with ⟨hXbound, hVbound⟩
    have hH_t := hH t ht
    rcases hH_t with ⟨hh_bound, hderiv_bound⟩
    have hXbound' : |lagrangianPartialXShifted L x h ε t| ≤ M' :=
      hXbound.trans hMM'
    have hVbound' : |lagrangianPartialVShifted L x h ε t| ≤ M' :=
      hVbound.trans hMM'
    have hh_bound' : |h t| ≤ H' :=
      hh_bound.trans hHH'
    have hderiv_bound' : |deriv h t| ≤ H' :=
      hderiv_bound.trans hHH'
    have habs_nonneg_h : 0 ≤ |h t| := abs_nonneg _
    have habs_nonneg_deriv : 0 ≤ |deriv h t| := abs_nonneg _
    calc
      |lagrangianPartialXShifted L x h ε t * h t
          + lagrangianPartialVShifted L x h ε t * deriv h t|
          ≤ |lagrangianPartialXShifted L x h ε t * h t|
            + |lagrangianPartialVShifted L x h ε t * deriv h t| := by
            apply abs_add_le
      _ = |lagrangianPartialXShifted L x h ε t| * |h t|
          + |lagrangianPartialVShifted L x h ε t| * |deriv h t| := by
        simp [abs_mul]
      _ ≤ M' * |h t| + |lagrangianPartialVShifted L x h ε t| * |deriv h t| := by
        nlinarith
      _ ≤ M' * |h t| + M' * |deriv h t| := by
        nlinarith
      _ = M' * (|h t| + |deriv h t|) := by ring
      _ ≤ M' * (H' + H') := by
        nlinarith
      _ = 2 * M' * H' := by ring
      _ = C := rfl
      _ = g t := by
        rw [hg_def, indicator_of_mem ht]
  · have h_out : Function.support (fun t => lagrangianPartialXShifted L x h ε t * h t
        + lagrangianPartialVShifted L x h ε t * deriv h t) ⊆ tsupport h :=
      deriv_integrand_support L x h hhsupp ε
    have hzero : lagrangianPartialXShifted L x h ε t * h t
        + lagrangianPartialVShifted L x h ε t * deriv h t = 0 := by
      have h_not_support : t ∉ Function.support (fun t => lagrangianPartialXShifted L x h ε t * h t
          + lagrangianPartialVShifted L x h ε t * deriv h t) :=
        mt (fun h => h_out h) ht
      simpa [Function.mem_support] using h_not_support
    calc
      |lagrangianPartialXShifted L x h ε t * h t
          + lagrangianPartialVShifted L x h ε t * deriv h t|
          = |0| := by rw [hzero]
      _ = 0 := abs_zero
      _ ≤ g t := hg_nonneg t

/-- **A.e.-measurability of the integrand family.** For every `ε` both the
integrand and its `ε`-derivative are a.e.-strongly-measurable on `(a, b)`. -/
theorem integrand_aestronglyMeasurable
    {a b : ℝ} (L : ℝ → ℝ → ℝ → ℝ) (x h : ℝ → ℝ)
    (hL : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2))
    (hx : ContDiff ℝ 2 x) (hh : ContDiff ℝ ∞ h) :
    (∀ ε : ℝ, AEStronglyMeasurable
        (fun t => L t (x t + ε * h t) (deriv x t + ε * deriv h t))
        (volume.restrict (Set.Ioo a b)))
    ∧ (∀ ε : ℝ, AEStronglyMeasurable
        (fun t => lagrangianPartialXShifted L x h ε t * h t
            + lagrangianPartialVShifted L x h ε t * deriv h t)
        (volume.restrict (Set.Ioo a b))) := by
  set F : ℝ × ℝ × ℝ → ℝ := fun p => L p.1 p.2.1 p.2.2 with hF
  have hF_cont : Continuous F := hL.continuous
  have hx_cont : Continuous x := hx.continuous
  have hh_cont : Continuous h := hh.continuous
  have hderiv_x_cont : Continuous (deriv x) :=
    hx.continuous_deriv (by norm_num : (1 : ℕ∞ω) ≤ (2 : ℕ∞ω))
  have hderiv_h_cont : Continuous (deriv h) :=
    hh.continuous_deriv (by decide : (1 : ℕ∞ω) ≤ ∞)
  have h_cont_Xpartial : Continuous (fun p : ℝ × ℝ × ℝ => fderiv ℝ F p (0, 1, 0)) :=
    (partialDeriv_contDiff F hL (0, 1, 0)).continuous
  have h_cont_Vpartial : Continuous (fun p : ℝ × ℝ × ℝ => fderiv ℝ F p (0, 0, 1)) :=
    (partialDeriv_contDiff F hL (0, 0, 1)).continuous
  constructor
  · intro ε
    have h_curve_cont : Continuous (fun t : ℝ => (t, x t + ε * h t, deriv x t + ε * deriv h t)) := by
      -- (t, a, b) is ℝ × ℝ × ℝ = ℝ × (ℝ × ℝ), so use nested prodMk
      refine continuous_id.prodMk ?_
      exact (hx_cont.add (hh_cont.const_mul ε)).prodMk
        (hderiv_x_cont.add (hderiv_h_cont.const_mul ε))
    have h_cont : Continuous (fun t : ℝ => L t (x t + ε * h t) (deriv x t + ε * deriv h t)) :=
      hF_cont.comp h_curve_cont
    exact h_cont.aestronglyMeasurable
  · intro ε
    have h_curve_cont : Continuous (fun t : ℝ => (t, x t + ε * h t, deriv x t + ε * deriv h t)) := by
      refine continuous_id.prodMk ?_
      exact (hx_cont.add (hh_cont.const_mul ε)).prodMk
        (hderiv_x_cont.add (hderiv_h_cont.const_mul ε))
    have h_cont_XShifted : Continuous (fun t : ℝ => lagrangianPartialXShifted L x h ε t) := by
      have h_eq : (fun t : ℝ => lagrangianPartialXShifted L x h ε t)
          = (fun p : ℝ × ℝ × ℝ => fderiv ℝ F p (0, 1, 0))
            ∘ (fun t : ℝ => (t, x t + ε * h t, deriv x t + ε * deriv h t)) := by
        ext t
        have h := (shiftedPartials_eq_fderiv L x h ε t hL).1
        simpa [hF] using h
      rw [h_eq]
      exact h_cont_Xpartial.comp h_curve_cont
    have h_cont_VShifted : Continuous (fun t : ℝ => lagrangianPartialVShifted L x h ε t) := by
      have h_eq : (fun t : ℝ => lagrangianPartialVShifted L x h ε t)
          = (fun p : ℝ × ℝ × ℝ => fderiv ℝ F p (0, 0, 1))
            ∘ (fun t : ℝ => (t, x t + ε * h t, deriv x t + ε * deriv h t)) := by
        ext t
        have h := (shiftedPartials_eq_fderiv L x h ε t hL).2
        simpa [hF] using h
      rw [h_eq]
      exact h_cont_Vpartial.comp h_curve_cont
    have h_cont_prod : Continuous (fun t : ℝ =>
        lagrangianPartialXShifted L x h ε t * h t
        + lagrangianPartialVShifted L x h ε t * deriv h t) :=
      (h_cont_XShifted.mul hh_cont).add (h_cont_VShifted.mul hderiv_h_cont)
    exact h_cont_prod.aestronglyMeasurable

/-- **Integrability of the base integrand.** For `a < b` and `L, x` `C²`, the
`ε = 0` integrand `t ↦ L(t, x t, x' t)` is integrable on `(a, b)`. -/
theorem base_integrand_integrable
    {a b : ℝ} (_hab : a < b) (L : ℝ → ℝ → ℝ → ℝ) (x : ℝ → ℝ)
    (hL : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2))
    (hx : ContDiff ℝ 2 x) :
    IntegrableOn (fun t => L t (x t) (deriv x t)) (Set.Ioo a b) := by
  let γ : ℝ → ℝ × ℝ × ℝ := fun t => (t, x t, deriv x t)
  have hγ_cont : Continuous γ :=
    (curve_contDiff x hx).continuous
  have hL_cont : Continuous fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2 :=
    hL.continuous
  have h_cont : Continuous (fun t => L t (x t) (deriv x t)) :=
    hL_cont.comp hγ_cont
  have h_int_Icc : IntegrableOn (fun t => L t (x t) (deriv x t)) (Set.Icc a b) :=
    h_cont.integrableOn_Icc
  exact h_int_Icc.mono_set Set.Ioo_subset_Icc_self

/-- **First variation as an integral.** Under the standing hypotheses, the first
variation equals `∫_{(a,b)} (∂_x L(t) h t + ∂_{x'} L(t) h' t) dt`. -/
theorem first_variation
    {a b : ℝ} (L : ℝ → ℝ → ℝ → ℝ) (x h : ℝ → ℝ)
    (hL : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2))
    (hx : ContDiff ℝ 2 x) (hh : ContDiff ℝ ∞ h) (hhsupp : HasCompactSupport h)
    (hsub : tsupport h ⊆ Set.Ioo a b) :
    deriv (fun ε : ℝ => ∫ t in Set.Ioo a b,
        L t (x t + ε * h t) (deriv x t + ε * deriv h t)) 0
      = ∫ t in Set.Ioo a b,
          (lagrangianPartialX L x t * h t + lagrangianPartialV L x t * deriv h t) := by
  by_cases hab : a < b
  · let μ := volume.restrict (Set.Ioo a b)
    let F : ℝ → ℝ → ℝ := fun ε t => L t (x t + ε * h t) (deriv x t + ε * deriv h t)
    let F' : ℝ → ℝ → ℝ := fun ε t =>
      lagrangianPartialXShifted L x h ε t * h t + lagrangianPartialVShifted L x h ε t * deriv h t
    have hr : (0 : ℝ) < 1 := by norm_num
    have hball : Metric.ball (0 : ℝ) 1 ∈ nhds (0 : ℝ) := Metric.ball_mem_nhds (0 : ℝ) hr
    rcases dominating_bound L x h hL hx hh hhsupp hsub hr with ⟨g, hg_int, hg_nonneg, hg_bound⟩
    have hF_meas : ∀ ε, AEStronglyMeasurable (F ε) μ :=
      (integrand_aestronglyMeasurable L x h hL hx hh).1
    have hF_meas_nhds : Filter.Eventually (fun ε => AEStronglyMeasurable (F ε) μ) (nhds (0 : ℝ)) :=
      Filter.Eventually.of_forall hF_meas
    have hF_int : Integrable (F 0) μ := by
      dsimp only [F, μ]
      have h_base := base_integrand_integrable hab L x hL hx
      change Integrable (fun t => L t (x t) (deriv x t))
        (volume.restrict (Set.Ioo a b)) at h_base
      simpa only [zero_mul, add_zero] using h_base
    have hF'_meas : AEStronglyMeasurable (F' 0) μ := by
      simpa [F'] using (integrand_aestronglyMeasurable L x h hL hx hh).2 0
    have h_bound : ∀ᵐ t ∂μ, ∀ ε ∈ Metric.ball (0 : ℝ) 1, |F' ε t| ≤ g t := by
      refine ae_of_all μ (fun t ε hε => ?_)
      have hε' : |ε| ≤ 1 := by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hε
        linarith
      exact hg_bound ε hε' t
    have hL_t_contDiff (t : ℝ) : ContDiff ℝ 2 (fun (p : ℝ × ℝ) => L t p.1 p.2) := by
      have h_embed : ContDiff ℝ 2 (fun (p : ℝ × ℝ) => (t, p.1, p.2)) :=
        contDiff_const.prodMk (contDiff_fst.prodMk contDiff_snd)
      exact hL.comp h_embed
    have hL_t_diff (t : ℝ) (p : ℝ × ℝ) : DifferentiableAt ℝ (fun (q : ℝ × ℝ) => L t q.1 q.2) p :=
      ((hL_t_contDiff t).differentiable (by
        have : (2 : ℕ∞ω) ≠ 0 := by decide
        exact this)).differentiableAt
    have h_diff' : ∀ (t : ℝ) (ε : ℝ), HasDerivAt (F · t) (F' ε t) ε := by
      intro t ε
      apply integrand_hasDerivAt L x h t ε
      exact hL_t_diff t (x t + ε * h t, deriv x t + ε * deriv h t)
    have h_diff : ∀ᵐ t ∂μ, ∀ ε ∈ Metric.ball (0 : ℝ) 1, HasDerivAt (F · t) (F' ε t) ε := by
      refine ae_of_all μ (fun t ε hε => ?_)
      exact h_diff' t ε
    have h_result := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (hs := hball) (hF_meas := hF_meas_nhds) (hF_int := hF_int)
      (F' := F') (hF'_meas := hF'_meas) (h_bound := h_bound)
      (bound_integrable := hg_int.restrict) (h_diff := h_diff)
    have h_F'_zero_eq : F' 0 = fun t => lagrangianPartialX L x t * h t + lagrangianPartialV L x t * deriv h t := by
      ext t
      dsimp [F', lagrangianPartialXShifted, lagrangianPartialVShifted, lagrangianPartialX, lagrangianPartialV]
      simp
    have h_deriv : deriv (fun ε : ℝ => ∫ t in Set.Ioo a b, F ε t) 0 = ∫ t in Set.Ioo a b, F' 0 t := by
      have h_hasDerivAt : HasDerivAt (fun ε : ℝ => ∫ t in Set.Ioo a b, F ε t) (∫ t in Set.Ioo a b, F' 0 t) 0 := by
        simpa [μ, F, F'] using h_result.2
      exact h_hasDerivAt.deriv
    calc
      deriv (fun ε : ℝ => ∫ t in Set.Ioo a b,
          L t (x t + ε * h t) (deriv x t + ε * deriv h t)) 0
          = deriv (fun ε : ℝ => ∫ t in Set.Ioo a b, F ε t) 0 := by
        simp [F]
      _ = ∫ t in Set.Ioo a b, F' 0 t := h_deriv
      _ = ∫ t in Set.Ioo a b,
          (lagrangianPartialX L x t * h t + lagrangianPartialV L x t * deriv h t) := by
        simp [h_F'_zero_eq]
  · -- case a ≥ b: Ioo a b is empty, so both sides are zero
    have h_empty : Set.Ioo a b = ∅ := Set.Ioo_eq_empty_iff.mpr (by linarith)
    simp [h_empty]

/-! ### Integration by parts and the weak equation -/

/-- **A compactly supported variation vanishes at the endpoints.** -/
theorem boundary_vanishing
    {a b : ℝ} (h : ℝ → ℝ) (hsub : tsupport h ⊆ Set.Ioo a b) :
    h a = 0 ∧ h b = 0 := by
  have ha_not : a ∉ Set.Ioo a b := Set.left_notMem_Ioo
  have hb_not : b ∉ Set.Ioo a b := Set.right_notMem_Ioo
  have ha_tsupport : a ∉ tsupport h :=
    mt (fun ha_ts => hsub ha_ts) ha_not
  have hb_tsupport : b ∉ tsupport h :=
    mt (fun hb_ts => hsub hb_ts) hb_not
  have ha_eq : h a = 0 := image_eq_zero_of_notMem_tsupport ha_tsupport
  have hb_eq : h b = 0 := image_eq_zero_of_notMem_tsupport hb_tsupport
  exact And.intro ha_eq hb_eq

/-- **Integral over `(a, b)` as an interval integral.** For `a ≤ b` and `f`
integrable on `(a, b)`, the set integral over `(a, b)` equals `∫ a..b`. -/
theorem ioo_interval_conversion
    {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) (_hf : IntegrableOn f (Set.Ioo a b)) :
    ∫ t in Set.Ioo a b, f t = ∫ t in a..b, f t := by
  -- interval integral ∫_a^b f with a ≤ b equals integral over (a, b]
  rw [intervalIntegral.integral_of_le hab]
  -- integral over (a, b] equals integral over (a, b) since the missing endpoint has measure zero
  rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]

/-- **Differentiability and interval-integrability for integration by parts.**
`∂_{x'} L` and `h` have derivatives everywhere, and the two product integrands
are interval-integrable on `[a, b]`. -/
theorem ibp_hypotheses
    {a b : ℝ} (L : ℝ → ℝ → ℝ → ℝ) (x h : ℝ → ℝ)
    (hL : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2))
    (hx : ContDiff ℝ 2 x) (hh : ContDiff ℝ ∞ h) :
    (∀ t : ℝ, HasDerivAt (lagrangianPartialV L x) (deriv (lagrangianPartialV L x) t) t)
    ∧ (∀ t : ℝ, HasDerivAt h (deriv h t) t)
    ∧ IntervalIntegrable (fun t => lagrangianPartialV L x t * deriv h t) volume a b
    ∧ IntervalIntegrable (fun t => deriv (lagrangianPartialV L x) t * h t) volume a b := by
  have hv_contDiff : ContDiff ℝ 1 (lagrangianPartialV L x) :=
    lagrangianPartialV_contDiff L x hL hx
  have hv_diff : Differentiable ℝ (lagrangianPartialV L x) :=
    hv_contDiff.differentiable (by decide : (1 : ℕ∞ω) ≠ 0)
  have hv_cont : Continuous (lagrangianPartialV L x) :=
    hv_contDiff.continuous
  have hderiv_cont : Continuous (deriv (lagrangianPartialV L x)) :=
    hv_contDiff.continuous_deriv (by decide : (1 : ℕ∞ω) ≤ (1 : ℕ∞ω))
  have h_cont : Continuous h :=
    hh.continuous
  have hderiv_h_cont : Continuous (deriv h) :=
    hh.continuous_deriv (by decide : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω))
  have h_hasDeriv : ∀ t : ℝ, HasDerivAt h (deriv h t) t :=
    fun t => (hh.differentiable (by decide : (∞ : ℕ∞ω) ≠ 0) t).hasDerivAt
  have hv_hasDeriv : ∀ t : ℝ, HasDerivAt (lagrangianPartialV L x) (deriv (lagrangianPartialV L x) t) t :=
    fun t => (hv_diff t).hasDerivAt
  have h_int_prod1 : IntervalIntegrable (fun t => lagrangianPartialV L x t * deriv h t) volume a b :=
    (hv_cont.mul hderiv_h_cont).intervalIntegrable a b
  have h_int_prod2 : IntervalIntegrable (fun t => deriv (lagrangianPartialV L x) t * h t) volume a b :=
    (hderiv_cont.mul h_cont).intervalIntegrable a b
  exact ⟨hv_hasDeriv, h_hasDeriv, h_int_prod1, h_int_prod2⟩

/-- **Integration by parts for the velocity term.** -/
theorem integration_by_parts
    {a b : ℝ} (hab : a < b) (L : ℝ → ℝ → ℝ → ℝ) (x h : ℝ → ℝ)
    (hL : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2))
    (hx : ContDiff ℝ 2 x) (hh : ContDiff ℝ ∞ h) (_hhsupp : HasCompactSupport h)
    (hsub : tsupport h ⊆ Set.Ioo a b) :
    (∫ t in Set.Ioo a b, lagrangianPartialV L x t * deriv h t)
      = - ∫ t in Set.Ioo a b, deriv (lagrangianPartialV L x) t * h t := by
  have h_ibp := ibp_hypotheses (a := a) (b := b) L x h hL hx hh
  rcases h_ibp with ⟨hu_deriv, hv_deriv, h_int_prod1, h_int_prod2⟩
  have hab_le : a ≤ b := le_of_lt hab
  have ⟨ha0, hb0⟩ : h a = 0 ∧ h b = 0 := boundary_vanishing h hsub
  -- `lagrangianPartialV L x` is C¹, hence its derivative is continuous → interval-integrable
  have h_contDiff_v : ContDiff ℝ 1 (lagrangianPartialV L x) :=
    lagrangianPartialV_contDiff L x hL hx
  have h_cont_u' : Continuous (deriv (lagrangianPartialV L x)) :=
    h_contDiff_v.continuous_deriv (le_refl (1 : ℕ∞ω))
  have h_int_u' : IntervalIntegrable (deriv (lagrangianPartialV L x)) volume a b :=
    h_cont_u'.intervalIntegrable a b
  -- `h` is smooth, hence `deriv h` is continuous → interval-integrable
  have h_cont_v' : Continuous (deriv h) :=
    hh.continuous_deriv (by simp : (1 : ℕ∞ω) ≤ ∞)
  have h_int_v' : IntervalIntegrable (deriv h) volume a b :=
    h_cont_v'.intervalIntegrable a b
  -- Apply the interval integration by parts lemma
  have h_ibp_inter := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun t _ht => hu_deriv t)
    (fun t _ht => hv_deriv t)
    h_int_u' h_int_v'
  -- h_ibp_inter: ∫ t in a..b, (lagrangianPartialV L x) t * (deriv h) t
  --   = (lagrangianPartialV L x) b * h b - (lagrangianPartialV L x) a * h a
  --     - ∫ t in a..b, (deriv (lagrangianPartialV L x)) t * h t
  have h_boundary_terms : (lagrangianPartialV L x) b * h b - (lagrangianPartialV L x) a * h a = 0 := by
    simp [ha0, hb0]
  have h_ibp_simp : (∫ t in a..b, lagrangianPartialV L x t * deriv h t)
      = -(∫ t in a..b, deriv (lagrangianPartialV L x) t * h t) := by
    linarith [h_ibp_inter, h_boundary_terms]
  -- Convert interval integrals to set integrals over Ioo a b
  have h_int_lhs : IntegrableOn (fun t : ℝ => lagrangianPartialV L x t * deriv h t) (Set.Ioo a b) :=
    (h_int_prod1.1).mono_set Set.Ioo_subset_Ioc_self
  have h_int_rhs : IntegrableOn (fun t : ℝ => deriv (lagrangianPartialV L x) t * h t) (Set.Ioo a b) :=
    (h_int_prod2.1).mono_set Set.Ioo_subset_Ioc_self
  have h_conv_lhs := ioo_interval_conversion hab_le (fun t => lagrangianPartialV L x t * deriv h t) h_int_lhs
  have h_conv_rhs := ioo_interval_conversion hab_le (fun t => deriv (lagrangianPartialV L x) t * h t) h_int_rhs
  calc
    (∫ t in Set.Ioo a b, lagrangianPartialV L x t * deriv h t)
        = (∫ t in a..b, lagrangianPartialV L x t * deriv h t) := h_conv_lhs
    _ = -(∫ t in a..b, deriv (lagrangianPartialV L x) t * h t) := h_ibp_simp
    _ = -(∫ t in Set.Ioo a b, deriv (lagrangianPartialV L x) t * h t) := by rw [h_conv_rhs]

/-- **The weak-equation integrands are integrable.** Each of `∂_x L · h`,
`∂_{x'} L · h'`, and `(d/dt ∂_{x'} L) · h` is continuous with compact support,
hence integrable. -/
theorem weak_el_integrands_integrable
    (L : ℝ → ℝ → ℝ → ℝ) (x h : ℝ → ℝ)
    (hL : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2))
    (hx : ContDiff ℝ 2 x) (hh : ContDiff ℝ ∞ h) (hhsupp : HasCompactSupport h) :
    Integrable (fun t => lagrangianPartialX L x t * h t)
    ∧ Integrable (fun t => lagrangianPartialV L x t * deriv h t)
    ∧ Integrable (fun t => deriv (lagrangianPartialV L x) t * h t) := by
  -- ∂_x L is continuous, and h is continuous with compact support
  have hx_cont : Continuous (lagrangianPartialX L x) :=
    lagrangianPartialX_continuous L x hL hx
  have h_cont : Continuous h :=
    hh.continuous
  have hx_prod_cont : Continuous (fun t => lagrangianPartialX L x t * h t) :=
    hx_cont.mul h_cont
  have hx_prod_supp : HasCompactSupport (fun t => lagrangianPartialX L x t * h t) :=
    hhsupp.mul_left
  have hx_integrable : Integrable (fun t => lagrangianPartialX L x t * h t) :=
    continuous_compactSupport_integrable hx_prod_cont hx_prod_supp

  -- ∂_v L is C¹, hence continuous; deriv h is continuous and compactly supported
  have hv_contDiff : ContDiff ℝ 1 (lagrangianPartialV L x) :=
    lagrangianPartialV_contDiff L x hL hx
  have hv_cont : Continuous (lagrangianPartialV L x) :=
    hv_contDiff.continuous
  have hderiv_cont : Continuous (deriv h) :=
    hh.continuous_deriv (by decide : 1 ≤ (∞ : ℕ∞ω))
  have hv_prod_cont : Continuous (fun t => lagrangianPartialV L x t * deriv h t) :=
    hv_cont.mul hderiv_cont
  have hderiv_supp : HasCompactSupport (deriv h) :=
    hhsupp.deriv
  have hv_prod_supp : HasCompactSupport (fun t => lagrangianPartialV L x t * deriv h t) :=
    hderiv_supp.mul_left
  have hv_integrable : Integrable (fun t => lagrangianPartialV L x t * deriv h t) :=
    continuous_compactSupport_integrable hv_prod_cont hv_prod_supp

  -- (d/dt) ∂_v L is continuous, and h is continuous with compact support
  have hderiv_v_cont : Continuous (deriv (lagrangianPartialV L x)) :=
    hv_contDiff.continuous_deriv (le_refl (1 : ℕ∞ω))
  have hderiv_v_prod_cont : Continuous (fun t => deriv (lagrangianPartialV L x) t * h t) :=
    hderiv_v_cont.mul h_cont
  have hderiv_v_prod_supp : HasCompactSupport (fun t => deriv (lagrangianPartialV L x) t * h t) :=
    hhsupp.mul_left
  have hderiv_v_integrable : Integrable (fun t => deriv (lagrangianPartialV L x) t * h t) :=
    continuous_compactSupport_integrable hderiv_v_prod_cont hderiv_v_prod_supp

  exact ⟨hx_integrable, hv_integrable, hderiv_v_integrable⟩

/-- **Weak Euler–Lagrange equation.** For a variational extremum `x`, the defect
tested against any admissible `h` integrates to zero over `(a, b)`. -/
theorem weak_euler_lagrange
    {a b : ℝ} (hab : a < b) (L : ℝ → ℝ → ℝ → ℝ) (x : ℝ → ℝ)
    (hL : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2))
    (hx : ContDiff ℝ 2 x) (hxe : IsVariationalExtremum a b L x)
    (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h) (hhsupp : HasCompactSupport h)
    (hsub : tsupport h ⊆ Set.Ioo a b) :
    (∫ t in Set.Ioo a b,
      (lagrangianPartialX L x t - deriv (lagrangianPartialV L x) t) * h t) = 0 := by
  rcases hxe with ⟨hx_c1, hx_ext⟩
  have h_var_zero : deriv (fun ε : ℝ => ∫ t in Set.Ioo a b,
      L t (x t + ε * h t) (deriv x t + ε * deriv h t)) 0 = 0 :=
    hx_ext h hh hhsupp hsub
  have h_first_var_eq : deriv (fun ε : ℝ => ∫ t in Set.Ioo a b,
      L t (x t + ε * h t) (deriv x t + ε * deriv h t)) 0
    = ∫ t in Set.Ioo a b,
        (lagrangianPartialX L x t * h t + lagrangianPartialV L x t * deriv h t) :=
    first_variation L x h hL hx hh hhsupp hsub
  have h_int_sum_zero : (∫ t in Set.Ioo a b,
      (lagrangianPartialX L x t * h t + lagrangianPartialV L x t * deriv h t)) = 0 := by
    rw [← h_first_var_eq, h_var_zero]
  have h_int_parts : (∫ t in Set.Ioo a b, lagrangianPartialV L x t * deriv h t)
    = -∫ t in Set.Ioo a b, deriv (lagrangianPartialV L x) t * h t :=
    integration_by_parts hab L x h hL hx hh hhsupp hsub
  rcases weak_el_integrands_integrable L x h hL hx hh hhsupp with
    ⟨h_intX, h_intV, h_intD⟩
  have h_intX_on : IntegrableOn (fun t => lagrangianPartialX L x t * h t) (Set.Ioo a b) :=
    h_intX.integrableOn
  have h_intV_on : IntegrableOn (fun t => lagrangianPartialV L x t * deriv h t) (Set.Ioo a b) :=
    h_intV.integrableOn
  have h_intD_on : IntegrableOn (fun t => deriv (lagrangianPartialV L x) t * h t) (Set.Ioo a b) :=
    h_intD.integrableOn
  have h_sum_eq_add : (∫ t in Set.Ioo a b,
      (lagrangianPartialX L x t * h t + lagrangianPartialV L x t * deriv h t))
    = (∫ t in Set.Ioo a b, lagrangianPartialX L x t * h t)
      + (∫ t in Set.Ioo a b, lagrangianPartialV L x t * deriv h t) :=
    integral_add h_intX_on h_intV_on
  rw [h_sum_eq_add, h_int_parts] at h_int_sum_zero
  -- h_int_sum_zero now: (∫ ∂_x L * h) + (-∫ (d/dt ∂_{x'} L) * h) = 0
  have h_diff_zero : (∫ t in Set.Ioo a b, lagrangianPartialX L x t * h t)
    - (∫ t in Set.Ioo a b, deriv (lagrangianPartialV L x) t * h t) = 0 := by
    linarith
  have h_sub_target : (∫ t in Set.Ioo a b,
      (lagrangianPartialX L x t * h t - deriv (lagrangianPartialV L x) t * h t)) = 0 := by
    rw [integral_sub h_intX_on h_intD_on, h_diff_zero]
  have h_eq_integrand : (fun t : ℝ => (lagrangianPartialX L x t - deriv (lagrangianPartialV L x) t) * h t)
      = (fun t : ℝ => lagrangianPartialX L x t * h t - deriv (lagrangianPartialV L x) t * h t) := by
    ext t; ring
  rw [h_eq_integrand, h_sub_target]

/-- **Weak equation in `∫ g • f` shape over the full measure.** The defect tested
against any admissible `h` integrates to zero against the full volume measure, in
the form required by the fundamental lemma of the calculus of variations. -/
theorem defect_test_integral_vanishes
    {a b : ℝ} (hab : a < b) (L : ℝ → ℝ → ℝ → ℝ) (x : ℝ → ℝ)
    (hL : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2))
    (hx : ContDiff ℝ 2 x) (hxe : IsVariationalExtremum a b L x) :
    ∀ h : ℝ → ℝ, ContDiff ℝ ∞ h → HasCompactSupport h → tsupport h ⊆ Set.Ioo a b →
      (∫ t, h t • (lagrangianPartialX L x t - deriv (lagrangianPartialV L x) t)) = 0 := by
  intro h hh hhsupp hsub
  set D := fun t : ℝ => lagrangianPartialX L x t - deriv (lagrangianPartialV L x) t with hD
  have h_weak_zero : (∫ t in Set.Ioo a b, D t * h t) = 0 := by
    simpa [hD] using weak_euler_lagrange hab L x hL hx hxe h hh hhsupp hsub
  have h_outside : ∀ t, t ∉ Set.Ioo a b → h t • D t = 0 := by
    intro t ht_out
    have ht_not_tsupport : t ∉ tsupport h := by
      intro ht_ts
      exact ht_out (hsub ht_ts)
    have h_zero : h t = 0 := image_eq_zero_of_notMem_tsupport ht_not_tsupport
    simp [h_zero]
  have h_full_eq_Ioo : (∫ t, h t • D t) = (∫ t in Set.Ioo a b, h t • D t) := by
    symm
    exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero h_outside
  calc
    (∫ t, h t • (lagrangianPartialX L x t - deriv (lagrangianPartialV L x) t)) = (∫ t, h t • D t) := by
      simp [hD]
    _ = (∫ t in Set.Ioo a b, h t • D t) := h_full_eq_Ioo
    _ = (∫ t in Set.Ioo a b, D t * h t) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo ?_
      intro t ht
      simp [mul_comm, smul_eq_mul]
    _ = 0 := h_weak_zero

/-- **Euler–Lagrange equation** (§44). On an interval `a < b`, every `C²`
variational extremum `x` of the action `I(y) = ∫_a^b L(t, y(t), y'(t)) dt`, with
`C²` Lagrangian `L`, satisfies the pointwise equation
`∂L/∂x (t, x(t), x'(t)) = (d/dt)(∂L/∂x' (t, x(t), x'(t)))` on `(a, b)`. -/
@[eval_problem]
theorem euler_lagrange_equation
    {a b : ℝ} (L : ℝ → ℝ → ℝ → ℝ) (x : ℝ → ℝ) (hab : a < b)
    (hL : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2))
    (hx : ContDiff ℝ 2 x)
    (hxe : IsVariationalExtremum a b L x) :
    ∀ t ∈ Set.Ioo a b,
      lagrangianPartialX L x t = deriv (lagrangianPartialV L x) t := by
  -- The Euler--Lagrange defect D(t) = ∂_x L(t) - (d/dt) ∂_{x'} L(t)
  set D : ℝ → ℝ := fun t => lagrangianPartialX L x t - deriv (lagrangianPartialV L x) t with hD
  have hD_cont : Continuous D :=
    el_defect_continuous L x hL hx
  have hU_open : IsOpen (Set.Ioo a b) :=
    isOpen_Ioo
  -- D is locally integrable on (a,b) because it is continuous
  have hD_locInt : LocallyIntegrableOn D (Set.Ioo a b) volume := by
    refine hD_cont.continuousOn.locallyIntegrableOn ?_
    exact measurableSet_Ioo
  -- defect_test_integral_vanishes says ∫ h • D = 0 for every smooth compactly supported h
  have h_integral_vanishes : ∀ (h : ℝ → ℝ), ContDiff ℝ ∞ h → HasCompactSupport h →
      tsupport h ⊆ Set.Ioo a b → (∫ t, h t • D t) = 0 := by
    intro h hh hhsupp hhsub
    have hh' : tsupport h ⊆ Set.Ioo a b := hhsub
    simpa [hD, sub_eq_zero] using
      defect_test_integral_vanishes hab L x hL hx hxe h hh hhsupp hh'
  -- The fundamental lemma of the calculus of variations: D = 0 a.e. on (a,b)
  have hD_ae : ∀ᵐ t ∂volume, t ∈ Set.Ioo a b → D t = 0 :=
    hU_open.ae_eq_zero_of_integral_contDiff_smul_eq_zero hD_locInt h_integral_vanishes
  -- Convert to the restricted-measure form required by eqOn_Ioo_of_ae_eq
  have hD_ae_restrict : D =ᵐ[volume.restrict (Set.Ioo a b)] (fun _ : ℝ => (0 : ℝ)) :=
    ((ae_restrict_iff' (measurableSet_Ioo (a := a) (b := b))).mpr hD_ae)
  -- D is continuous and 0 is continuous, so a.e.-equality upgrades to everywhere equality on (a,b)
  have hD_eqOn : Set.EqOn D (fun _ => (0 : ℝ)) (Set.Ioo a b) :=
    MeasureTheory.Measure.eqOn_Ioo_of_ae_eq (volume : Measure ℝ) hD_ae_restrict hD_cont.continuousOn
      (continuous_const.continuousOn)
  -- Conclude: D(t) = 0 for all t in (a,b), i.e. ∂_x L(t) = (d/dt) ∂_{x'} L(t)
  intro t ht
  have hDzero : D t = 0 := hD_eqOn ht
  dsimp [D] at hDzero
  linarith

end Analysis
end LeanEval
