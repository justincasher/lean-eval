import LeanEval.KnotTheory.Prelude
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
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
All statements are stated with `sorry`; the two genuinely hard inputs
(`deformedIntegrand_r_divergence` and `hopf_linking_value`) are accepted
assumptions of the benchmark.
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

/-- **Smoothness of the Gauss map.** -/
theorem TwoLink.gaussMap_smooth (Lk : TwoLink) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => Lk.gaussMap p.1 p.2) := by
  sorry

/-- **Continuity of a knot's velocity.** A knot is smooth, hence its derivative
is continuous. -/
theorem Knot.continuous_deriv (γ : Knot) : Continuous (deriv γ.curve) := by
  sorry

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

/-- **Joint smoothness of the deformed integrand**, together with its
`r`-derivative. -/
theorem deformedIntegrand_smooth (Lk : TwoLink) (Φ : AmbientIsotopy) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × ℝ => deformedIntegrand Lk Φ p.1 p.2.1 p.2.2) ∧
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × ℝ =>
      deriv (fun r => deformedIntegrand Lk Φ r p.2.1 p.2.2) p.1) := by
  sorry

/-- **Accepted assumption: the `r`-derivative is an `(s,t)`-divergence.**
The coordinate form of the closedness of the solid-angle 2-form. -/
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
  sorry

/-- **Periodicity of a coordinate circle.** -/
theorem coordinateCircle_periodic (p₀ : R3) (i j : Fin 3) (t : ℝ) :
    coordinateCircle p₀ i j (t + 2 * Real.pi) = coordinateCircle p₀ i j t := by
  simp [coordinateCircle, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- **Velocity of a coordinate circle.** -/
theorem coordinateCircle_deriv (p₀ : R3) (i j : Fin 3) (t : ℝ) :
    deriv (coordinateCircle p₀ i j) t
      = -Real.sin t • EuclideanSpace.single i (1 : ℝ)
        + Real.cos t • EuclideanSpace.single j (1 : ℝ) := by
  sorry

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

/-- **Inner integral of the unlink integrand vanishes** for every `t`. -/
theorem unlink_inner_integral_zero (t : ℝ) :
    ∫ s in (0 : ℝ)..(2 * Real.pi), linkingIntegrand unlink.K.curve unlink.L.curve s t = 0 := by
  sorry

/-- **The unlink has linking number zero.** -/
theorem linking_unlink_zero : unlink.linkingNumber = 0 := by
  sorry

/-- **Accepted assumption: the Hopf Gauss integral.** The double integral
evaluates to `4π`, so `lk(L₂) = 1`. -/
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
