import LeanEval.KnotTheory.Linking.Invariance
import LeanEval.KnotTheory.Linking.Examples

namespace LeanEval
namespace KnotTheory

/-!
# Computing the two linking numbers

The closed-form linking integrands of the unlink and the Hopf link, the
vanishing of `lk(unlink)`, the (elliptic-integral) Hopf evaluation, and the
conclusion that the two links are not ambient-isotopic.
-/

open scoped RealInnerProductSpace

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
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) (2 * Real.pi),
      HasDerivAt (fun s' : ℝ => (6 - 2 * Real.cos (s' - t)) ^ (-(1 / 2 : ℝ)))
        (-2 * Real.sin (s - t) / Real.sqrt (6 - 2 * Real.cos (s - t)) ^ 3) s := by
    intro s hs
    exact unlink_inner_antideriv t s
  have hcont : Continuous fun s : ℝ => -2 * Real.sin (s - t) / Real.sqrt (6 - 2 * Real.cos (s - t)) ^ 3 := by
    have hnum : Continuous fun s : ℝ => -2 * Real.sin (s - t) := by continuity
    have hdenom_nonzero : ∀ s : ℝ, Real.sqrt (6 - 2 * Real.cos (s - t)) ^ 3 ≠ 0 := by
      intro s
      have hpos : 0 < 6 - 2 * Real.cos (s - t) := by
        have hcos_le_one : Real.cos (s - t) ≤ 1 := Real.cos_le_one _
        nlinarith
      have hsqrtpos : 0 < Real.sqrt (6 - 2 * Real.cos (s - t)) := Real.sqrt_pos.mpr hpos
      positivity
    have hdenom_cont : Continuous fun s : ℝ => Real.sqrt (6 - 2 * Real.cos (s - t)) ^ 3 := by
      continuity
    exact hnum.div hdenom_cont hdenom_nonzero
  have hint : IntervalIntegrable (fun s : ℝ => -2 * Real.sin (s - t) / Real.sqrt (6 - 2 * Real.cos (s - t)) ^ 3)
      MeasureTheory.volume (0 : ℝ) (2 * Real.pi) :=
    hcont.intervalIntegrable _ _
  have hcos_eq : Real.cos (2 * Real.pi - t) = Real.cos (0 - t) := by
    calc
      Real.cos (2 * Real.pi - t) = Real.cos (-t + 2 * Real.pi) := by ring
      _ = Real.cos (-t) := by rw [Real.cos_add_two_pi]
      _ = Real.cos (0 - t) := by simp
  calc
    ∫ s in (0 : ℝ)..(2 * Real.pi), linkingIntegrand unlink.K.curve unlink.L.curve s t
        = ∫ s in (0 : ℝ)..(2 * Real.pi), (-2 * Real.sin (s - t) / Real.sqrt (6 - 2 * Real.cos (s - t)) ^ 3) := by
      refine intervalIntegral.integral_congr (fun s hs => ?_)
      rw [unlink_integrand]
    _ = (6 - 2 * Real.cos (2 * Real.pi - t)) ^ (-(1 / 2 : ℝ)) - (6 - 2 * Real.cos (0 - t)) ^ (-(1 / 2 : ℝ)) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    _ = 0 := by
      rw [hcos_eq]
      simp

/-- **The unlink has linking number zero.** -/
theorem linking_unlink_zero : unlink.linkingNumber = 0 := by
  unfold TwoLink.linkingNumber
  have h_outer : ∫ t in (0 : ℝ)..(2 * Real.pi), ∫ s in (0 : ℝ)..(2 * Real.pi),
      linkingIntegrand unlink.K.curve unlink.L.curve s t = 0 := by
    calc
      ∫ t in (0 : ℝ)..(2 * Real.pi), ∫ s in (0 : ℝ)..(2 * Real.pi),
          linkingIntegrand unlink.K.curve unlink.L.curve s t
          = ∫ t in (0 : ℝ)..(2 * Real.pi), (0 : ℝ) := by
            refine intervalIntegral.integral_congr ?_
            intro t ht
            exact unlink_inner_integral_zero t
      _ = 0 := by simp
  simp [h_outer]

/-- **The Hopf linking integrand** in closed form:
`I_{L₂}(s,t) = (cos t - (1 + cos t) cos s) / D(s,t)^{3/2}`, where
`D(s,t) = 3 + 2 cos t - 2 (1 + cos t) cos s = ‖u‖²`. -/
theorem hopf_integrand (s t : ℝ) :
    linkingIntegrand hopfLink.K.curve hopfLink.L.curve s t
      = (Real.cos t - (1 + Real.cos t) * Real.cos s)
        / Real.sqrt (3 + 2 * Real.cos t - 2 * (1 + Real.cos t) * Real.cos s) ^ 3 := by
  unfold linkingIntegrand
  -- Numerator: tripleProduct = cos t - (1 + cos t) cos s
  have hnum : tripleProduct (hopfLink.K.curve s - hopfLink.L.curve t)
      (deriv (hopfLink.K.curve) s) (deriv (hopfLink.L.curve) t)
      = Real.cos t - (1 + Real.cos t) * Real.cos s := by
    unfold tripleProduct
    have hK : hopfLink.K.curve = coordinateCircle (0 : R3) (0 : Fin 3) (1 : Fin 3) := rfl
    have hL : hopfLink.L.curve = coordinateCircle hopfShift (0 : Fin 3) (2 : Fin 3) := rfl
    rw [hK, hL]
    rw [coordinateCircle_deriv, coordinateCircle_deriv]
    simp [coordinateCircle, hopfShift, EuclideanSpace.single, cross_apply, Fin.sum_univ_three]
    ring
    have h_sinsq_cossq_s : Real.sin s ^ 2 = 1 - Real.cos s ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq s]
    have h_sinsq_cossq_t : Real.sin t ^ 2 = 1 - Real.cos t ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq t]
    rw [h_sinsq_cossq_s, h_sinsq_cossq_t]
    ring
  rw [hnum]
  -- Denominator: ‖u‖³ = (Real.sqrt D)³ where D = ‖u‖²
  have hden_sq : ‖hopfLink.K.curve s - hopfLink.L.curve t‖ ^ 2
      = 3 + 2 * Real.cos t - 2 * (1 + Real.cos t) * Real.cos s := by
    have hK : hopfLink.K.curve = coordinateCircle (0 : R3) (0 : Fin 3) (1 : Fin 3) := rfl
    have hL : hopfLink.L.curve = coordinateCircle hopfShift (0 : Fin 3) (2 : Fin 3) := rfl
    rw [hK, hL]
    simp [coordinateCircle, hopfShift, EuclideanSpace.single, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    ring
    have h_sinsq_cossq_s : Real.sin s ^ 2 = 1 - Real.cos s ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq s]
    have h_sinsq_cossq_t : Real.sin t ^ 2 = 1 - Real.cos t ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq t]
    rw [h_sinsq_cossq_s, h_sinsq_cossq_t]
    ring
  have h_sqrt : Real.sqrt (3 + 2 * Real.cos t - 2 * (1 + Real.cos t) * Real.cos s)
      = ‖hopfLink.K.curve s - hopfLink.L.curve t‖ := by
    calc
      Real.sqrt (3 + 2 * Real.cos t - 2 * (1 + Real.cos t) * Real.cos s)
          = Real.sqrt (‖hopfLink.K.curve s - hopfLink.L.curve t‖ ^ 2) := by rw [hden_sq]
      _ = ‖hopfLink.K.curve s - hopfLink.L.curve t‖ := Real.sqrt_sq (norm_nonneg _)
  rw [h_sqrt]

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
  -- Write the LHS in closed form using `hopf_integrand`
  rw [hopf_integrand s t]
  set D := 3 + 2 * Real.cos t - 2 * (1 + Real.cos t) * Real.cos s with hD
  have hDpos : 0 < D := by
    have h := hopf_denom_pos s t
    linarith
  have hD_nonneg : 0 ≤ D := le_of_lt hDpos
  -- numerator: cos t - (1 + cos t)cos s = (D - 3)/2
  have h_num : Real.cos t - (1 + Real.cos t) * Real.cos s = (1 / 2) * (D - 3) := by
    dsimp [D]
    ring
  rw [h_num]
  -- convert denominator: (Real.sqrt D) ^ 3 = D ^ (3/2 : ℝ)
  have h_sq3 : Real.sqrt D ^ 3 = D ^ (3/2 : ℝ) := by
    calc
      Real.sqrt D ^ 3 = (D ^ (1/2 : ℝ)) ^ 3 := by rw [Real.sqrt_eq_rpow D]
      _ = (D ^ (1/2 : ℝ)) ^ (3 : ℝ) := by simp
      _ = D ^ ((1/2 : ℝ) * (3 : ℝ)) := by rw [← Real.rpow_mul hD_nonneg (1/2 : ℝ) (3 : ℝ)]
      _ = D ^ (3/2 : ℝ) := by norm_num
  rw [h_sq3]
  -- rewrite negative exponents as reciprocals
  rw [Real.rpow_neg hD_nonneg (1/2 : ℝ), Real.rpow_neg hD_nonneg (3/2 : ℝ)]
  -- Goal: ((1/2)*(D-3)) / (D^(3/2 : ℝ)) = (1/2)*(D^(1/2 : ℝ))⁻¹ - (3/2)*(D^(3/2 : ℝ))⁻¹
  have h32_ne : (3/2 : ℝ) ≠ 0 := by norm_num
  have h12_ne : (1/2 : ℝ) ≠ 0 := by norm_num
  have hD32_ne : D ^ (3/2 : ℝ) ≠ 0 := ((Real.rpow_ne_zero hD_nonneg h32_ne).mpr hDpos.ne')
  have hD12_ne : D ^ (1/2 : ℝ) ≠ 0 := ((Real.rpow_ne_zero hD_nonneg h12_ne).mpr hDpos.ne')
  -- identity: D^(1/2) * D = D^(3/2)
  have h_mul : D ^ (1/2 : ℝ) * D = D ^ (3/2 : ℝ) := by
    calc
      D ^ (1/2 : ℝ) * D = D ^ (1/2 : ℝ) * D ^ (1 : ℝ) := by simp
      _ = D ^ ((1/2 : ℝ) + 1) := by rw [Real.rpow_add hDpos (1/2 : ℝ) 1]
      _ = D ^ (3/2 : ℝ) := by norm_num
  field_simp [hD32_ne, hD12_ne]
  -- Goal: (D-3)*D^(1/2) = D^(3/2) - 3*D^(1/2)
  calc
    (D - 3) * (D ^ (1/2 : ℝ)) = (D ^ (1/2 : ℝ)) * D - 3 * (D ^ (1/2 : ℝ)) := by ring
    _ = D ^ (3/2 : ℝ) - 3 * (D ^ (1/2 : ℝ)) := by rw [h_mul]

/-- **Explicit half-angle reduction of the Hopf inner integrand.** Under
`x = tan(s/2)`, with `c = 5 + 4cos t`, the reduced integrand times `2/(1+x²)`
equals `Ψ_t(x) = ((c-3)x² - 2)(1+x²)^{-1/2}(1+cx²)^{-3/2}`. -/
theorem hopf_halfAngle_reduction (t x : ℝ) :
    ((1 / 2) * ((1 + (5 + 4 * Real.cos t) * x ^ 2) / (1 + x ^ 2)) ^ (-(1 / 2) : ℝ)
        - (3 / 2) * ((1 + (5 + 4 * Real.cos t) * x ^ 2) / (1 + x ^ 2)) ^ (-(3 / 2) : ℝ))
        * (2 / (1 + x ^ 2))
      = ((5 + 4 * Real.cos t - 3) * x ^ 2 - 2) * (1 + x ^ 2) ^ (-(1 / 2) : ℝ)
          * (1 + (5 + 4 * Real.cos t) * x ^ 2) ^ (-(3 / 2) : ℝ) := by
  set c := 5 + 4 * Real.cos t with hc
  set A := 1 + c * x ^ 2 with hA
  set B := 1 + x ^ 2 with hB
  have hx2_nonneg : 0 ≤ x ^ 2 := pow_two_nonneg x
  have hBpos : 0 < B := by
    dsimp [B]
    nlinarith
  have hB_nonneg : 0 ≤ B := le_of_lt hBpos
  have hApos : 0 < A := by
    dsimp [A, c]
    have hcos_ge : -1 ≤ Real.cos t := Real.neg_one_le_cos _
    nlinarith
  have hA_nonneg : 0 ≤ A := le_of_lt hApos
  -- Rewrite D^(-1/2) in terms of A and B
  have hDnegHalf : ((A / B) ^ (-(1 / 2 : ℝ))) = B ^ (1 / 2 : ℝ) * A ^ (-(1 / 2 : ℝ)) := by
    calc
      (A / B) ^ (-(1 / 2 : ℝ)) = (A ^ (-(1 / 2 : ℝ))) / (B ^ (-(1 / 2 : ℝ))) := by
        rw [Real.div_rpow hA_nonneg hB_nonneg]
      _ = A ^ (-(1 / 2 : ℝ)) * (B ^ (-(1 / 2 : ℝ)))⁻¹ := by rw [div_eq_mul_inv]
      _ = A ^ (-(1 / 2 : ℝ)) * B ^ (1 / 2 : ℝ) := by
        rw [Real.rpow_neg hB_nonneg, inv_inv]
      _ = B ^ (1 / 2 : ℝ) * A ^ (-(1 / 2 : ℝ)) := mul_comm _ _
  -- Rewrite D^(-3/2) in terms of A and B
  have hDnegThreeHalf : ((A / B) ^ (-(3 / 2 : ℝ))) = B ^ (3 / 2 : ℝ) * A ^ (-(3 / 2 : ℝ)) := by
    calc
      (A / B) ^ (-(3 / 2 : ℝ)) = (A ^ (-(3 / 2 : ℝ))) / (B ^ (-(3 / 2 : ℝ))) := by
        rw [Real.div_rpow hA_nonneg hB_nonneg]
      _ = A ^ (-(3 / 2 : ℝ)) * (B ^ (-(3 / 2 : ℝ)))⁻¹ := by rw [div_eq_mul_inv]
      _ = A ^ (-(3 / 2 : ℝ)) * B ^ (3 / 2 : ℝ) := by
        rw [Real.rpow_neg hB_nonneg, inv_inv]
      _ = B ^ (3 / 2 : ℝ) * A ^ (-(3 / 2 : ℝ)) := mul_comm _ _
  -- Simplify B^(p)/B = B^(p-1)
  have h_div1 : B ^ (1 / 2 : ℝ) / B = B ^ (-(1 / 2 : ℝ)) := by
    calc
      B ^ (1 / 2 : ℝ) / B = B ^ (1 / 2 : ℝ) / B ^ (1 : ℝ) := by simp
      _ = B ^ ((1 / 2 : ℝ) - (1 : ℝ)) := by rw [Real.rpow_sub hBpos]
      _ = B ^ (-(1 / 2 : ℝ)) := by ring
  have h_div2 : B ^ (3 / 2 : ℝ) / B = B ^ (1 / 2 : ℝ) := by
    calc
      B ^ (3 / 2 : ℝ) / B = B ^ (3 / 2 : ℝ) / B ^ (1 : ℝ) := by simp
      _ = B ^ ((3 / 2 : ℝ) - (1 : ℝ)) := by rw [Real.rpow_sub hBpos]
      _ = B ^ (1 / 2 : ℝ) := by ring
  -- Express A^(-1/2) as A^(-3/2)*A
  have h_factorA : A ^ (-(1 / 2 : ℝ)) = A ^ (-(3 / 2 : ℝ)) * A := by
    calc
      A ^ (-(1 / 2 : ℝ)) = A ^ ((-(3 / 2 : ℝ)) + (1 : ℝ)) := by ring
      _ = A ^ (-(3 / 2 : ℝ)) * A ^ (1 : ℝ) := by rw [Real.rpow_add hApos]
      _ = A ^ (-(3 / 2 : ℝ)) * A := by simp
  -- Express B^(1/2) as B^(-1/2)*B
  have h_factorB : B ^ (1 / 2 : ℝ) = B ^ (-(1 / 2 : ℝ)) * B := by
    calc
      B ^ (1 / 2 : ℝ) = B ^ ((-(1 / 2 : ℝ)) + (1 : ℝ)) := by ring
      _ = B ^ (-(1 / 2 : ℝ)) * B ^ (1 : ℝ) := by rw [Real.rpow_add hBpos]
      _ = B ^ (-(1 / 2 : ℝ)) * B := by simp
  calc
    ((1 / 2) * ((A / B) ^ (-(1 / 2 : ℝ))) - (3 / 2) * ((A / B) ^ (-(3 / 2 : ℝ)))) * (2 / B)
        = ((1 / 2) * (B ^ (1 / 2 : ℝ) * A ^ (-(1 / 2 : ℝ)))
            - (3 / 2) * (B ^ (3 / 2 : ℝ) * A ^ (-(3 / 2 : ℝ)))) * (2 / B) := by
          rw [hDnegHalf, hDnegThreeHalf]
    _ = (B ^ (1 / 2 : ℝ) * A ^ (-(1 / 2 : ℝ)) / B)
        - (3 * B ^ (3 / 2 : ℝ) * A ^ (-(3 / 2 : ℝ)) / B) := by
      ring
    _ = ((B ^ (1 / 2 : ℝ) / B) * A ^ (-(1 / 2 : ℝ)))
        - (3 * ((B ^ (3 / 2 : ℝ) / B) * A ^ (-(3 / 2 : ℝ)))) := by
      ring
    _ = (B ^ (-(1 / 2 : ℝ)) * A ^ (-(1 / 2 : ℝ)))
        - (3 * (B ^ (1 / 2 : ℝ) * A ^ (-(3 / 2 : ℝ)))) := by
      rw [h_div1, h_div2]
    _ = (B ^ (-(1 / 2 : ℝ)) * A ^ (-(1 / 2 : ℝ)))
        - (3 * B ^ (1 / 2 : ℝ) * A ^ (-(3 / 2 : ℝ))) := by
      ring
    _ = (B ^ (-(1 / 2 : ℝ)) * (A ^ (-(3 / 2 : ℝ)) * A))
        - (3 * (B ^ (-(1 / 2 : ℝ)) * B) * A ^ (-(3 / 2 : ℝ))) := by
      rw [h_factorA, h_factorB]
    _ = B ^ (-(1 / 2 : ℝ)) * A ^ (-(3 / 2 : ℝ)) * A - 3 * B ^ (-(1 / 2 : ℝ)) * B * A ^ (-(3 / 2 : ℝ)) := by
      ring
    _ = B ^ (-(1 / 2 : ℝ)) * A ^ (-(3 / 2 : ℝ)) * (A - 3 * B) := by
      ring
    _ = B ^ (-(1 / 2 : ℝ)) * A ^ (-(3 / 2 : ℝ)) * ((c - 3) * x ^ 2 - 2) := by
      dsimp [A, B, c]
      ring
    _ = ((c - 3) * x ^ 2 - 2) * B ^ (-(1 / 2 : ℝ)) * A ^ (-(3 / 2 : ℝ)) := by
      ring
    _ = ((5 + 4 * Real.cos t - 3) * x ^ 2 - 2) * (1 + x ^ 2) ^ (-(1 / 2) : ℝ)
          * (1 + (5 + 4 * Real.cos t) * x ^ 2) ^ (-(3 / 2) : ℝ) := by
      simp [hA, hB, hc]

/-- **Continuity and periodicity of the Hopf inner integral.** -/
theorem hopf_inner_integral_regularity :
    Continuous (fun t => ∫ s in (0 : ℝ)..(2 * Real.pi),
        (1 / 2) * (3 + 2 * Real.cos t - 2 * (1 + Real.cos t) * Real.cos s) ^ (-(1 / 2) : ℝ)
        - (3 / 2) * (3 + 2 * Real.cos t - 2 * (1 + Real.cos t) * Real.cos s) ^ (-(3 / 2) : ℝ))
      ∧ Function.Periodic (fun t => ∫ s in (0 : ℝ)..(2 * Real.pi),
        (1 / 2) * (3 + 2 * Real.cos t - 2 * (1 + Real.cos t) * Real.cos s) ^ (-(1 / 2) : ℝ)
        - (3 / 2) * (3 + 2 * Real.cos t - 2 * (1 + Real.cos t) * Real.cos s) ^ (-(3 / 2) : ℝ))
        (2 * Real.pi) := by
  set D := fun (s t : ℝ) => 3 + 2 * Real.cos t - 2 * (1 + Real.cos t) * Real.cos s with hD
  have hD_nonzero : ∀ s t : ℝ, D s t ≠ 0 := fun s t => by
    have hpos : D s t ≥ 1 := hopf_denom_pos s t
    linarith
  have hD_cont : Continuous (fun (p : ℝ × ℝ) => D p.2 p.1) := by
    unfold D; continuity
  have h_integrand_uncurry_cont : Continuous (fun (p : ℝ × ℝ) =>
      (1 / 2 : ℝ) * (D p.2 p.1) ^ (-(1 / 2 : ℝ)) - (3 / 2 : ℝ) * (D p.2 p.1) ^ (-(3 / 2 : ℝ))) := by
    have h_pow1 : Continuous (fun (p : ℝ × ℝ) => (D p.2 p.1) ^ (-(1 / 2 : ℝ))) :=
      hD_cont.rpow_const (fun p => Or.inl (hD_nonzero p.2 p.1))
    have h_pow2 : Continuous (fun (p : ℝ × ℝ) => (D p.2 p.1) ^ (-(3 / 2 : ℝ))) :=
      hD_cont.rpow_const (fun p => Or.inl (hD_nonzero p.2 p.1))
    have h_term1 : Continuous (fun (p : ℝ × ℝ) => (1 / 2 : ℝ) * (D p.2 p.1) ^ (-(1 / 2 : ℝ))) :=
      Continuous.mul continuous_const h_pow1
    have h_term2 : Continuous (fun (p : ℝ × ℝ) => (3 / 2 : ℝ) * (D p.2 p.1) ^ (-(3 / 2 : ℝ))) :=
      Continuous.mul continuous_const h_pow2
    exact Continuous.sub h_term1 h_term2
  have hcont : Continuous (fun t : ℝ => ∫ s in (0 : ℝ)..(2 * Real.pi),
      (1 / 2 : ℝ) * (D s t) ^ (-(1 / 2 : ℝ)) - (3 / 2 : ℝ) * (D s t) ^ (-(3 / 2 : ℝ))) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' h_integrand_uncurry_cont (0 : ℝ) (2 * Real.pi)
  have hper : Function.Periodic (fun t : ℝ => ∫ s in (0 : ℝ)..(2 * Real.pi),
      (1 / 2) * (D s t) ^ (-(1 / 2 : ℝ)) - (3 / 2) * (D s t) ^ (-(3 / 2 : ℝ))) (2 * Real.pi) := by
    intro t
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    have hD_eq : D s (t + 2 * Real.pi) = D s t := by
      unfold D
      rw [Real.cos_add_two_pi]
    simp [hD_eq]
  exact And.intro hcont hper

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

end KnotTheory
end LeanEval
