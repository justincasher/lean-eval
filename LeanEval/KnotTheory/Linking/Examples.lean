import LeanEval.KnotTheory.Linking.Basic

namespace LeanEval
namespace KnotTheory

/-!
# The unlink and the Hopf link

Round coordinate circles and the two distinguished two-component links: the
unlink (two parallel circles) and the Hopf link.
-/

open scoped RealInnerProductSpace

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

end KnotTheory
end LeanEval
