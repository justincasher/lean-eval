import LeanEval.KnotTheory.Linking.Basic

namespace LeanEval
namespace KnotTheory

/-!
# Ambient-isotopy invariance of the linking number

The deformed components and integrand, the divergence potentials, the pointwise
divergence identity, differentiation under the integral sign, and the
change-of-variables argument that together prove the Gauss linking number is an
ambient-isotopy invariant.
-/

open scoped RealInnerProductSpace

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
  -- Positive part: deformedDiff is nonzero because Φ.H r is injective (via inv_left)
  -- and the components are disjoint.
  have hpos : ∀ r s t, 0 < ‖deformedDiff Lk Φ r s t‖ := by
    intro r s t
    rw [norm_pos_iff]
    intro hzero
    have h_eq : Φ.H r (Lk.K.curve s) = Φ.H r (Lk.L.curve t) := sub_eq_zero.mp hzero
    have h_neq : Lk.K.curve s ≠ Lk.L.curve t := by
      intro h_eq_curves
      have : Lk.K.curve s - Lk.L.curve t = 0 := sub_eq_zero_of_eq h_eq_curves
      exact TwoLink.components_nonzero Lk s t this
    apply h_neq
    calc
      Lk.K.curve s = Φ.Hinv r (Φ.H r (Lk.K.curve s)) := by
        symm; exact Φ.inv_left r (Lk.K.curve s)
      _ = Φ.Hinv r (Φ.H r (Lk.L.curve t)) := by rw [h_eq]
      _ = Lk.L.curve t := Φ.inv_left r (Lk.L.curve t)
  -- Smooth part: deformedDiff is C∞ (deformedDiff_smooth gives the third conjunct),
  -- hence its norm is C∞ (via contDiffAt_norm at each point since it is nowhere zero),
  -- and then the p-th power is C∞ (via ContDiffAt.rpow).
  have h_smooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ × ℝ => deformedDiff Lk Φ p.1 p.2.1 p.2.2) :=
    (deformedDiff_smooth Lk Φ).2.2.1
  have h_norm_smooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ × ℝ => ‖deformedDiff Lk Φ q.1 q.2.1 q.2.2‖) := by
    refine (contDiff_iff_contDiffAt.mpr ?_)
    intro q
    have h_nonzero : deformedDiff Lk Φ q.1 q.2.1 q.2.2 ≠ 0 :=
      norm_pos_iff.mp (hpos q.1 q.2.1 q.2.2)
    have h_diff_at : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun q' : ℝ × ℝ × ℝ => deformedDiff Lk Φ q'.1 q'.2.1 q'.2.2) q :=
      (contDiff_iff_contDiffAt.mp h_smooth) q
    have h_norm_at : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun y => ‖(fun q' : ℝ × ℝ × ℝ => deformedDiff Lk Φ q'.1 q'.2.1 q'.2.2) y‖) q :=
      (contDiffAt_norm (𝕜 := ℝ) h_nonzero).comp q h_diff_at
    simpa using h_norm_at
  have h_rpow_smooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ × ℝ => ‖deformedDiff Lk Φ q.1 q.2.1 q.2.2‖ ^ p) := by
    refine (contDiff_iff_contDiffAt.mpr ?_)
    intro q
    have h_nz : ‖deformedDiff Lk Φ q.1 q.2.1 q.2.2‖ ≠ 0 := by
      linarith [hpos q.1 q.2.1 q.2.2]
    have h_norm_at : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun q' : ℝ × ℝ × ℝ => ‖deformedDiff Lk Φ q'.1 q'.2.1 q'.2.2‖) q :=
      (contDiff_iff_contDiffAt.mp h_norm_smooth) q
    exact h_norm_at.rpow (contDiffAt_const (c := p) (x := q)) h_nz
  exact ⟨h_rpow_smooth, hpos⟩

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
  refine ⟨?_, ?_⟩
  · exact deriv_const t (deriv (fun s => Φ.H r (Lk.K.curve s)) s)
  · exact deriv_const s (deriv (fun t => Φ.H r (Lk.L.curve t)) t)

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
  -- key abbreviations
  set u := fun r' => deformedDiff Lk Φ r' s t with hu_def
  set da := fun r' => deriv (fun s' => Φ.H r' (Lk.K.curve s')) s with hda_def
  set db := fun r' => deriv (fun t' => Φ.H r' (Lk.L.curve t')) t with hdb_def
  -- derivative values
  set ū := deriv (fun r' => Φ.H r' (Lk.K.curve s)) r - deriv (fun r' => Φ.H r' (Lk.L.curve t)) r with hū_def
  set da_s := deriv (fun s' => deriv (fun r' => Φ.H r' (Lk.K.curve s')) r) s with hda_s_def
  set db_t := deriv (fun t' => deriv (fun r' => Φ.H r' (Lk.L.curve t')) r) t with hdb_t_def
  -- positivity of denominator
  have hpos_u : 0 < ‖u r‖ := (deformedDenom_smooth_pos Lk Φ 3).2 r s t
  have h_ne_zero : u r ≠ 0 := norm_pos_iff.mp hpos_u
  -- smoothness of u, da, db in r (via deformedDiff_smooth)
  have h_smooth := deformedDiff_smooth Lk Φ
  rcases h_smooth with ⟨_, _, hu_contDiff_raw, hda_contDiff_raw, hdb_contDiff_raw⟩
  have h_map : ContDiff ℝ (⊤ : ℕ∞) (fun (r' : ℝ) => (r', s, t)) :=
    (contDiff_id : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => x)).prodMk
      ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => s)).prodMk
        (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => t)))
  have hu_contDiff : ContDiff ℝ (⊤ : ℕ∞) u := hu_contDiff_raw.comp h_map
  have hda_contDiff : ContDiff ℝ (⊤ : ℕ∞) da := hda_contDiff_raw.comp h_map
  have hdb_contDiff : ContDiff ℝ (⊤ : ℕ∞) db := hdb_contDiff_raw.comp h_map
  -- differentiability at r via ContDiffAt
  have hu_diff : DifferentiableAt ℝ u r :=
    (hu_contDiff.contDiffAt (x := r)).differentiableAt (by decide)
  have hda_diff : DifferentiableAt ℝ da r :=
    (hda_contDiff.contDiffAt (x := r)).differentiableAt (by decide)
  have hdb_diff : DifferentiableAt ℝ db r :=
    (hdb_contDiff.contDiffAt (x := r)).differentiableAt (by decide)
  -- HasDerivAt from deriv + differentiability
  have hu_hasDeriv : HasDerivAt u (deriv u r) r := hu_diff.hasDerivAt
  have hda_hasDeriv : HasDerivAt da (deriv da r) r := hda_diff.hasDerivAt
  have hdb_hasDeriv : HasDerivAt db (deriv db r) r := hdb_diff.hasDerivAt
  -- rewrite derivatives via deformedU_partials and mixed_partials_symm
  have h_deriv_u : deriv u r = ū := by
    simpa [u, ū] using (deformedU_partials Lk Φ r s t).1
  have h_mixed : deriv (fun r => deriv (fun s => Φ.H r (Lk.K.curve s)) s) r
      = deriv (fun s => deriv (fun r => Φ.H r (Lk.K.curve s)) r) s
    ∧ deriv (fun r => deriv (fun t => Φ.H r (Lk.L.curve t)) t) r
      = deriv (fun t => deriv (fun r => Φ.H r (Lk.L.curve t)) r) t :=
    mixed_partials_symm Lk Φ r s t
  have h_deriv_da : deriv da r = da_s := by
    calc
      deriv da r = deriv (fun r' => deriv (fun s' => Φ.H r' (Lk.K.curve s')) s) r := rfl
      _ = deriv (fun s' => deriv (fun r' => Φ.H r' (Lk.K.curve s')) r) s := h_mixed.1
      _ = da_s := rfl
  have h_deriv_db : deriv db r = db_t := by
    calc
      deriv db r = deriv (fun r' => deriv (fun t' => Φ.H r' (Lk.L.curve t')) t) r := rfl
      _ = deriv (fun t' => deriv (fun r' => Φ.H r' (Lk.L.curve t')) r) t := h_mixed.2
      _ = db_t := rfl
  -- HasDerivAt with the right derivative values
  have hu_hasDeriv' : HasDerivAt u ū r := by
    rw [h_deriv_u] at hu_hasDeriv
    exact hu_hasDeriv
  have hda_hasDeriv' : HasDerivAt da da_s r := by
    rw [h_deriv_da] at hda_hasDeriv
    exact hda_hasDeriv
  have hdb_hasDeriv' : HasDerivAt db db_t r := by
    rw [h_deriv_db] at hdb_hasDeriv
    exact hdb_hasDeriv
  -- HasDerivAt for the triple product numerator
  have h_num_hasDeriv : HasDerivAt (fun r' => tripleProduct (u r') (da r') (db r'))
      (tripleProduct ū (da r) (db r) + tripleProduct (u r) da_s (db r)
        + tripleProduct (u r) (da r) db_t) r :=
    tripleProduct_deriv hu_hasDeriv' hda_hasDeriv' hdb_hasDeriv'
  -- HasDerivAt for the denominator factor (‖u‖³)⁻¹
  have h_den_hasDeriv : HasDerivAt (fun r' => (‖u r'‖ ^ 3)⁻¹)
      (-3 * (‖u r‖ ^ 5)⁻¹ * ⟪u r, ū⟫) r :=
    recip_norm_cube_deriv hu_hasDeriv' h_ne_zero
  -- Product rule: deformedIntegrand = tripleProduct(u, da, db) * (‖u‖³)⁻¹
  have h_eq : (fun r' : ℝ => deformedIntegrand Lk Φ r' s t)
      = (fun r' : ℝ => tripleProduct (u r') (da r') (db r') * (‖u r'‖ ^ 3)⁻¹) := by
    ext r'
    unfold deformedIntegrand linkingIntegrand
    simp [u, da, db, div_eq_mul_inv]
  have h_prod_hasDeriv : HasDerivAt (fun r' => deformedIntegrand Lk Φ r' s t)
      ((tripleProduct ū (da r) (db r) + tripleProduct (u r) da_s (db r)
          + tripleProduct (u r) (da r) db_t) * (‖u r‖ ^ 3)⁻¹
        + tripleProduct (u r) (da r) (db r) * (-3 * (‖u r‖ ^ 5)⁻¹ * ⟪u r, ū⟫)) r := by
    rw [h_eq]
    exact HasDerivAt.mul h_num_hasDeriv h_den_hasDeriv
  -- Convert HasDerivAt to deriv
  have h_deriv : deriv (fun r' => deformedIntegrand Lk Φ r' s t) r
      = (tripleProduct ū (da r) (db r) + tripleProduct (u r) da_s (db r)
          + tripleProduct (u r) (da r) db_t) * (‖u r‖ ^ 3)⁻¹
        + tripleProduct (u r) (da r) (db r) * (-3 * (‖u r‖ ^ 5)⁻¹ * ⟪u r, ū⟫) :=
    h_prod_hasDeriv.deriv
  -- simplify second term and expand abbreviations
  have h_simplify : (tripleProduct ū (da r) (db r) + tripleProduct (u r) da_s (db r)
        + tripleProduct (u r) (da r) db_t) * (‖u r‖ ^ 3)⁻¹
      + tripleProduct (u r) (da r) (db r) * (-3 * (‖u r‖ ^ 5)⁻¹ * ⟪u r, ū⟫)
      = (tripleProduct ū (da r) (db r) + tripleProduct (u r) da_s (db r)
          + tripleProduct (u r) (da r) db_t) * (‖u r‖ ^ 3)⁻¹
        - 3 * tripleProduct (u r) (da r) (db r) * ⟪u r, ū⟫ * (‖u r‖ ^ 5)⁻¹ := by ring
  have h_deriv' : deriv (fun r' => deformedIntegrand Lk Φ r' s t) r
      = (tripleProduct ū (da r) (db r) + tripleProduct (u r) da_s (db r)
          + tripleProduct (u r) (da r) db_t) * (‖u r‖ ^ 3)⁻¹
        - 3 * tripleProduct (u r) (da r) (db r) * ⟪u r, ū⟫ * (‖u r‖ ^ 5)⁻¹ :=
    h_deriv.trans h_simplify
  -- expand abbreviations to match the target statement
  simpa [u, da, db, ū, da_s, db_t, hu_def, hda_def, hdb_def, hū_def, hda_s_def, hdb_t_def] using h_deriv'

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

end KnotTheory
end LeanEval
