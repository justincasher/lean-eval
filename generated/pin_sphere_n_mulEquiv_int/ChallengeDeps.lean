import Mathlib

/-!
# The fundamental group of the circle is `ℤ`

This file contains the blueprint formalization for `π₁(S¹) ≅ ℤ`, computed via the winding number
arising from the covering map `Circle.exp : ℝ → Circle`.

The headline statement `π₁(S¹, 1) ≃* Multiplicative ℤ` is `LeanEval.Topology.pi1_circle_mulEquiv_int`
in `LeanEval.Topology.HomotopyGroups`; the declarations here build the winding-number isomorphism
with the fundamental group used to prove it.

All declarations below are fully proved.
-/

namespace LeanEval
namespace Topology

open Path

noncomputable section

/-- Membership in the fibre of `Circle.exp` over `1` is exactly the kernel condition. -/
theorem mem_exp_preimage_one {r : ℝ} : r ∈ Circle.exp ⁻¹' {1} ↔ Circle.exp r = 1 := Iff.rfl

/-- The chosen lift `⟨0⟩` of the basepoint, valid since `Circle.exp 0 = 1`. -/
def fiberBasePt : ↥(Circle.exp ⁻¹' {1}) := ⟨0, mem_exp_preimage_one.mpr Circle.exp_zero⟩

/-- **Cancelling the period.** For integers `n, m`, if `n · 2π = m · 2π` then `n = m`. -/
theorem two_pi_cancel {n m : ℤ}
    (h : (n : ℝ) * (2 * Real.pi) = (m : ℝ) * (2 * Real.pi)) : n = m := by
  have hpi₀ : (2 * Real.pi) ≠ 0 := by
    linarith [Real.two_pi_pos]
  have hnm : (n : ℝ) = (m : ℝ) := mul_right_cancel₀ hpi₀ h
  exact Int.cast_injective hnm

/-- **Integer parametrization of the fibre.** The fibre `Circle.exp ⁻¹' {1}` is in bijection with
`ℤ` via `⟨r⟩ ↦ n` where `r = n · 2π`; the inverse is `n ↦ ⟨n · 2π⟩`. -/
def fiberEquivInt : ↥(Circle.exp ⁻¹' {1}) ≃ ℤ :=
  { toFun := λ x =>
      Classical.choose (Circle.exp_eq_one.mp x.property)
    invFun := λ n => ⟨(n : ℝ) * (2 * Real.pi), mem_exp_preimage_one.mpr (Circle.exp_int_mul_two_pi n)⟩
    left_inv := by
      intro x
      have hx' : ∃ n : ℤ, x.val = (n : ℝ) * (2 * Real.pi) := Circle.exp_eq_one.mp x.property
      let n := Classical.choose hx'
      have hn : x.val = (n : ℝ) * (2 * Real.pi) := Classical.choose_spec hx'
      ext; exact hn.symm
    right_inv := by
      intro n
      have hr' : ∃ m : ℤ, (n : ℝ) * (2 * Real.pi) = (m : ℝ) * (2 * Real.pi) :=
        Circle.exp_eq_one.mp (Circle.exp_int_mul_two_pi n)
      let m := Classical.choose hr'
      have hm : (n : ℝ) * (2 * Real.pi) = (m : ℝ) * (2 * Real.pi) := Classical.choose_spec hr'
      exact (two_pi_cancel hm).symm
  }

/-- **Fibre parametrization on integers.** The fibre point assigned to `n` has underlying real
number `n · 2π`. -/
theorem fiberEquivInt_symm_apply (n : ℤ) :
    (fiberEquivInt.symm n : ℝ) = n * (2 * Real.pi) := by
  rfl

/-- **The translated lift is the lift.** For a loop `γ₀` based at `1`, `a` with `exp a = 1`, and a
fibre point `e`, the lift of `γ₀` from `e` translated by `a` is the lift of `γ₀` from `e + a`. -/
theorem translatedLift_eq_liftPath
    (γ₀ : Path (1 : Circle) 1) {a : ℝ} (ha : Circle.exp a = 1)
    {e : ℝ} (he : Circle.exp e = 1) :
    (fun t => Circle.isCoveringMap_exp.liftPath γ₀ e (γ₀.source.trans he.symm) t + a)
      = ⇑(Circle.isCoveringMap_exp.liftPath γ₀ (e + a)
          (γ₀.source.trans
            (show (1 : Circle) = Circle.exp (e + a) by rw [Circle.exp_add, he, ha, one_mul]))) := by
  -- h₁ : γ₀ 0 = Circle.exp e, a proof that e lives in the fibre over γ₀(0)
  have h₁ : γ₀ 0 = Circle.exp e := γ₀.source.trans he.symm
  -- h₂ : γ₀ 0 = Circle.exp (e + a), a proof that e + a lives in the same fibre
  have h₂ : γ₀ 0 = Circle.exp (e + a) := γ₀.source.trans (by
    rw [Circle.exp_add, he, ha, one_mul])
  -- the translated map
  set Γ := fun t => Circle.isCoveringMap_exp.liftPath γ₀ e h₁ t + a with hΓ
  have hΓ_cont : Continuous Γ := by
    unfold Γ
    refine Continuous.add ?_ continuous_const
    exact (Circle.isCoveringMap_exp.liftPath γ₀ e h₁).continuous
  have hΓ_comp : Circle.exp ∘ Γ = γ₀ := by
    have hlifts : Circle.exp ∘ (Circle.isCoveringMap_exp.liftPath γ₀ e h₁) = γ₀ :=
      Circle.isCoveringMap_exp.liftPath_lifts γ₀ e h₁
    funext t
    calc
      (Circle.exp ∘ Γ) t = Circle.exp (Γ t) := rfl
      _ = Circle.exp (Circle.isCoveringMap_exp.liftPath γ₀ e h₁ t + a) := rfl
      _ = Circle.exp (Circle.isCoveringMap_exp.liftPath γ₀ e h₁ t) * Circle.exp a := by
        rw [Circle.exp_add]
      _ = Circle.exp (Circle.isCoveringMap_exp.liftPath γ₀ e h₁ t) * 1 := by rw [ha]
      _ = Circle.exp (Circle.isCoveringMap_exp.liftPath γ₀ e h₁ t) := by simp
      _ = γ₀ t := by
        simpa using congrArg (fun f => f t) hlifts
  have hΓ_zero : Γ 0 = e + a := by
    unfold Γ
    simp [Circle.isCoveringMap_exp.liftPath_zero γ₀ e h₁]
  -- by the unique characterization of lifted paths, Γ = liftPath γ₀ (e + a) h₂
  exact (Circle.isCoveringMap_exp.eq_liftPath_iff (γ := γ₀) (e := e + a) (γ_0 := h₂)).mpr
    ⟨hΓ_cont, hΓ_comp, hΓ_zero⟩

/-- **Translation invariance of monodromy.** For a class `γ`, `a` with `exp a = 1`, and a fibre
point `e`, monodromy at `e + a` is monodromy at `e` shifted by `a`. -/
theorem monodromy_translation (γ : FundamentalGroup Circle 1)
    {a : ℝ} (ha : Circle.exp a = 1) (e : ↥(Circle.exp⁻¹' {1})) :
    (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath γ)
        ⟨e.val + a, mem_exp_preimage_one.mpr
          (by rw [Circle.exp_add, mem_exp_preimage_one.mp e.2, ha, one_mul])⟩).val
      = (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath γ) e).val + a := by
  refine Quotient.inductionOn (FundamentalGroup.toPath γ) ?_
  intro γ₀
  have he : Circle.exp e.val = 1 := mem_exp_preimage_one.mp e.2
  have hea_symm : (1 : Circle) = Circle.exp (e.val + a) := by
    rw [Circle.exp_add, he, ha, one_mul]
  have htrans : (fun t => Circle.isCoveringMap_exp.liftPath γ₀ e.val (γ₀.source.trans he.symm) t + a) =
      Circle.isCoveringMap_exp.liftPath γ₀ (e.val + a) (γ₀.source.trans hea_symm) :=
    translatedLift_eq_liftPath γ₀ ha he
  have h_at_1 : (Circle.isCoveringMap_exp.liftPath γ₀ e.val (γ₀.source.trans he.symm)) 1 + a =
      (Circle.isCoveringMap_exp.liftPath γ₀ (e.val + a) (γ₀.source.trans hea_symm)) 1 := by
    calc
      (Circle.isCoveringMap_exp.liftPath γ₀ e.val (γ₀.source.trans he.symm)) 1 + a
          = ((fun t => Circle.isCoveringMap_exp.liftPath γ₀ e.val (γ₀.source.trans he.symm) t + a) 1) := by
            simp
      _ = (Circle.isCoveringMap_exp.liftPath γ₀ (e.val + a) (γ₀.source.trans hea_symm)) 1 := by
        rw [htrans]
  have hmon_e_add : (Circle.isCoveringMap_exp.monodromy (⟦γ₀⟧ : Path.Homotopic.Quotient (1 : Circle) 1)
        ⟨e.val + a, mem_exp_preimage_one.mpr (by rw [Circle.exp_add, he, ha, one_mul])⟩).val
      = (Circle.isCoveringMap_exp.liftPath γ₀ (e.val + a) (γ₀.source.trans hea_symm)) 1 := by
    dsimp [IsCoveringMap.monodromy]
    let f : Path (1 : Circle) 1 → ↥(Circle.exp⁻¹' {1}) := fun γ' =>
      ⟨Circle.isCoveringMap_exp.liftPath γ' (e.val + a) (γ'.source.trans hea_symm) 1,
        (congr_fun (Circle.isCoveringMap_exp.liftPath_lifts γ' (e.val + a) (γ'.source.trans hea_symm)) 1).trans γ'.target⟩
    have h_lift : Quotient.lift f (fun γ₁ γ₂ h => Subtype.ext
        (Circle.isCoveringMap_exp.liftPath_apply_one_eq_of_homotopicRel h (e.val + a) (γ₁.source.trans hea_symm) (γ₂.source.trans hea_symm))) (⟦γ₀⟧) = f γ₀ :=
      Quotient.lift_mk (s := Homotopic.setoid (1 : Circle) 1) f (fun γ₁ γ₂ h => Subtype.ext
        (Circle.isCoveringMap_exp.liftPath_apply_one_eq_of_homotopicRel h (e.val + a) (γ₁.source.trans hea_symm) (γ₂.source.trans hea_symm))) γ₀
    calc
      Subtype.val (Quotient.lift f (fun γ₁ γ₂ h => Subtype.ext
          (Circle.isCoveringMap_exp.liftPath_apply_one_eq_of_homotopicRel h (e.val + a) (γ₁.source.trans hea_symm) (γ₂.source.trans hea_symm))) (⟦γ₀⟧))
          = Subtype.val (f γ₀) := by rw [h_lift]
      _ = (Circle.isCoveringMap_exp.liftPath γ₀ (e.val + a) (γ₀.source.trans hea_symm)) 1 := rfl
  have hmon_e : (Circle.isCoveringMap_exp.monodromy (⟦γ₀⟧ : Path.Homotopic.Quotient (1 : Circle) 1) e).val
      = (Circle.isCoveringMap_exp.liftPath γ₀ e.val (γ₀.source.trans he.symm)) 1 := by
    dsimp [IsCoveringMap.monodromy]
    let f : Path (1 : Circle) 1 → ↥(Circle.exp⁻¹' {1}) := fun γ' =>
      ⟨Circle.isCoveringMap_exp.liftPath γ' e.val (γ'.source.trans e.2.symm) 1,
        (congr_fun (Circle.isCoveringMap_exp.liftPath_lifts γ' e.val (γ'.source.trans e.2.symm)) 1).trans γ'.target⟩
    have h_lift : Quotient.lift f (fun γ₁ γ₂ h => Subtype.ext
        (Circle.isCoveringMap_exp.liftPath_apply_one_eq_of_homotopicRel h e.val (γ₁.source.trans e.2.symm) (γ₂.source.trans e.2.symm))) (⟦γ₀⟧) = f γ₀ :=
      Quotient.lift_mk (s := Homotopic.setoid (1 : Circle) 1) f (fun γ₁ γ₂ h => Subtype.ext
        (Circle.isCoveringMap_exp.liftPath_apply_one_eq_of_homotopicRel h e.val (γ₁.source.trans e.2.symm) (γ₂.source.trans e.2.symm))) γ₀
    calc
      Subtype.val (Quotient.lift f (fun γ₁ γ₂ h => Subtype.ext
          (Circle.isCoveringMap_exp.liftPath_apply_one_eq_of_homotopicRel h e.val (γ₁.source.trans e.2.symm) (γ₂.source.trans e.2.symm))) (⟦γ₀⟧))
          = Subtype.val (f γ₀) := by rw [h_lift]
      _ = (Circle.isCoveringMap_exp.liftPath γ₀ e.val (γ₀.source.trans he.symm)) 1 := rfl
  calc
    (Circle.isCoveringMap_exp.monodromy (⟦γ₀⟧ : Path.Homotopic.Quotient (1 : Circle) 1)
        ⟨e.val + a, mem_exp_preimage_one.mpr (by rw [Circle.exp_add, he, ha, one_mul])⟩).val
        = (Circle.isCoveringMap_exp.liftPath γ₀ (e.val + a) (γ₀.source.trans hea_symm)) 1 := hmon_e_add
    _ = (Circle.isCoveringMap_exp.liftPath γ₀ e.val (γ₀.source.trans he.symm)) 1 + a := by
      symm; exact h_at_1
    _ = (Circle.isCoveringMap_exp.monodromy (⟦γ₀⟧ : Path.Homotopic.Quotient (1 : Circle) 1) e).val + a := by
      rw [hmon_e]

/-- **Monodromy on a fibre point, in real coordinates.** For a class `γ` and any fibre point `e`,
the monodromy value at `e` is the value at `⟨0⟩` shifted by `(e : ℝ)`. -/
theorem monodromy_val_of_fibre (γ : FundamentalGroup Circle 1) (e : ↥(Circle.exp ⁻¹' {1})) :
    (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath γ) e).val
      = (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath γ) fiberBasePt).val
          + (e : ℝ) := by
  have hfib : Circle.exp (e : ℝ) = 1 := mem_exp_preimage_one.mp e.2
  have h_e_eq : e = ⟨fiberBasePt.val + (e : ℝ),
    mem_exp_preimage_one.mpr (by
      calc
        Circle.exp (fiberBasePt.val + (e : ℝ)) = Circle.exp (fiberBasePt.val : ℝ) * Circle.exp (e : ℝ) := by
          rw [Circle.exp_add]
        _ = 1 * Circle.exp (e : ℝ) := by simp [fiberBasePt]
        _ = Circle.exp (e : ℝ) := by simp
        _ = 1 := hfib)⟩ := by
    ext; simp [fiberBasePt]
  calc
    (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath γ) e).val
        = (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath γ)
            (⟨fiberBasePt.val + (e : ℝ), _⟩ : ↥(Circle.exp ⁻¹' {1}))).val := by
      simpa using congrArg (fun x : ↥(Circle.exp ⁻¹' {1}) =>
        (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath γ) x).val) h_e_eq
    _ = (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath γ) fiberBasePt).val + (e : ℝ) :=
      monodromy_translation γ hfib fiberBasePt

/-- **Winding number.** The integer assigned by `fiberEquivInt` to the monodromy of `γ` at the
basepoint lift `⟨0⟩`. -/
def wind (γ : FundamentalGroup Circle 1) : ℤ :=
  fiberEquivInt (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath γ) fiberBasePt)

/-- **Winding number specification.** The underlying real number of the monodromy of `γ` at `⟨0⟩`
equals `w(γ) · 2π`. -/
theorem wind_spec (γ : FundamentalGroup Circle 1) :
    (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath γ) fiberBasePt).val
      = wind γ * (2 * Real.pi) := by
  let m := Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath γ) fiberBasePt
  have hm : m = fiberEquivInt.symm (wind γ) := by
    calc
      m = fiberEquivInt.symm (fiberEquivInt m) := (Equiv.symm_apply_apply fiberEquivInt m).symm
      _ = fiberEquivInt.symm (wind γ) := rfl
  calc
    m.val = (fiberEquivInt.symm (wind γ)).val := by rw [hm]
    _ = wind γ * (2 * Real.pi) := by rw [fiberEquivInt_symm_apply]

/-- **Group law as path concatenation.** `toPath (γ * δ) = (toPath δ).trans (toPath γ)`. -/
theorem toPath_mul (γ δ : FundamentalGroup Circle 1) :
    FundamentalGroup.toPath (γ * δ)
      = (FundamentalGroup.toPath δ).trans (FundamentalGroup.toPath γ) := by
  rfl

/-- **Additivity of winding in real coordinates.** -/
theorem wind_mul_real (γ δ : FundamentalGroup Circle 1) :
    wind (γ * δ) * (2 * Real.pi) = wind γ * (2 * Real.pi) + wind δ * (2 * Real.pi) := by
  calc
    wind (γ * δ) * (2 * Real.pi) = (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath (γ * δ)) fiberBasePt).val := by
      rw [wind_spec]
    _ = (Circle.isCoveringMap_exp.monodromy ((FundamentalGroup.toPath δ).trans (FundamentalGroup.toPath γ)) fiberBasePt).val := by
      rw [toPath_mul]
    _ = (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath γ) (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath δ) fiberBasePt)).val := by
      rw [Circle.isCoveringMap_exp.monodromy_trans_apply]
    _ = (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath γ) fiberBasePt).val + (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath δ) fiberBasePt : ℝ) := by
      rw [monodromy_val_of_fibre]
    _ = wind γ * (2 * Real.pi) + wind δ * (2 * Real.pi) := by
      rw [wind_spec γ, wind_spec δ]

/-- **Winding number is additive.** `w(γ · δ) = w(γ) + w(δ)`. -/
theorem wind_mul (γ δ : FundamentalGroup Circle 1) :
    wind (γ * δ) = wind γ + wind δ := by
  apply two_pi_cancel
  calc
    (wind (γ * δ) : ℝ) * (2 * Real.pi) = wind (γ * δ) * (2 * Real.pi) := rfl
    _ = wind γ * (2 * Real.pi) + wind δ * (2 * Real.pi) := wind_mul_real γ δ
    _ = ((wind γ : ℝ) + (wind δ : ℝ)) * (2 * Real.pi) := by ring
    _ = ((wind γ + wind δ : ℤ) : ℝ) * (2 * Real.pi) := by simp

/-- **Path classes in `ℝ` are unique.** For any `c`, homotopy classes of paths `0 → c` in `ℝ`
form a subsingleton. -/
theorem quotient_subsingleton (c : ℝ) :
    Subsingleton (Path.Homotopic.Quotient (0 : ℝ) c) := by
  infer_instance

/-- The homotopy class in `ℝ` of the lift of `toPath γ` starting at `0`. -/
def liftClass (γ : FundamentalGroup Circle 1) :
    Path.Homotopic.Quotient (0 : ℝ)
      (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath γ) fiberBasePt).val :=
  let p0 := (FundamentalGroup.toPath γ).out
  let γ_0 := p0.source.trans fiberBasePt.2.symm
  let lp := Circle.isCoveringMap_exp.liftPath p0 fiberBasePt γ_0
  have h_source : lp 0 = (0 : ℝ) := by
    simpa [lp, fiberBasePt] using Circle.isCoveringMap_exp.liftPath_zero p0 fiberBasePt γ_0
  have h_target : lp 1 = (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath γ) fiberBasePt).val := by
    have h_mk : Path.Homotopic.Quotient.mk p0 = FundamentalGroup.toPath γ := Quotient.out_eq _
    calc
      lp 1 = (Circle.isCoveringMap_exp.monodromy (Path.Homotopic.Quotient.mk p0) fiberBasePt).val := rfl
      _ = (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath γ) fiberBasePt).val := by rw [h_mk]
  Path.Homotopic.Quotient.mk
    { toFun := lp
      continuous_toFun := lp.continuous
      source' := h_source
      target' := h_target }

/-- **Pushing the lift class forward recovers the loop.** The image of `liftClass γ` under the map
induced by `Circle.exp` (cast to a class of loops at `1`) equals `toPath γ`. -/
theorem map_liftClass (γ : FundamentalGroup Circle 1) :
    ((liftClass γ).map Circle.exp).cast Circle.exp_zero.symm
        (mem_exp_preimage_one.mp
          (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath γ) fiberBasePt).2).symm
      = FundamentalGroup.toPath γ := by
  let p0 := (FundamentalGroup.toPath γ).out
  have h_mk_p0 : Path.Homotopic.Quotient.mk p0 = FundamentalGroup.toPath γ := Quotient.out_eq _
  let γ_0 := p0.source.trans fiberBasePt.2.symm
  let lp := Circle.isCoveringMap_exp.liftPath p0 fiberBasePt γ_0
  have h_lp_lifts : Circle.exp ∘ (⇑lp : ↑unitInterval → ℝ) = ⇑p0 :=
    IsCoveringMap.liftPath_lifts Circle.isCoveringMap_exp p0 fiberBasePt γ_0
  have h_source : lp 0 = (0 : ℝ) := by
    simpa [lp, fiberBasePt] using Circle.isCoveringMap_exp.liftPath_zero p0 fiberBasePt γ_0
  have h_target : lp 1 = (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath γ) fiberBasePt).val := by
    calc
      lp 1 = (Circle.isCoveringMap_exp.monodromy (Path.Homotopic.Quotient.mk p0) fiberBasePt).val := rfl
      _ = (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath γ) fiberBasePt).val := by rw [h_mk_p0]
  let L : Path (0 : ℝ) (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath γ) fiberBasePt).val :=
    { toFun := lp
      continuous_toFun := lp.continuous
      source' := h_source
      target' := h_target }
  have hL_eq : liftClass γ = Path.Homotopic.Quotient.mk L := rfl
  have h_path_eq : (L.map Circle.exp.continuous).cast Circle.exp_zero.symm
      (mem_exp_preimage_one.mp (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath γ) fiberBasePt).2).symm = p0 := by
    apply Path.ext
    funext t
    have h_left : ((L.map Circle.exp.continuous).cast Circle.exp_zero.symm
      (mem_exp_preimage_one.mp (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath γ) fiberBasePt).2).symm) t
        = (L.map Circle.exp.continuous) t := by simp
    have h_mid : (L.map Circle.exp.continuous) t = Circle.exp (L t) := rfl
    have h_mid2 : Circle.exp (L t) = Circle.exp (lp t) := rfl
    have h_right : Circle.exp (lp t) = p0 t := by
      have h := congrArg (fun (f : ↑unitInterval → Circle) => f t) h_lp_lifts
      simpa using h
    calc
      ((L.map Circle.exp.continuous).cast Circle.exp_zero.symm
        (mem_exp_preimage_one.mp (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath γ) fiberBasePt).2).symm) t
          = (L.map Circle.exp.continuous) t := h_left
      _ = Circle.exp (L t) := h_mid
      _ = Circle.exp (lp t) := h_mid2
      _ = p0 t := h_right
  calc
    ((liftClass γ).map Circle.exp).cast Circle.exp_zero.symm
        (mem_exp_preimage_one.mp
          (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath γ) fiberBasePt).2).symm
        = ((Path.Homotopic.Quotient.mk L).map Circle.exp).cast Circle.exp_zero.symm
            (mem_exp_preimage_one.mp
              (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath γ) fiberBasePt).2).symm := by
      rw [hL_eq]
    _ = (Path.Homotopic.Quotient.mk (L.map Circle.exp.continuous)).cast Circle.exp_zero.symm
          (mem_exp_preimage_one.mp
            (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath γ) fiberBasePt).2).symm := by
      rw [Path.Homotopic.Quotient.mk_map]
    _ = Path.Homotopic.Quotient.mk ((L.map Circle.exp.continuous).cast Circle.exp_zero.symm
          (mem_exp_preimage_one.mp
            (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath γ) fiberBasePt).2).symm) := by
      rw [Path.Homotopic.Quotient.mk_cast]
    _ = Path.Homotopic.Quotient.mk p0 := by rw [h_path_eq]
    _ = FundamentalGroup.toPath γ := h_mk_p0

/-- Monodromy's underlying value is invariant under retyping the path-class endpoints
(`Path.Homotopic.Quotient.cast`) and replacing the fibre basepoint by one with the same
underlying real value. -/
theorem monodromy_cast_val {x y x' y' : Circle}
    (γ : Path.Homotopic.Quotient x y) (hx : x' = x) (hy : y' = y)
    (e : ↥(Circle.exp ⁻¹' {x'})) (e₂ : ↥(Circle.exp ⁻¹' {x}))
    (he : (e : ℝ) = (e₂ : ℝ)) :
    (Circle.isCoveringMap_exp.monodromy (γ.cast hx hy) e).val
      = (Circle.isCoveringMap_exp.monodromy γ e₂).val := by
  induction γ using Quotient.inductionOn with
  | h P =>
    obtain ⟨ev, ep⟩ := e
    obtain ⟨e2v, e2p⟩ := e₂
    have he' : ev = e2v := he
    subst he'
    rfl

/-- **Winding number is injective.** -/
theorem wind_injective : Function.Injective wind := by
  have toPath_inj : ∀ a b : FundamentalGroup Circle 1,
      FundamentalGroup.toPath a = FundamentalGroup.toPath b → a = b := by
    intro a b hab
    calc a = FundamentalGroup.fromPath (FundamentalGroup.toPath a) := rfl
      _ = FundamentalGroup.fromPath (FundamentalGroup.toPath b) := by rw [hab]
      _ = b := rfl
  intro γ δ h
  apply toPath_inj
  have he : (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath δ) fiberBasePt).val
      = (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath γ) fiberBasePt).val := by
    rw [wind_spec δ, wind_spec γ, h]
  have hlc : (liftClass δ).cast rfl he.symm = liftClass γ := Subsingleton.elim _ _
  rw [← map_liftClass γ, ← map_liftClass δ, ← hlc]
  generalize liftClass δ = q
  induction q using Quotient.inductionOn with
  | h P => rfl

/-- **Lift class projects to its loop class.** For a path `L : Path 0 c` with `exp c = 1`,
`toPath (fromPath ⟦exp ∘ L⟧) = ⟦exp ∘ L⟧`. -/
theorem toPath_fromPath_exp {c : ℝ} (L : Path (0 : ℝ) c) (hc : Circle.exp c = 1) :
    FundamentalGroup.toPath (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk
          ((L.map Circle.exp.continuous).cast Circle.exp_zero.symm hc.symm)))
      = Path.Homotopic.Quotient.mk
          ((L.map Circle.exp.continuous).cast Circle.exp_zero.symm hc.symm) := by
  rfl

/-- **Monodromy of an exponential loop class.** For `L : Path 0 c`, the monodromy of the class of
`exp ∘ L` at `⟨0⟩` is `⟨c⟩`. -/
theorem monodromy_exp_comp {c : ℝ} (L : Path (0 : ℝ) c) :
    Circle.isCoveringMap_exp.monodromy ((Path.Homotopic.Quotient.mk L).map Circle.exp) ⟨0, rfl⟩
      = ⟨c, rfl⟩ := by
  let exp' : C(ℝ, Circle) :=
    ⟨Circle.exp, Circle.isCoveringMap_exp.continuous⟩
  have hexp : exp' = Circle.exp := by
    ext
    rfl
  have h := Circle.isCoveringMap_exp.monodromy_map
    (γ := Path.Homotopic.Quotient.mk L)
  change Circle.isCoveringMap_exp.monodromy
      ((Path.Homotopic.Quotient.mk L).map exp') ⟨0, rfl⟩ = ⟨c, rfl⟩ at h
  subst exp'
  exact h

/-- The straight-line path `t ↦ t · b` in `ℝ` from `0` to `b`. -/
def linePath (b : ℝ) : Path (0 : ℝ) b where
  toFun t := (t : ℝ) * b
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

/-- The homotopy class of loops at `1` obtained by exponentiating the straight-line path to
`n · 2π`. -/
def expLoopClass (n : ℤ) : Path.Homotopic.Quotient (1 : Circle) 1 :=
  Path.Homotopic.Quotient.mk
    (((linePath ((n : ℝ) * (2 * Real.pi))).map Circle.exp.continuous).cast
      Circle.exp_zero.symm (Circle.exp_int_mul_two_pi n).symm)

/-- The fundamental group element `γₙ` realizing winding number `n`. -/
def gammaN (n : ℤ) : FundamentalGroup Circle 1 :=
  FundamentalGroup.fromPath (expLoopClass n)

/-- **Explicit loop and its lift.** The monodromy of `toPath γₙ` at `⟨0⟩` is `⟨n · 2π⟩`. -/
theorem explicit_loop_lift (n : ℤ) :
    Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath (gammaN n)) fiberBasePt
      = ⟨(n : ℝ) * (2 * Real.pi), mem_exp_preimage_one.mpr (Circle.exp_int_mul_two_pi n)⟩ := by
  apply Subtype.ext
  have hc : Circle.exp ((n : ℝ) * (2 * Real.pi)) = 1 := Circle.exp_int_mul_two_pi n
  have hstep : FundamentalGroup.toPath (gammaN n)
      = ((Path.Homotopic.Quotient.mk (linePath ((n : ℝ) * (2 * Real.pi)))).map
          Circle.exp).cast Circle.exp_zero.symm hc.symm := by
    show expLoopClass n = _
    unfold expLoopClass
    rw [Path.Homotopic.Quotient.mk_cast, Path.Homotopic.Quotient.mk_map]
  rw [hstep,
    monodromy_cast_val _ Circle.exp_zero.symm hc.symm fiberBasePt ⟨0, rfl⟩ rfl,
    monodromy_exp_comp (linePath ((n : ℝ) * (2 * Real.pi)))]

/-- **Winding number is surjective.** -/
theorem wind_surjective : Function.Surjective wind := by
  intro n
  refine ⟨gammaN n, ?_⟩
  apply two_pi_cancel
  calc
    (wind (gammaN n) : ℝ) * (2 * Real.pi) = (Circle.isCoveringMap_exp.monodromy
      (FundamentalGroup.toPath (gammaN n)) fiberBasePt).val := by
      rw [wind_spec]
    _ = ((n : ℝ) * (2 * Real.pi)) := by
      rw [explicit_loop_lift n]
    _ = (n : ℝ) * (2 * Real.pi) := rfl

/-- **Winding-number isomorphism.** `γ ↦ Multiplicative.ofAdd (w γ)` is a group isomorphism
`π₁(S¹, 1) ≃* Multiplicative ℤ`. -/
def windEquiv : FundamentalGroup Circle 1 ≃* Multiplicative ℤ :=
  MulEquiv.ofBijective
    (MonoidHom.mk' (fun γ : FundamentalGroup Circle 1 => Multiplicative.ofAdd (wind γ)) (by
      intro γ δ
      calc
        Multiplicative.ofAdd (wind (γ * δ)) = Multiplicative.ofAdd (wind γ + wind δ) := by rw [wind_mul]
        _ = Multiplicative.ofAdd (wind γ) * Multiplicative.ofAdd (wind δ) := rfl))
    (by
      refine ⟨?_, ?_⟩
      · intro x y h
        apply wind_injective
        simpa using congr_arg Multiplicative.toAdd h
      · intro z
        rcases wind_surjective (Multiplicative.toAdd z) with ⟨γ, hγ⟩
        refine ⟨γ, ?_⟩
        simp [hγ])

end

end Topology
end LeanEval
