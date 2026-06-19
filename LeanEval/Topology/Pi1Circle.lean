import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# The fundamental group of the circle is `ℤ`

This file contains the blueprint formalization for `π₁(S¹) ≅ ℤ`, computed via the winding number
arising from the covering map `Circle.exp : ℝ → Circle`.

The headline statement `π₁(S¹, 1) ≃* Multiplicative ℤ` is `LeanEval.Topology.pi1_circle_mulEquiv_int`
in `LeanEval.Topology.HomotopyGroups`; the declarations here build the winding-number isomorphism
with the fundamental group used to prove it.

All proofs are `sorry`'d: this file fixes faithful statements only.
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
  sorry

/-- **Integer parametrization of the fibre.** The fibre `Circle.exp ⁻¹' {1}` is in bijection with
`ℤ` via `⟨r⟩ ↦ n` where `r = n · 2π`; the inverse is `n ↦ ⟨n · 2π⟩`. -/
def fiberEquivInt : ↥(Circle.exp ⁻¹' {1}) ≃ ℤ := sorry

/-- **Fibre parametrization on integers.** The fibre point assigned to `n` has underlying real
number `n · 2π`. -/
theorem fiberEquivInt_symm_apply (n : ℤ) :
    (fiberEquivInt.symm n : ℝ) = n * (2 * Real.pi) := by
  sorry

/-- **The translated lift is the lift.** For a loop `γ₀` based at `1`, `a` with `exp a = 1`, and a
fibre point `e`, the lift of `γ₀` from `e` translated by `a` is the lift of `γ₀` from `e + a`. -/
theorem translatedLift_eq_liftPath
    (γ₀ : Path (1 : Circle) 1) {a : ℝ} (ha : Circle.exp a = 1)
    {e : ℝ} (he : Circle.exp e = 1) :
    (fun t => Circle.isCoveringMap_exp.liftPath γ₀ e (γ₀.source.trans he.symm) t + a)
      = ⇑(Circle.isCoveringMap_exp.liftPath γ₀ (e + a)
          (γ₀.source.trans
            (show (1 : Circle) = Circle.exp (e + a) by rw [Circle.exp_add, he, ha, one_mul]))) := by
  sorry

/-- **Translation invariance of monodromy.** For a class `γ`, `a` with `exp a = 1`, and a fibre
point `e`, monodromy at `e + a` is monodromy at `e` shifted by `a`. -/
theorem monodromy_translation (γ : FundamentalGroup Circle 1)
    {a : ℝ} (ha : Circle.exp a = 1) (e : ↥(Circle.exp ⁻¹' {1})) :
    (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath γ)
        ⟨e.val + a, mem_exp_preimage_one.mpr
          (by rw [Circle.exp_add, mem_exp_preimage_one.mp e.2, ha, one_mul])⟩).val
      = (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath γ) e).val + a := by
  sorry

/-- **Monodromy on a fibre point, in real coordinates.** For a class `γ` and any fibre point `e`,
the monodromy value at `e` is the value at `⟨0⟩` shifted by `(e : ℝ)`. -/
theorem monodromy_val_of_fibre (γ : FundamentalGroup Circle 1) (e : ↥(Circle.exp ⁻¹' {1})) :
    (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath γ) e).val
      = (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath γ) fiberBasePt).val
          + (e : ℝ) := by
  sorry

/-- **Winding number.** The integer assigned by `fiberEquivInt` to the monodromy of `γ` at the
basepoint lift `⟨0⟩`. -/
def wind (γ : FundamentalGroup Circle 1) : ℤ :=
  fiberEquivInt (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath γ) fiberBasePt)

/-- **Winding number specification.** The underlying real number of the monodromy of `γ` at `⟨0⟩`
equals `w(γ) · 2π`. -/
theorem wind_spec (γ : FundamentalGroup Circle 1) :
    (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath γ) fiberBasePt).val
      = wind γ * (2 * Real.pi) := by
  sorry

/-- **Group law as path concatenation.** `toPath (γ * δ) = (toPath δ).trans (toPath γ)`. -/
theorem toPath_mul (γ δ : FundamentalGroup Circle 1) :
    FundamentalGroup.toPath (γ * δ)
      = (FundamentalGroup.toPath δ).trans (FundamentalGroup.toPath γ) := by
  sorry

/-- **Additivity of winding in real coordinates.** -/
theorem wind_mul_real (γ δ : FundamentalGroup Circle 1) :
    wind (γ * δ) * (2 * Real.pi) = wind γ * (2 * Real.pi) + wind δ * (2 * Real.pi) := by
  sorry

/-- **Winding number is additive.** `w(γ · δ) = w(γ) + w(δ)`. -/
theorem wind_mul (γ δ : FundamentalGroup Circle 1) :
    wind (γ * δ) = wind γ + wind δ := by
  sorry

/-- **Path classes in `ℝ` are unique.** For any `c`, homotopy classes of paths `0 → c` in `ℝ`
form a subsingleton. -/
theorem quotient_subsingleton (c : ℝ) :
    Subsingleton (Path.Homotopic.Quotient (0 : ℝ) c) := by
  sorry

/-- The homotopy class in `ℝ` of the lift of `toPath γ` starting at `0`. -/
def liftClass (γ : FundamentalGroup Circle 1) :
    Path.Homotopic.Quotient (0 : ℝ)
      (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath γ) fiberBasePt).val := sorry

/-- **Pushing the lift class forward recovers the loop.** The image of `liftClass γ` under the map
induced by `Circle.exp` (cast to a class of loops at `1`) equals `toPath γ`. -/
theorem map_liftClass (γ : FundamentalGroup Circle 1) :
    ((liftClass γ).map Circle.exp).cast Circle.exp_zero.symm
        (mem_exp_preimage_one.mp
          (Circle.isCoveringMap_exp.monodromy (FundamentalGroup.toPath γ) fiberBasePt).2).symm
      = FundamentalGroup.toPath γ := by
  sorry

/-- **Winding number is injective.** -/
theorem wind_injective : Function.Injective wind := by
  sorry

/-- **Lift class projects to its loop class.** For a path `L : Path 0 c` with `exp c = 1`,
`toPath (fromPath ⟦exp ∘ L⟧) = ⟦exp ∘ L⟧`. -/
theorem toPath_fromPath_exp {c : ℝ} (L : Path (0 : ℝ) c) (hc : Circle.exp c = 1) :
    FundamentalGroup.toPath (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk
          ((L.map Circle.exp.continuous).cast Circle.exp_zero.symm hc.symm)))
      = Path.Homotopic.Quotient.mk
          ((L.map Circle.exp.continuous).cast Circle.exp_zero.symm hc.symm) := by
  sorry

/-- **Monodromy of an exponential loop class.** For `L : Path 0 c`, the monodromy of the class of
`exp ∘ L` at `⟨0⟩` is `⟨c⟩`. -/
theorem monodromy_exp_comp {c : ℝ} (L : Path (0 : ℝ) c) :
    Circle.isCoveringMap_exp.monodromy ((Path.Homotopic.Quotient.mk L).map Circle.exp) ⟨0, rfl⟩
      = ⟨c, rfl⟩ := by
  sorry

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
  sorry

/-- **Winding number is surjective.** -/
theorem wind_surjective : Function.Surjective wind := by
  sorry

/-- **Winding-number isomorphism.** `γ ↦ Multiplicative.ofAdd (w γ)` is a group isomorphism
`π₁(S¹, 1) ≃* Multiplicative ℤ`. -/
def windEquiv : FundamentalGroup Circle 1 ≃* Multiplicative ℤ := sorry

end

end Topology
end LeanEval
