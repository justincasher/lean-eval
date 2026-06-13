import Mathlib
import EvalTools.Markers

/-!
Topological facts about the two "type copies" of `B(H)` used in the von Neumann
double commutant theorem: the weak operator topology `ContinuousLinearMapWOT`
(inclusion `ContinuousLinearMap.toWOT`) and the strong operator topology /
pointwise-convergence topology `PointwiseConvergenceCLM` (inclusion
`ContinuousLinearMap.toPointwiseConvergenceCLM`). Helper file for
`LeanEval.Analysis.VonNeumannDoubleCommutant`.

Note. The ambient Mathlib used here defines `ContinuousLinearMapWOT σ E F` as an
irreducible type copy of `E →SL[σ] F` carrying only the additive/topological
structure of the weak operator topology; it does not register a multiplicative
(ring) structure on the type copy. We therefore transport the ring structure
from `H →L[ℂ] H` along the linear equivalence `ContinuousLinearMap.toWOT`, so
that the multiplication-dependent statements (commutants, `Commute`, …) can be
phrased faithfully on the WOT type copy. The two inclusions `ι_W` and `ι_S` are
recorded as plain equivalences `wotEquiv` and `sotEquiv` (each the underlying map
of the corresponding Mathlib inclusion, i.e. the identity on operators).
-/

namespace LeanEval
namespace Analysis

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The WOT inclusion `ι_W : H →L[ℂ] H → (H →WOT[ℂ] H)` as an equivalence, the
underlying map of `ContinuousLinearMap.toWOT` (the identity on operators). -/
noncomputable def wotEquiv :
    (H →L[ℂ] H) ≃ (ContinuousLinearMapWOT (RingHom.id ℂ) H H) :=
  (ContinuousLinearMap.toWOT (RingHom.id ℂ) H H).toEquiv

/-- The SOT inclusion `ι_S : H →L[ℂ] H → (H →Lₚₜ[ℂ] H)` as an equivalence, the
underlying map of `ContinuousLinearMap.toPointwiseConvergenceCLM` (the identity on
operators). -/
noncomputable def sotEquiv :
    (H →L[ℂ] H) ≃ (PointwiseConvergenceCLM (RingHom.id ℂ) H H) :=
  (ContinuousLinearMap.toUniformConvergenceCLM (𝕜₁ := ℂ) (𝕜₂ := ℂ)
    (σ := RingHom.id ℂ) (E := H) (F := H) {s : Set H | Finite s}).toEquiv

/-- The ring structure on the WOT type copy, transported from `H →L[ℂ] H` along the
inclusion `ι_W`. This is the multiplicative structure under which the WOT inclusion
is a ring homomorphism. -/
noncomputable instance : Ring (ContinuousLinearMapWOT (RingHom.id ℂ) H H) :=
  Equiv.ring (wotEquiv (H := H)).symm

/-- The WOT type copy `ContinuousLinearMapWOT` is a `T2Space` (`lem:wot-t2space`). -/
theorem wot_t2space :
    T2Space (ContinuousLinearMapWOT (RingHom.id ℂ) H H) := by
  sorry

/-- Multiplication on the WOT type copy is separately continuous
(`lem:wot-separately-continuous-mul`). -/
theorem wot_separatelyContinuousMul :
    SeparatelyContinuousMul (ContinuousLinearMapWOT (RingHom.id ℂ) H H) := by
  sorry

/-- For any subset `Y` of the WOT type copy, its centralizer is closed
(`lem:wot-centralizer-closed`). -/
theorem wot_centralizer_isClosed
    (Y : Set (ContinuousLinearMapWOT (RingHom.id ℂ) H H)) :
    IsClosed (Set.centralizer Y) := by
  sorry

/-- The WOT inclusion preserves commuting: `Commute S T` in `B(H)` iff
`Commute (ι_W S) (ι_W T)` in the WOT type copy (`lem:wot-commute-iff`). -/
theorem wot_commute_iff (S T : H →L[ℂ] H) :
    Commute S T ↔
      Commute (wotEquiv (H := H) S) (wotEquiv (H := H) T) := by
  sorry

/-- The WOT inclusion preserves commutants: for every `X ⊆ B(H)`,
`ι_W (X') = (ι_W X)'` (`lem:toWOT-centralizer`). -/
theorem toWOT_centralizer (X : Set (H →L[ℂ] H)) :
    (wotEquiv (H := H)) '' (Set.centralizer X) =
      Set.centralizer ((wotEquiv (H := H)) '' X) := by
  sorry

/-- `(1) ⇒ (2)`: if `S'' = S` then the WOT image of `S` is closed
(`lem:dct-wot-closed`). -/
theorem dct_wot_closed (S : Set (H →L[ℂ] H))
    (hS : Set.centralizer (Set.centralizer S) = S) :
    IsClosed ((wotEquiv (H := H)) '' S) := by
  sorry

/-- Each WOT pairing `T ↦ ⟪T x, y⟫` is continuous on the SOT type copy
(`lem:sot-pairing-continuous`). The element `T` of the SOT type copy is evaluated
through its underlying operator via `ι_S⁻¹`. -/
theorem sot_pairing_continuous (x y : H) :
    Continuous (fun T : PointwiseConvergenceCLM (RingHom.id ℂ) H H =>
      (inner ℂ ((sotEquiv (H := H)).symm T x) y : ℂ)) := by
  sorry

/-- The "identity on underlying operators" map from the SOT type copy to the WOT
type copy: it sends `ι_S T` to `ι_W T`. This is the continuous map `φ` of
`lem:continuous-sot-wot`; concretely it is `ι_W ∘ ι_S⁻¹`. -/
noncomputable def sotToWot (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] :
    PointwiseConvergenceCLM (RingHom.id ℂ) H H → ContinuousLinearMapWOT (RingHom.id ℂ) H H :=
  fun T => wotEquiv (H := H) ((sotEquiv (H := H)).symm T)

/-- `φ ∘ ι_S = ι_W` on underlying operators: the SOT-to-WOT map agrees with the WOT
inclusion after precomposition with the SOT inclusion (`lem:continuous-sot-wot`). -/
theorem sotToWot_sotEquiv (T : H →L[ℂ] H) :
    sotToWot H (sotEquiv (H := H) T) = wotEquiv (H := H) T := by
  sorry

/-- The SOT is finer than the WOT: the identity map `φ = sotToWot` from the SOT
type copy to the WOT type copy is continuous (`lem:continuous-sot-wot`). -/
theorem continuous_sotToWot :
    Continuous (sotToWot H) := by
  sorry

/-- The SOT image is a preimage of the WOT image under `φ = sotToWot`: for every
`X ⊆ B(H)`, `ι_S X = φ⁻¹ (ι_W X)` (`lem:sot-image-eq-preimage`). -/
theorem sot_image_eq_preimage (X : Set (H →L[ℂ] H)) :
    (sotEquiv (H := H)) '' X =
      (sotToWot H) ⁻¹' ((wotEquiv (H := H)) '' X) := by
  sorry

/-- `(2) ⇒ (3)`: if the WOT image of `S` is closed, then its SOT image is closed
(`lem:wot-closed-imp-sot-closed`). -/
theorem wot_closed_imp_sot_closed (S : Set (H →L[ℂ] H))
    (hS : IsClosed ((wotEquiv (H := H)) '' S)) :
    IsClosed ((sotEquiv (H := H)) '' S) := by
  sorry

end Analysis
end LeanEval
