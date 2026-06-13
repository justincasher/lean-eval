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
  infer_instance

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
  haveI : T2Space (ContinuousLinearMapWOT (RingHom.id ℂ) H H) := wot_t2space
  haveI : SeparatelyContinuousMul (ContinuousLinearMapWOT (RingHom.id ℂ) H H) :=
    wot_separatelyContinuousMul
  exact Set.isClosed_centralizer Y

/-- The WOT inclusion preserves commuting: `Commute S T` in `B(H)` iff
`Commute (ι_W S) (ι_W T)` in the WOT type copy (`lem:wot-commute-iff`). -/
theorem wot_commute_iff (S T : H →L[ℂ] H) :
    Commute S T ↔
      Commute (wotEquiv (H := H) S) (wotEquiv (H := H) T) := by
  let f : (H →L[ℂ] H) ≃+* (ContinuousLinearMapWOT (RingHom.id ℂ) H H) :=
    (Equiv.ringEquiv (wotEquiv (H := H)).symm).symm
  have hfS (A : H →L[ℂ] H) : f A = wotEquiv A := rfl
  constructor
  · intro h
    have hST : S * T = T * S := h
    calc
      f S * f T = f (S * T) := (f.map_mul S T).symm
      _ = f (T * S) := by rw [hST]
      _ = f T * f S := f.map_mul T S
  · intro h
    have hf_commute : Commute (f S) (f T) := by simpa [hfS] using h
    have h_eq : f (S * T) = f (T * S) := by
      calc
        f (S * T) = f S * f T := f.map_mul S T
        _ = f T * f S := hf_commute
        _ = f (T * S) := (f.map_mul T S).symm
    exact f.injective h_eq

/-- The WOT inclusion preserves commutants: for every `X ⊆ B(H)`,
`ι_W (X') = (ι_W X)'` (`lem:toWOT-centralizer`). -/
theorem toWOT_centralizer (X : Set (H →L[ℂ] H)) :
    (wotEquiv (H := H)) '' (Set.centralizer X) =
      Set.centralizer ((wotEquiv (H := H)) '' X) := by
  ext U
  constructor
  · intro h
    rcases h with ⟨T, hT, rfl⟩
    rw [Set.mem_centralizer_iff] at hT ⊢
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have h_comm : Commute x T := by
      rw [commute_iff_eq]
      exact hT x hx
    rw [← commute_iff_eq]
    exact (wot_commute_iff x T).mp h_comm
  · intro h
    have h_surj : Function.Surjective (wotEquiv (H := H)) := wotEquiv.surjective
    rcases h_surj U with ⟨T, rfl⟩
    refine ⟨T, ?_, rfl⟩
    rw [Set.mem_centralizer_iff]
    intro x hx
    have h_mem : wotEquiv (H := H) x ∈ (wotEquiv (H := H)) '' X :=
      (Set.mem_image (wotEquiv (H := H)) X (wotEquiv (H := H) x)).mpr ⟨x, hx, rfl⟩
    have h_central := (Set.mem_centralizer_iff.mp h) (wotEquiv (H := H) x) h_mem
    rw [← commute_iff_eq]
    apply (wot_commute_iff x T).mpr
    rw [commute_iff_eq]
    exact h_central

/-- `(1) ⇒ (2)`: if `S'' = S` then the WOT image of `S` is closed
(`lem:dct-wot-closed`). -/
theorem dct_wot_closed (S : Set (H →L[ℂ] H))
    (hS : Set.centralizer (Set.centralizer S) = S) :
    IsClosed ((wotEquiv (H := H)) '' S) := by
  have hcalc : (wotEquiv (H := H)) '' S =
      Set.centralizer (Set.centralizer ((wotEquiv (H := H)) '' S)) := by
    calc
      (wotEquiv (H := H)) '' S =
          (wotEquiv (H := H)) '' (Set.centralizer (Set.centralizer S)) := by
        rw [hS]
      _ = Set.centralizer ((wotEquiv (H := H)) '' (Set.centralizer S)) := by
        rw [toWOT_centralizer]
      _ = Set.centralizer (Set.centralizer ((wotEquiv (H := H)) '' S)) := by
        rw [toWOT_centralizer]
  rw [hcalc]
  exact wot_centralizer_isClosed (Set.centralizer ((wotEquiv (H := H)) '' S))

/-- Each WOT pairing `T ↦ ⟪T x, y⟫` is continuous on the SOT type copy
(`lem:sot-pairing-continuous`). The element `T` of the SOT type copy is evaluated
through its underlying operator via `ι_S⁻¹`. -/
theorem sot_pairing_continuous (x y : H) :
    Continuous (fun T : PointwiseConvergenceCLM (RingHom.id ℂ) H H =>
      (inner ℂ ((sotEquiv (H := H)).symm T x) y : ℂ)) := by
  have h_eval : Continuous (fun T : PointwiseConvergenceCLM (RingHom.id ℂ) H H => T x) :=
    continuous_eval_const x
  have h_comp : Continuous (fun T : PointwiseConvergenceCLM (RingHom.id ℂ) H H => (sotEquiv (H := H)).symm T x) := by
    simpa using h_eval
  have h_const : Continuous (fun (_ : PointwiseConvergenceCLM (RingHom.id ℂ) H H) => y) :=
    continuous_const
  exact (h_comp.inner h_const)

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
  simp [sotToWot]

/-- The SOT is finer than the WOT: the identity map `φ = sotToWot` from the SOT
type copy to the WOT type copy is continuous (`lem:continuous-sot-wot`). -/
theorem continuous_sotToWot :
    Continuous (sotToWot H) := by
  -- The WOT topology on ContinuousLinearMapWOT is induced by the family of
  -- pairings A ↦ y' (A x).  By continuous_of_dual_apply_continuous it suffices
  -- to show each such pairing is SOT-continuous.
  apply ContinuousLinearMapWOT.continuous_of_dual_apply_continuous
  intro x y'
  -- By the Riesz representation theorem every y' : StrongDual ℂ H equals
  -- innerSL ℂ z for some z : H.
  obtain ⟨z, hz⟩ := (InnerProductSpace.toDual (𝕜 := ℂ) (E := H)).surjective y'
  have hy'_apply (v : H) : y' v = inner ℂ z v := by
    calc
      y' v = (InnerProductSpace.toDual ℂ H z) v := by rw [hz]
      _ = (InnerProductSpace.toDualMap ℂ H z) v := rfl
      _ = inner ℂ z v := rfl
  have h_sotToWot_apply (T : PointwiseConvergenceCLM (RingHom.id ℂ) H H) (v : H) :
      (sotToWot H T) v = ((sotEquiv (H := H)).symm T) v := by
    simp [sotToWot, wotEquiv]
  have h_inner_conj (T : PointwiseConvergenceCLM (RingHom.id ℂ) H H) :
      y' ((sotToWot H T) x) = starRingEnd ℂ (inner ℂ ((sotEquiv (H := H)).symm T x) z) := by
    calc
      y' ((sotToWot H T) x) = y' (((sotEquiv (H := H)).symm T) x) := by rw [h_sotToWot_apply]
      _ = inner ℂ z (((sotEquiv (H := H)).symm T) x) := hy'_apply _
      _ = (starRingEnd ℂ) (inner ℂ (((sotEquiv (H := H)).symm T) x) z) := by rw [inner_conj_symm]
  -- The function T ↦ y' ((sotToWot H T) x) is continuous
  have h_cont_inner : Continuous (fun T : PointwiseConvergenceCLM (RingHom.id ℂ) H H =>
      inner ℂ ((sotEquiv (H := H)).symm T x) z) :=
    sot_pairing_continuous x z
  have h_cont : Continuous (fun (T : PointwiseConvergenceCLM (RingHom.id ℂ) H H) =>
      y' ((sotToWot H T) x)) := by
    -- rewrite using the equality h_inner_conj
    have : (fun T : PointwiseConvergenceCLM (RingHom.id ℂ) H H => y' ((sotToWot H T) x))
        = (starRingEnd ℂ) ∘ (fun T : PointwiseConvergenceCLM (RingHom.id ℂ) H H =>
            inner ℂ ((sotEquiv (H := H)).symm T x) z) := by
      ext T; exact h_inner_conj T
    rw [this]
    exact (continuous_star : Continuous (starRingEnd ℂ)).comp h_cont_inner
  exact h_cont

/-- The SOT image is a preimage of the WOT image under `φ = sotToWot`: for every
`X ⊆ B(H)`, `ι_S X = φ⁻¹ (ι_W X)` (`lem:sot-image-eq-preimage`). -/
theorem sot_image_eq_preimage (X : Set (H →L[ℂ] H)) :
    (sotEquiv (H := H)) '' X =
      (sotToWot H) ⁻¹' ((wotEquiv (H := H)) '' X) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp [sotToWot_sotEquiv, hx]
  · intro hz
    rcases hz with ⟨x, hx, h⟩
    set y := (sotEquiv (H := H)).symm z with hy
    have hz_eq : z = sotEquiv (H := H) y := by
      simp [hy]
    have h_eq : wotEquiv (H := H) y = wotEquiv (H := H) x := by
      calc
        wotEquiv (H := H) y = sotToWot H (sotEquiv (H := H) y) := by
          symm; exact sotToWot_sotEquiv _
        _ = sotToWot H z := by rw [hz_eq]
        _ = wotEquiv (H := H) x := h.symm
    have hyx : y = x := (wotEquiv (H := H)).injective h_eq
    have hy_mem : y ∈ X := by
      rw [hyx]
      exact hx
    exact ⟨y, hy_mem, hz_eq⟩

/-- `(2) ⇒ (3)`: if the WOT image of `S` is closed, then its SOT image is closed
(`lem:wot-closed-imp-sot-closed`). -/
theorem wot_closed_imp_sot_closed (S : Set (H →L[ℂ] H))
    (hS : IsClosed ((wotEquiv (H := H)) '' S)) :
    IsClosed ((sotEquiv (H := H)) '' S) := by
  rw [sot_image_eq_preimage]
  exact hS.preimage (continuous_sotToWot (H := H))

end Analysis
end LeanEval
