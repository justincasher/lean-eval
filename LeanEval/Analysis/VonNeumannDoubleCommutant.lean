import Mathlib
import EvalTools.Markers
import LeanEval.Analysis.VonNeumannDoubleCommutant.Topology
import LeanEval.Analysis.VonNeumannDoubleCommutant.Orbit
import LeanEval.Analysis.VonNeumannDoubleCommutant.Amplification
import LeanEval.Analysis.VonNeumannDoubleCommutant.Blocks
import LeanEval.Analysis.VonNeumannDoubleCommutant.Approximation

namespace LeanEval
namespace Analysis

/-!
Von Neumann's double commutant theorem.

For a unital *-subalgebra `S` of bounded operators on a complex Hilbert space `H`, the
following are equivalent:

1. `S` equals its double commutant `S''`.
2. `S` is closed in the weak operator topology.
3. `S` is closed in the strong operator topology (in Mathlib, the topology of pointwise
   convergence on continuous linear maps).

The WOT and SOT live on irreducible type copies of `H →L[ℂ] H`, so each closed-ness
condition is stated as the closedness of the image of `S` under the canonical inclusion
into the corresponding type copy.
-/

/-- `(3) ⇒ (1)`: if the SOT image of `S` (the image under
`ContinuousLinearMap.toPointwiseConvergenceCLM`) is closed, then `S` equals its
double commutant, `S'' = S`. Blueprint label `thm:sot-imp-dct`. -/
theorem sot_imp_dct
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (hS : IsClosed
      (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        (S : Set (H →L[ℂ] H)))) :
    Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) = (S : Set (H →L[ℂ] H)) := by
  apply Set.Subset.antisymm
  · -- S'' ⊆ S
    intro T hT
    apply sot_closed_mem S hS T
    intro n x ε hε
    exact double_commutant_approx S hT x hε
  · -- S ⊆ S''
    exact Set.subset_centralizer_centralizer (S := (S : Set (H →L[ℂ] H)))

@[eval_problem]
theorem vonNeumann_doubleCommutant_tfae
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    List.TFAE
      [ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) = S
      , IsClosed
          (ContinuousLinearMap.toWOT (RingHom.id ℂ) H H '' (S : Set (H →L[ℂ] H)))
      , IsClosed
          (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
            (S : Set (H →L[ℂ] H))) ] := by
  have h_image_wot : (wotEquiv (H := H)) '' (S : Set (H →L[ℂ] H)) =
      (ContinuousLinearMap.toWOT (RingHom.id ℂ) H H) '' (S : Set (H →L[ℂ] H)) := by
    ext x; simp [wotEquiv]
  have h_image_sot : (sotEquiv (H := H)) '' (S : Set (H →L[ℂ] H)) =
      (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H) ''
        (S : Set (H →L[ℂ] H)) := by
    apply Set.image_congr
    intro x hx
    ext v : 1
    simp [sotEquiv, ContinuousLinearMap.toPointwiseConvergenceCLM,
      ContinuousLinearMap.toUniformConvergenceCLM_apply]; rfl
  tfae_have 1 → 2 := by
    intro h
    have hclosed : IsClosed ((wotEquiv (H := H)) '' (S : Set (H →L[ℂ] H))) :=
      dct_wot_closed (S : Set (H →L[ℂ] H)) h
    rw [h_image_wot] at hclosed
    exact hclosed
  tfae_have 2 → 3 := by
    intro h
    rw [← h_image_wot] at h
    have hclosed : IsClosed ((sotEquiv (H := H)) '' (S : Set (H →L[ℂ] H))) :=
      wot_closed_imp_sot_closed (S : Set (H →L[ℂ] H)) h
    rw [h_image_sot] at hclosed
    exact hclosed
  tfae_have 3 → 1 := sot_imp_dct S
  tfae_finish

end Analysis
end LeanEval
