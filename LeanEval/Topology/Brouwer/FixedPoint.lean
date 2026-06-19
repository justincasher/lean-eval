import Mathlib

/-!
# The fixed-point property

Section 1 of the Brouwer blueprint: the fixed-point property (FPP) of a
topological space, its invariance under homeomorphism, and the passage from a
subspace having FPP to an ambient fixed point.
-/

namespace LeanEval
namespace Topology

/-- **Fixed-point property (FPP).** A topological space `X` has the fixed-point
property if every continuous self-map `f : X → X` has a fixed point. -/
def HasFPP (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ f : X → X, Continuous f → ∃ x, f x = x

/-- **FPP is a topological invariant.** If `X ≃ₜ Y` and `X` has the fixed-point
property, then so does `Y`. -/
theorem fpp_homeo {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) (hX : HasFPP X) : HasFPP Y := by
  intro g hg
  have h_cont : Continuous h := h.continuous_toFun
  have hs_cont : Continuous h.symm := h.continuous_invFun
  have hf : Continuous (h.symm ∘ g ∘ h) :=
    hs_cont.comp (hg.comp h_cont)
  rcases hX (h.symm ∘ g ∘ h) hf with ⟨x, hx⟩
  have hy_eq : g (h x) = h x := by
    calc
      g (h x) = h (h.symm (g (h x))) := by
        symm; exact h.right_inv (g (h x))
      _ = h x := by
        simpa using congrArg h hx
  exact ⟨h x, hy_eq⟩

/-- **Subtype FPP gives an ambient fixed point.** If the subspace `K ⊆ E_d` has
the fixed-point property, then every map continuous on `K` and mapping `K` into
`K` has a fixed point in `K`. -/
theorem fpp_ambient {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (hK : HasFPP K)
    (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hf : ContinuousOn f K) (hmaps : Set.MapsTo f K K) :
    ∃ x ∈ K, f x = x := by
  let g : K → K := hmaps.restrict f K K
  have hg : Continuous g := hf.mapsToRestrict hmaps
  rcases hK g hg with ⟨x, hx⟩
  refine ⟨x.val, x.property, ?_⟩
  simpa [g, Set.MapsTo.restrict] using congr_arg Subtype.val hx

end Topology
end LeanEval
