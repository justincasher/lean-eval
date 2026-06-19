import LeanEval.KnotTheory.Linking.Basic
import LeanEval.KnotTheory.Linking.Invariance
import LeanEval.KnotTheory.Linking.Examples
import LeanEval.KnotTheory.Linking.Computation

/-!
# Existence of a non-isotopic pair of oriented two-component links

This module aggregates the formalization, split across:

* `LeanEval.KnotTheory.Linking.Basic` — the Gauss map, scalar triple product,
  linking integrand and linking number, plus foundational smoothness/continuity
  and the pointwise algebraic and differentiation identities;
* `LeanEval.KnotTheory.Linking.Invariance` — ambient-isotopy invariance of the
  linking number (deformed data, the divergence identity, differentiation under
  the integral, reparametrization invariance);
* `LeanEval.KnotTheory.Linking.Examples` — the unlink and the Hopf link;
* `LeanEval.KnotTheory.Linking.Computation` — the two linking-number
  computations (`linking_unlink_zero`, `linking_hopf_nonzero`).

The headline existence theorem lives here so it sits in the module named by the
problem manifest.
-/

namespace LeanEval
namespace KnotTheory

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
