import Mathlib
import LeanEval.Topology.Brouwer.Triangulation
import LeanEval.Topology.Brouwer.Simplex
import LeanEval.Topology.Brouwer.FixedPoint

/-!
# Reduction to the simplex

Section 6 of the Brouwer blueprint: compact convex sets are homeomorphic to
balls, the ball has the fixed-point property, and hence so does every compact
convex set.
-/

namespace LeanEval
namespace Topology

open scoped BigOperators
open Set

/-- **Full-dimensional convex bodies are homeomorphic to balls.** A bounded
convex set with nonempty interior has closure homeomorphic to the closed unit
ball of `E_m`. -/
theorem convex_body_homeo_ball {m} {B : Set (EuclSp m)} (hconv : Convex ℝ B)
    (hbdd : Bornology.IsBounded B) (hint : (interior B).Nonempty) :
    Nonempty (closure B ≃ₜ Metric.closedBall (0 : EuclSp m) 1) := by
  sorry

/-- **A nonempty convex set has nonempty relative interior.** -/
theorem convex_relint_nonempty {d} {K : Set (EuclSp d)} (hconv : Convex ℝ K) (hne : K.Nonempty) :
    (intrinsicInterior ℝ K).Nonempty :=
  hne.intrinsicInterior hconv

/-- **Reduction to full dimension.** A nonempty compact convex `K ⊆ E_d` is, via
a homeomorphism, a compact convex set `K'` with nonempty interior in `E_m`,
where `m = dim(affine span K)`. -/
theorem affine_span_iso {d} {K : Set (EuclSp d)} (hne : K.Nonempty) (hcomp : IsCompact K)
    (hconv : Convex ℝ K) :
    ∃ (m : ℕ) (K' : Set (EuclSp m)), IsCompact K' ∧ Convex ℝ K' ∧ (interior K').Nonempty ∧
      Nonempty (K ≃ₜ K') ∧ m = Module.finrank ℝ (vectorSpan ℝ K) := by
  sorry

/-- **Compact convex bodies are homeomorphic to balls.** A nonempty compact
convex `K ⊆ E_d` is homeomorphic to the closed unit ball of `E_m`, where
`m = dim(affine span K)`. -/
theorem convex_homeo_ball {d} {K : Set (EuclSp d)} (hne : K.Nonempty) (hcomp : IsCompact K)
    (hconv : Convex ℝ K) :
    Nonempty (K ≃ₜ Metric.closedBall (0 : EuclSp (Module.finrank ℝ (vectorSpan ℝ K))) 1) := by
  sorry

/-- **The closed ball has the fixed-point property.** -/
theorem ball_fpp (m : ℕ) : HasFPP (Metric.closedBall (0 : EuclSp m) 1) := by
  sorry

/-- **Compact convex sets have the fixed-point property.** -/
theorem convex_fpp {d} {K : Set (EuclSp d)} (hne : K.Nonempty) (hcomp : IsCompact K)
    (hconv : Convex ℝ K) : HasFPP K := by
  sorry

end Topology
end LeanEval
