import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Topology.Order.IntermediateValue
import EvalTools.Markers

namespace LeanEval
namespace ConvexGeometry

open Set

/-!
Minkowski-Carathéodory theorem in finite-dimensional real normed spaces.

This file formalizes the blueprint `minkowski-caratheodory-theorem`. The main result
(`mem_convexHull_finset_extremePoints_of_mem_compact_convex`) packages the theorem as a
finite extreme-point representation for each point of a compact convex set, with the
expected `finrank + 1` bound on the number of points used.

The proof combines a cardinality-bounded form of Carathéodory's theorem with Minkowski's
theorem (the finite-dimensional Krein–Milman theorem). The supporting lemmas are stated
faithfully to the blueprint; many of the "direction subspace" lemmas carry the explicit
shared context (a base point `p ∈ s`, the direction subspace `W = vectorSpan ℝ s`, and the
translated set `s' = {w ∈ W | w + p ∈ s}`).
-/

universe u

/-! ### Carathéodory with a dimension bound -/

/-- **Carathéodory representation lands in the convex hull of a finite image.**
From `x ∈ convexHull ℝ A` we obtain a finite affinely independent family `z` with strictly
positive weights summing to `1` representing `x`, whose image finset `t` lies in `A` and has
`x` in its convex hull. -/
theorem caratheodory_image_mem.{v} {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : Set E} {x : E} (hx : x ∈ convexHull ℝ A) :
    ∃ (ι : Type v) (_ : Fintype ι) (z : ι → E) (w : ι → ℝ) (t : Finset E),
      Set.range z ⊆ A ∧ AffineIndependent ℝ z ∧ (∀ i, 0 < w i) ∧
      ∑ i, w i = 1 ∧ ∑ i, w i • z i = x ∧
      (↑t : Set E) = Set.range z ∧ (↑t : Set E) ⊆ A ∧
      x ∈ convexHull ℝ (↑t : Set E) := by
  sorry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Carathéodory cardinality estimate.** With `z` affinely independent and `t` its image
finset, `#t ≤ #ι ≤ finrank ℝ E + 1`. -/
theorem caratheodory_card_bound [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] {z : ι → E}
    {t : Finset E} (hz : AffineIndependent ℝ z) (ht : (↑t : Set E) = Set.range z) :
    t.card ≤ Fintype.card ι ∧ Fintype.card ι ≤ Module.finrank ℝ E + 1 := by
  sorry

/-- **Carathéodory cardinality bound.** Every point of `convexHull ℝ A` lies in the convex
hull of a finite subset `t ⊆ A` with at most `finrank ℝ E + 1` points. -/
theorem caratheodory_card [FiniteDimensional ℝ E] {A : Set E} {x : E}
    (hx : x ∈ convexHull ℝ A) :
    ∃ t : Finset E, (↑t : Set E) ⊆ A ∧ t.card ≤ Module.finrank ℝ E + 1 ∧
      x ∈ convexHull ℝ (↑t : Set E) := by
  sorry

/-! ### Building blocks for Minkowski's theorem -/

/-- **Maximal face of a linear functional.** The face of `s` on which the continuous linear
functional `ℓ` attains its maximum, i.e. the exposed subset determined by `ℓ`. -/
def exposedFace (ℓ : E →L[ℝ] ℝ) (s : Set E) : Set E := {y | y ∈ s ∧ ∀ z ∈ s, ℓ z ≤ ℓ y}

/-- **The maximal face is an extreme subset.** `exposedFace ℓ s` is compact and convex, and its
extreme points are extreme points of `s`. -/
theorem exposedFace_isExtreme {s : Set E} (hscomp : IsCompact s) (hsconv : Convex ℝ s)
    (ℓ : E →L[ℝ] ℝ) :
    IsCompact (exposedFace ℓ s) ∧ Convex ℝ (exposedFace ℓ s) ∧
      (exposedFace ℓ s).extremePoints ℝ ⊆ s.extremePoints ℝ := by
  sorry

/-- **The maximal face lies in the kernel of `ℓ`.** Every difference of two points of
`exposedFace ℓ s` is annihilated by `ℓ`. -/
theorem exposedFace_vectorSpan_le_ker {s : Set E} (ℓ : E →L[ℝ] ℝ) :
    vectorSpan ℝ (exposedFace ℓ s) ≤ LinearMap.ker (ℓ : E →ₗ[ℝ] ℝ) := by
  sorry

/-- **The maximal face has smaller affine dimension.** If `ℓ` is non-constant on `s`, then the
affine dimension of `exposedFace ℓ s` is strictly smaller than that of `s`. -/
theorem exposedFace_finrank_lt [FiniteDimensional ℝ E] {s : Set E} (ℓ : E →L[ℝ] ℝ)
    {a b : E} (ha : a ∈ s) (hb : b ∈ s) (hab : ℓ a ≠ ℓ b) :
    Module.finrank ℝ (vectorSpan ℝ (exposedFace ℓ s)) <
      Module.finrank ℝ (vectorSpan ℝ s) := by
  sorry

/-- **The translated set is convex.** For a subspace `W` and a base point `p`, the translated
copy `{w ∈ W | w + p ∈ s}` of `s` inside `W` is convex. -/
theorem translatedSet_convex {s : Set E} (hsconv : Convex ℝ s) (W : Submodule ℝ E) (p : E) :
    Convex ℝ {w : W | (w : E) + p ∈ s} := by
  sorry

/-- **Intrinsic interior via the direction subspace.** With `W = vectorSpan ℝ s` and base point
`p ∈ s`, the intrinsic interior of `s` is the image of the topological interior of the
translated set under `w ↦ w + p`. -/
theorem intrinsicInterior_eq_image {s : Set E} {p : E} (hp : p ∈ s) :
    intrinsicInterior ℝ s =
      (fun w : (vectorSpan ℝ s) => (w : E) + p) ''
        interior {w : (vectorSpan ℝ s) | (w : E) + p ∈ s} := by
  sorry

/-- **The interior in the direction subspace is nonempty.** If `s` is nonempty (and convex),
the topological interior of the translated set in `W = vectorSpan ℝ s` is nonempty. -/
theorem interior_translatedSet_nonempty [FiniteDimensional ℝ E] {s : Set E} (hsconv : Convex ℝ s)
    (hne : s.Nonempty) {p : E} (hp : p ∈ s) :
    (interior {w : (vectorSpan ℝ s) | (w : E) + p ∈ s}).Nonempty := by
  sorry

/-- **Separation in the direction subspace.** A relative boundary point `y` of `s` translates to
`y - p` which is not in the interior of the translated set, and is strictly separated from it by
a continuous linear functional `g` on `W = vectorSpan ℝ s`. -/
theorem separation_in_direction {s : Set E} (hsconv : Convex ℝ s) {p : E} (hp : p ∈ s)
    {y : E} (hy : y ∈ s) (hynotin : y ∉ intrinsicInterior ℝ s)
    (hyW : y - p ∈ vectorSpan ℝ s) :
    (⟨y - p, hyW⟩ : (vectorSpan ℝ s)) ∉ interior {w : (vectorSpan ℝ s) | (w : E) + p ∈ s} ∧
      ∃ g : (vectorSpan ℝ s) →L[ℝ] ℝ,
        ∀ w ∈ interior {w : (vectorSpan ℝ s) | (w : E) + p ∈ s}, g w < g ⟨y - p, hyW⟩ := by
  sorry

/-- **Extension of the separating functional to `E`.** The separating functional `g` on
`W = vectorSpan ℝ s` extends to a continuous linear functional `ℓ` on `E` restricting to `g`,
and every `z ∈ s` with `z - p` in the interior of the translated set satisfies `ℓ z < ℓ y`. -/
theorem extension_to_E {s : Set E} {p : E} {y : E} (hyW : y - p ∈ vectorSpan ℝ s)
    (g : (vectorSpan ℝ s) →L[ℝ] ℝ)
    (hsep : ∀ w ∈ interior {w : (vectorSpan ℝ s) | (w : E) + p ∈ s}, g w < g ⟨y - p, hyW⟩) :
    ∃ ℓ : E →L[ℝ] ℝ,
      (∀ w : (vectorSpan ℝ s), ℓ (w : E) = g w) ∧
      ∀ z ∈ s, ∀ hzW : z - p ∈ vectorSpan ℝ s,
        (⟨z - p, hzW⟩ : (vectorSpan ℝ s)) ∈ interior {w : (vectorSpan ℝ s) | (w : E) + p ∈ s} →
          ℓ z < ℓ y := by
  sorry

/-- **The bound passes to all of `s`.** If the strict bound `ℓ z < ℓ y` holds for all `z ∈ s`
with `z - p` in the interior of the translated set, then `ℓ z ≤ ℓ y` for all `z ∈ s`. -/
theorem bound_passes_to_closure [FiniteDimensional ℝ E] {s : Set E} (hsconv : Convex ℝ s)
    (hne : s.Nonempty) {p : E} (hp : p ∈ s) {y : E} (ℓ : E →L[ℝ] ℝ)
    (hstrict : ∀ z ∈ s, ∀ hzW : z - p ∈ vectorSpan ℝ s,
      (⟨z - p, hzW⟩ : (vectorSpan ℝ s)) ∈ interior {w : (vectorSpan ℝ s) | (w : E) + p ∈ s} →
        ℓ z < ℓ y) :
    ∀ z ∈ s, ℓ z ≤ ℓ y := by
  sorry

/-- **The separating functional is non-constant on `s`.** Under the strict separation bound, the
functional `ℓ` takes two distinct values on `s`. -/
theorem functional_non_constant [FiniteDimensional ℝ E] {s : Set E} (hsconv : Convex ℝ s)
    (hne : s.Nonempty) {p : E} (hp : p ∈ s) {y : E} (hy : y ∈ s) (ℓ : E →L[ℝ] ℝ)
    (hstrict : ∀ z ∈ s, ∀ hzW : z - p ∈ vectorSpan ℝ s,
      (⟨z - p, hzW⟩ : (vectorSpan ℝ s)) ∈ interior {w : (vectorSpan ℝ s) | (w : E) + p ∈ s} →
        ℓ z < ℓ y) :
    ∃ a ∈ s, ∃ b ∈ s, ℓ a ≠ ℓ b := by
  sorry

/-- **Supporting functional at a relative boundary point.** A point `y ∈ s` not in the intrinsic
interior of `s` admits a non-constant supporting functional `ℓ` with `ℓ z ≤ ℓ y` for all `z ∈ s`
(equivalently `y ∈ exposedFace ℓ s`). -/
theorem supporting_functional [FiniteDimensional ℝ E] {s : Set E} (hsconv : Convex ℝ s)
    (hne : s.Nonempty) {y : E} (hy : y ∈ s) (hynotin : y ∉ intrinsicInterior ℝ s) :
    ∃ ℓ : E →L[ℝ] ℝ, (∃ a ∈ s, ∃ b ∈ s, ℓ a ≠ ℓ b) ∧ ∀ z ∈ s, ℓ z ≤ ℓ y := by
  sorry

/-- **A nonzero direction exists.** If the affine dimension of `s` is at least `1`, then
`vectorSpan ℝ s` contains a nonzero vector. -/
theorem exists_direction_vector {s : Set E} (h : 1 ≤ Module.finrank ℝ (vectorSpan ℝ s)) :
    ∃ v ∈ vectorSpan ℝ s, v ≠ 0 := by
  sorry

/-- **The line section is compact and convex.** For `x ∈ s` and a nonzero direction `v`, the
section `{t | x + t • v ∈ s}` is compact and convex. -/
theorem lineSection_isCompact_convex {s : Set E} (hscomp : IsCompact s) (hsconv : Convex ℝ s)
    {x : E} (hx : x ∈ s) {v : E} (hv : v ≠ 0) :
    IsCompact {t : ℝ | x + t • v ∈ s} ∧ Convex ℝ {t : ℝ | x + t • v ∈ s} := by
  sorry

/-- **The line section is a closed interval.** The section equals `Icc (sInf T) (sSup T)`. -/
theorem lineSection_eq_Icc {s : Set E} (hscomp : IsCompact s) (hsconv : Convex ℝ s)
    {x : E} (hx : x ∈ s) {v : E} (hv : v ≠ 0) :
    {t : ℝ | x + t • v ∈ s} =
      Set.Icc (sInf {t : ℝ | x + t • v ∈ s}) (sSup {t : ℝ | x + t • v ∈ s}) := by
  sorry

/-- **Zero is interior to the section.** If `0` is in the interior of the section, then
`sInf T < 0 < sSup T`. -/
theorem lineSection_zero_interior {s : Set E} (hscomp : IsCompact s) (hsconv : Convex ℝ s)
    {x : E} (hx : x ∈ s) {v : E} (hv : v ≠ 0)
    (h0 : 0 ∈ interior {t : ℝ | x + t • v ∈ s}) :
    sInf {t : ℝ | x + t • v ∈ s} < 0 ∧ 0 < sSup {t : ℝ | x + t • v ∈ s} := by
  sorry

/-- **Endpoints of the section are not interior.** With `a = sInf T` and `b = sSup T`, neither
`x + a • v` nor `x + b • v` lies in the intrinsic interior of `s`. -/
theorem segment_endpoints_not_interior {s : Set E} (hscomp : IsCompact s) (hsconv : Convex ℝ s)
    {x : E} (hx : x ∈ s) {v : E} (hv : v ≠ 0) (hvspan : v ∈ vectorSpan ℝ s) :
    x + (sInf {t : ℝ | x + t • v ∈ s}) • v ∉ intrinsicInterior ℝ s ∧
      x + (sSup {t : ℝ | x + t • v ∈ s}) • v ∉ intrinsicInterior ℝ s := by
  sorry

/-- **An interior point lies between two boundary points.** If `finrank (vectorSpan ℝ s) ≥ 1`
and `x` is in the intrinsic interior of `s`, then `x` lies on a segment between two points of `s`
that are not in the intrinsic interior of `s`. -/
theorem interior_in_segment {s : Set E} (hscomp : IsCompact s) (hsconv : Convex ℝ s)
    (h : 1 ≤ Module.finrank ℝ (vectorSpan ℝ s)) {x : E} (hx : x ∈ intrinsicInterior ℝ s) :
    ∃ y ∈ s, ∃ z ∈ s, y ∉ intrinsicInterior ℝ s ∧ z ∉ intrinsicInterior ℝ s ∧
      x ∈ segment ℝ y z := by
  sorry

/-! ### Minkowski's theorem -/

/-- **Zero-dimensional base case.** If `finrank (vectorSpan ℝ s) = 0` and `x ∈ s`, then `x` is an
extreme point of `s` (indeed `s = {x}`). -/
theorem base_case {s : Set E} {x : E} (h : Module.finrank ℝ (vectorSpan ℝ s) = 0) (hx : x ∈ s) :
    x ∈ s.extremePoints ℝ := by
  sorry

/-- **Reduction at a relative boundary point.** A relative boundary point `y` of a nonempty
compact convex set `s` lies in a compact convex face `F ⊆ s` of strictly smaller affine dimension
whose extreme points are extreme points of `s`. -/
theorem minkowski_boundary [FiniteDimensional ℝ E] {s : Set E} (hscomp : IsCompact s)
    (hsconv : Convex ℝ s) (hne : s.Nonempty) {y : E} (hy : y ∈ s)
    (hynotin : y ∉ intrinsicInterior ℝ s) :
    ∃ F : Set E, F ⊆ s ∧ IsCompact F ∧ Convex ℝ F ∧
      F.extremePoints ℝ ⊆ s.extremePoints ℝ ∧ y ∈ F ∧
      Module.finrank ℝ (vectorSpan ℝ F) < Module.finrank ℝ (vectorSpan ℝ s) := by
  sorry

/-- **Boundary points are convex combinations of extreme points.** Assuming the induction
hypothesis on lower-dimensional compact convex sets, every relative boundary point `y` of `s`
lies in the convex hull of the extreme points of `s`. -/
theorem minkowski_boundary_mem [FiniteDimensional ℝ E] {s : Set E} (hscomp : IsCompact s)
    (hsconv : Convex ℝ s)
    (IH : ∀ (s₀ : Set E), IsCompact s₀ → Convex ℝ s₀ →
      Module.finrank ℝ (vectorSpan ℝ s₀) < Module.finrank ℝ (vectorSpan ℝ s) →
      ∀ x₀ ∈ s₀, x₀ ∈ convexHull ℝ (s₀.extremePoints ℝ))
    {y : E} (hy : y ∈ s) (hynotin : y ∉ intrinsicInterior ℝ s) :
    y ∈ convexHull ℝ (s.extremePoints ℝ) := by
  sorry

/-- **Minkowski's theorem** (finite-dimensional Krein–Milman). Every point of a compact convex set
`s` lies in the convex hull of the extreme points of `s`. -/
theorem minkowski [FiniteDimensional ℝ E] {s : Set E} (hscomp : IsCompact s) (hsconv : Convex ℝ s)
    {x : E} (hx : x ∈ s) :
    x ∈ convexHull ℝ (s.extremePoints ℝ) := by
  sorry

/-! ### Main theorem -/

/-- **Minkowski–Carathéodory theorem.** Every point of a compact convex set in a
finite-dimensional real normed space is a convex combination of at most `finrank ℝ E + 1`
extreme points. -/
@[eval_problem]
theorem mem_convexHull_finset_extremePoints_of_mem_compact_convex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} {x : E}
    (hscomp : IsCompact s)
    (hsconv : Convex ℝ s)
    (hx : x ∈ s) :
    ∃ t : Finset E,
      (↑t : Set E) ⊆ s.extremePoints ℝ ∧
      t.card ≤ Module.finrank ℝ E + 1 ∧
      x ∈ convexHull ℝ (↑t : Set E) := by
  sorry

end ConvexGeometry
end LeanEval
