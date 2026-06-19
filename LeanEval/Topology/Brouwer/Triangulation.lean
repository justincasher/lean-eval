import Mathlib
import LeanEval.Topology.Brouwer.Incidence

/-!
# Triangulations of the corner simplex and their incidence model

Section 3 of the Brouwer blueprint. We set up the corner simplex
`S_n = convexHull {0, e_1, …, e_n}`, barycentric coordinates and carrier faces,
the bespoke `Triangulation` structure, Sperner labelings, the labeled incidence
model attached to a Sperner-labeled triangulation, the geometric "door
incidence" lemmas, and Sperner's lemma.
-/

namespace LeanEval
namespace Topology

open scoped Classical BigOperators
open Set

/-- The ambient Euclidean space `E_n = ℝ^n`. -/
abbrev EuclSp (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The corner vertices `0, e_1, …, e_n` of `S_n`, indexed by `Fin (n+1)`:
index `0` is the origin and index `i.succ` is the `i`-th basis vector. -/
noncomputable def cornerVertex (n : ℕ) : Fin (n + 1) → EuclSp n :=
  Fin.cons 0 (fun i : Fin n => EuclideanSpace.single i (1 : ℝ))

/-- The standard corner simplex `S_n = convexHull {0, e_1, …, e_n} ⊆ E_n`. -/
def cornerSimplex (n : ℕ) : Set (EuclSp n) :=
  convexHull ℝ (Set.range (cornerVertex n))

/-- The barycentric coordinates of a point `p` relative to the corner vertices:
coordinate `0` is `1 - ∑ p i` and coordinate `i.succ` is `p i`. -/
noncomputable def baryCoord (n : ℕ) (p : EuclSp n) : Fin (n + 1) → ℝ :=
  Fin.cons (1 - ∑ i, p i) (fun i => p i)

/-- The support `{ i : x_i > 0 }` of the barycentric coordinates of `p`. -/
noncomputable def carrierSupp (n : ℕ) (p : EuclSp n) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun i => 0 < baryCoord n p i)

/-- The **carrier face** of `p`: the closed face of `S_n` spanned by the corner
vertices indexed by `carrierSupp p`. -/
noncomputable def carrierFace (n : ℕ) (p : EuclSp n) : Set (EuclSp n) :=
  convexHull ℝ (cornerVertex n '' (carrierSupp n p : Set (Fin (n + 1))))

/-- **Triangulation of the corner simplex `S_n`.** A finite set of affinely
independent cells of dimension `≤ n`, closed under nonempty faces, meeting
face-to-face, pure of dimension `n`, whose maximal cells cover `S_n`. -/
structure Triangulation (n : ℕ) where
  /-- The cells of the triangulation. -/
  cells : Finset (Finset (EuclSp n))
  indep : ∀ C ∈ cells, AffineIndependent ℝ ((↑) : C → EuclSp n)
  dim_le : ∀ C ∈ cells, C.card ≤ n + 1
  face_closed : ∀ C ∈ cells, ∀ D : Finset (EuclSp n), D.Nonempty → D ⊆ C → D ∈ cells
  face_to_face : ∀ C ∈ cells, ∀ C' ∈ cells,
    convexHull ℝ (C : Set (EuclSp n)) ∩ convexHull ℝ (C' : Set (EuclSp n))
      = convexHull ℝ ((C ∩ C' : Finset (EuclSp n)) : Set (EuclSp n))
  purity : ∀ C ∈ cells, ∃ M ∈ cells, C ⊆ M ∧ M.card = n + 1
  covering :
    (⋃ C ∈ cells.filter (fun C => C.card = n + 1), convexHull ℝ (C : Set (EuclSp n)))
      = cornerSimplex n

namespace Triangulation

variable {n : ℕ}

/-- The **maximal cells** of `T` (those with `n+1` vertices). -/
def maximalCells (T : Triangulation n) : Finset (Finset (EuclSp n)) :=
  T.cells.filter (fun C => C.card = n + 1)

/-- The **facets** / `(n-1)`-faces of `T` (those with `n` vertices). -/
def facets (T : Triangulation n) : Finset (Finset (EuclSp n)) :=
  T.cells.filter (fun C => C.card = n)

/-- `v` is a **vertex** of `T` if `{v}` is a cell. -/
def IsVertex (T : Triangulation n) (v : EuclSp n) : Prop :=
  ({v} : Finset (EuclSp n)) ∈ T.cells

/-- The **mesh** of `T`: the supremum of the diameters of its maximal cells. -/
noncomputable def mesh (T : Triangulation n) : ℝ :=
  sSup ((fun C : Finset (EuclSp n) => Metric.diam (C : Set (EuclSp n))) ''
    (T.maximalCells : Set (Finset (EuclSp n))))

end Triangulation

/-- A **Sperner labeling** of a triangulation `T`: each vertex `v` receives a
label in the support of its carrier face, `ℓ v ∈ carrierSupp v`. -/
def IsSpernerLabeling {n} (T : Triangulation n) (ℓ : EuclSp n → Fin (n + 1)) : Prop :=
  ∀ v, T.IsVertex v → ℓ v ∈ carrierSupp n v

/-- A maximal cell is **rainbow** for `ℓ` if its `n+1` vertices carry all `n+1`
distinct labels. -/
def IsRainbowCell {n} (T : Triangulation n) (ℓ : EuclSp n → Fin (n + 1))
    (C : Finset (EuclSp n)) : Prop :=
  C ∈ T.maximalCells ∧ C.image ℓ = (Finset.univ : Finset (Fin (n + 1)))

/-- A facet is a **door** for `ℓ` if its `n` vertices carry exactly the labels
`{0,…,n-1}`. -/
def IsDoorFacet {n} (T : Triangulation n) (ℓ : EuclSp n → Fin (n + 1))
    (F : Finset (EuclSp n)) : Prop :=
  F ∈ T.facets ∧ F.image ℓ = Finset.univ.erase (Fin.last n)

/-- **Labeled incidence model of a Sperner-labeled triangulation.** Cells are
the maximal cells, facets are the `(n-1)`-faces, incidence is "is a face of",
the boundary predicate is `conv(F) ⊆ ∂S_n`, and labels are the vertex labels. -/
noncomputable def triangulationModel {n} (T : Triangulation n) (ℓ : EuclSp n → Fin (n + 1)) :
    IncidenceModel n where
  Cell := {C : Finset (EuclSp n) // C ∈ T.maximalCells}
  Facet := {F : Finset (EuclSp n) // F ∈ T.facets}
  Inc C F := (F : Finset (EuclSp n)) ⊆ (C : Finset (EuclSp n))
  bdry F := convexHull ℝ ((F : Finset (EuclSp n)) : Set (EuclSp n)) ⊆ frontier (cornerSimplex n)
  cellLabel C := ((C : Finset (EuclSp n)).val).map ℓ
  facetLabel F := ((F : Finset (EuclSp n)).val).map ℓ
  cellLabel_card C := by sorry
  facetLabel_card F := by sorry
  compat C F h := by sorry

/-- **A facet spans an affine hyperplane.** The affine span of an `(n-1)`-face
`F` is the zero set of a surjective (hence nonconstant) affine functional; its
two open half-spaces `{φ > 0}`, `{φ < 0}` are the two components of the
complement. -/
theorem facet_hyperplane {n} (T : Triangulation n) {F : Finset (EuclSp n)}
    (hF : F ∈ T.facets) :
    ∃ φ : EuclSp n →ᵃ[ℝ] ℝ, Function.Surjective φ ∧
      {x | φ x = 0} = (affineSpan ℝ (F : Set (EuclSp n)) : Set (EuclSp n)) := by
  sorry

/-- **An incident cell lies on one side of its facet.** The off-facet vertex `w`
of a maximal cell `C ⊇ F` lies off the hyperplane, and all of `conv C` lies in
the closed half-space on `w`'s side (`φ w` and `φ x` have the same sign). -/
theorem cell_one_side {n} (T : Triangulation n) {C F : Finset (EuclSp n)}
    (hC : C ∈ T.maximalCells) (hF : F ∈ T.facets) (hFC : F ⊆ C)
    (φ : EuclSp n →ᵃ[ℝ] ℝ) (hφ : Function.Surjective φ)
    (hker : {x | φ x = 0} = (affineSpan ℝ (F : Set (EuclSp n)) : Set (EuclSp n))) :
    ∃ w ∈ C, w ∉ F ∧ φ w ≠ 0 ∧
      ∀ x ∈ convexHull ℝ (C : Set (EuclSp n)), 0 ≤ φ w * φ x := by
  sorry

/-- **At most one incident cell per side.** Two distinct maximal cells sharing
`F` lie on opposite sides of its hyperplane: their off-facet vertices have
`φ`-values of opposite sign. -/
theorem one_cell_per_side {n} (T : Triangulation n) {F : Finset (EuclSp n)}
    (hF : F ∈ T.facets) (φ : EuclSp n →ᵃ[ℝ] ℝ) (hφ : Function.Surjective φ)
    (hker : {x | φ x = 0} = (affineSpan ℝ (F : Set (EuclSp n)) : Set (EuclSp n)))
    {C C' : Finset (EuclSp n)} (hC : C ∈ T.maximalCells) (hC' : C' ∈ T.maximalCells)
    (hFC : F ⊆ C) (hFC' : F ⊆ C') (hne : C ≠ C') :
    ∃ w ∈ C, ∃ w' ∈ C', φ w * φ w' < 0 := by
  sorry

/-- **Both sides of an interior facet are occupied.** If `F` is not contained in
`∂S_n`, then each open side carries an incident maximal cell. -/
theorem interior_facet_both_sides {n} (T : Triangulation n) {F : Finset (EuclSp n)}
    (hF : F ∈ T.facets)
    (hint : ¬ (convexHull ℝ (F : Set (EuclSp n)) ⊆ frontier (cornerSimplex n)))
    (φ : EuclSp n →ᵃ[ℝ] ℝ) (hφ : Function.Surjective φ)
    (hker : {x | φ x = 0} = (affineSpan ℝ (F : Set (EuclSp n)) : Set (EuclSp n))) :
    (∃ C ∈ T.maximalCells, F ⊆ C ∧ ∃ w ∈ C, 0 < φ w) ∧
    (∃ C ∈ T.maximalCells, F ⊆ C ∧ ∃ w ∈ C, φ w < 0) := by
  sorry

/-- **A boundary facet is occupied on one side only.** If `conv(F) ⊆ ∂S_n`, then
all incident maximal cells lie on one closed side of the hyperplane. -/
theorem boundary_facet_one_side {n} (T : Triangulation n) {F : Finset (EuclSp n)}
    (hF : F ∈ T.facets)
    (hbd : convexHull ℝ (F : Set (EuclSp n)) ⊆ frontier (cornerSimplex n))
    (φ : EuclSp n →ᵃ[ℝ] ℝ) (hφ : Function.Surjective φ)
    (hker : {x | φ x = 0} = (affineSpan ℝ (F : Set (EuclSp n)) : Set (EuclSp n))) :
    (∀ C ∈ T.maximalCells, F ⊆ C → ∀ w ∈ C, 0 ≤ φ w) ∨
    (∀ C ∈ T.maximalCells, F ⊆ C → ∀ w ∈ C, φ w ≤ 0) := by
  sorry

/-- **Door incidence.** An interior `(n-1)`-face is a face of exactly two
maximal cells; a boundary `(n-1)`-face is a face of exactly one. -/
theorem door_incidence {n} (T : Triangulation n) {F : Finset (EuclSp n)}
    (hF : F ∈ T.facets) :
    (¬ (convexHull ℝ (F : Set (EuclSp n)) ⊆ frontier (cornerSimplex n)) →
        Nat.card {C // C ∈ T.maximalCells ∧ F ⊆ C} = 2) ∧
    ((convexHull ℝ (F : Set (EuclSp n)) ⊆ frontier (cornerSimplex n)) →
        Nat.card {C // C ∈ T.maximalCells ∧ F ⊆ C} = 1) := by
  sorry

/-- **The triangulation model is balanced.** -/
theorem triangulation_model_balanced {n} (T : Triangulation n) (ℓ : EuclSp n → Fin (n + 1))
    (hℓ : IsSpernerLabeling T ℓ) :
    (triangulationModel T ℓ).Balanced := by
  sorry

/-- **The induced bottom-facet restriction data.** `T'` (a triangulation of
`S_m`) is the restriction of `T` (a triangulation of `S_{m+1}`) to the bottom
facet `{x_{m+1} = 0}` along the affine embedding `e : E_m ↪ E_{m+1}` when:
`e` is an injective affine map carrying `S_m` isomorphically onto the bottom
facet, and the cells of `T'` are *exactly* the `e`-pullbacks of the cells of `T`
lying in that facet (a finset `C'` is a cell of `T'` iff its `e`-image is a cell
of `T`). The last condition pins `T'.cells` down uniquely in terms of `T.cells`
and `e`. -/
def IsFacetRestriction {m} (T : Triangulation (m + 1)) (T' : Triangulation m)
    (e : EuclSp m →ᵃ[ℝ] EuclSp (m + 1)) : Prop :=
  Function.Injective e ∧
  (∀ x, (e x) (Fin.last m) = 0) ∧
  e '' cornerSimplex m = {x ∈ cornerSimplex (m + 1) | x (Fin.last m) = 0} ∧
  (∀ C' : Finset (EuclSp m), C' ∈ T'.cells ↔ C'.image (e ·) ∈ T.cells)

/-- **The labeling induced on the bottom facet.** The label `ℓ' x` is the
`ℓ`-label of `e x` viewed in `Fin (m+1)` (the last label, which never occurs on
the bottom facet, is dropped to `0`). On facet vertices this is exactly the
restriction `ℓ ∘ e`. -/
noncomputable def inducedFacetLabeling {m} (ℓ : EuclSp (m + 1) → Fin (m + 2))
    (e : EuclSp m →ᵃ[ℝ] EuclSp (m + 1)) : EuclSp m → Fin (m + 1) :=
  fun x => if h : ℓ (e x) = Fin.last (m + 1) then 0 else (ℓ (e x)).castPred h

/-- **The bottom facet is a triangulation of `S_{m}`.** For `T` a triangulation
of `S_{m+1}`, the cells contained in `{x_{m+1} = 0}` are carried by an affine
injection `e : E_m ↪ E_{m+1}` onto the bottom facet of `S_{m+1}` and form a
triangulation `T'` of `S_m` — the induced restriction of `T`. -/
theorem facet_is_triangulation {m} (T : Triangulation (m + 1)) :
    ∃ (T' : Triangulation m) (e : EuclSp m →ᵃ[ℝ] EuclSp (m + 1)),
      IsFacetRestriction T T' e := by
  sorry

/-- **The restricted labeling is Sperner**, with all labels in `{0,…,m}`. For the
induced restriction `(T', e)` of `T`, the inherited labeling
`inducedFacetLabeling ℓ e` (i.e. `ℓ ∘ e` on facet vertices) is a Sperner
labeling of `T'`. -/
theorem facet_labeling_sperner {m} (T : Triangulation (m + 1))
    (ℓ : EuclSp (m + 1) → Fin (m + 2)) (hℓ : IsSpernerLabeling T ℓ)
    {T' : Triangulation m} {e : EuclSp m →ᵃ[ℝ] EuclSp (m + 1)}
    (he : IsFacetRestriction T T' e) :
    IsSpernerLabeling T' (inducedFacetLabeling ℓ e) := by
  sorry

/-- **Restriction to a boundary facet.** The faces of `T` in `{x_{m+1} = 0}`,
identified with `S_m` via the induced restriction `(T', e)`, form a triangulation
of `S_m` whose inherited labeling `inducedFacetLabeling ℓ e` is Sperner. -/
theorem facet_restriction {m} (T : Triangulation (m + 1))
    (ℓ : EuclSp (m + 1) → Fin (m + 2)) (hℓ : IsSpernerLabeling T ℓ) :
    ∃ (T' : Triangulation m) (e : EuclSp m →ᵃ[ℝ] EuclSp (m + 1)),
      IsFacetRestriction T T' e ∧
      IsSpernerLabeling T' (inducedFacetLabeling ℓ e) := by
  sorry

/-- **Boundary doors lie on the bottom facet.** Every boundary door of `T` lies
on the facet `{x_n = 0}`, i.e. all its vertices have last barycentric coordinate
zero. -/
theorem boundary_doors_bottom {n} (T : Triangulation n) (ℓ : EuclSp n → Fin (n + 1))
    (hℓ : IsSpernerLabeling T ℓ) {F : Finset (EuclSp n)} (hF : IsDoorFacet T ℓ F)
    (hbd : convexHull ℝ (F : Set (EuclSp n)) ⊆ frontier (cornerSimplex n)) :
    ∀ v ∈ F, baryCoord n v (Fin.last n) = 0 := by
  sorry

/-- **Bottom-facet doors are rainbow cells.** For the induced restriction
`(T', e)` of `T` with inherited labeling `inducedFacetLabeling ℓ e`, the doors of
`T` on `{x_{m+1} = 0}` correspond exactly (in number) to the rainbow maximal
cells of that induced Sperner-labeled triangulation of `S_m`. -/
theorem bottom_facet_doors_rainbow {m} (T : Triangulation (m + 1))
    (ℓ : EuclSp (m + 1) → Fin (m + 2)) (hℓ : IsSpernerLabeling T ℓ)
    {T' : Triangulation m} {e : EuclSp m →ᵃ[ℝ] EuclSp (m + 1)}
    (he : IsFacetRestriction T T' e) :
    Nat.card {F : Finset (EuclSp (m + 1)) //
        IsDoorFacet T ℓ F ∧ ∀ v ∈ F, baryCoord (m + 1) v (Fin.last (m + 1)) = 0}
      = Nat.card {C // IsRainbowCell T' (inducedFacetLabeling ℓ e) C} := by
  sorry

/-- **Boundary doors are the rainbow cells of the facet.** For the induced
restriction `(T', e)` of `T` with inherited labeling `inducedFacetLabeling ℓ e`,
the boundary doors of `T` are exactly (in number) the rainbow maximal cells of
that induced Sperner-labeled triangulation of `S_m` on `{x_{m+1} = 0}`. -/
theorem boundary_doors_facet {m} (T : Triangulation (m + 1))
    (ℓ : EuclSp (m + 1) → Fin (m + 2)) (hℓ : IsSpernerLabeling T ℓ)
    {T' : Triangulation m} {e : EuclSp m →ᵃ[ℝ] EuclSp (m + 1)}
    (he : IsFacetRestriction T T' e) :
    Nat.card {F : Finset (EuclSp (m + 1)) //
        IsDoorFacet T ℓ F ∧
          convexHull ℝ (F : Set (EuclSp (m + 1))) ⊆ frontier (cornerSimplex (m + 1))}
      = Nat.card {C // IsRainbowCell T' (inducedFacetLabeling ℓ e) C} := by
  sorry

/-- **Sperner's lemma.** Every Sperner-labeled triangulation of `S_n` has an odd
number of rainbow maximal cells; in particular at least one. -/
theorem sperner {n} (T : Triangulation n) (ℓ : EuclSp n → Fin (n + 1))
    (hℓ : IsSpernerLabeling T ℓ) :
    Odd (Nat.card {C // IsRainbowCell T ℓ C}) := by
  sorry

end Topology
end LeanEval
