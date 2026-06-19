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

/-- **Corner affine basis.** The points `0, e_1, …, e_n` are affinely
independent and affinely span `E_n`, so they form an
`AffineBasis (Fin (n+1)) ℝ E_n` whose underlying family is `cornerVertex`. -/
noncomputable def cornerBasis (n : ℕ) : AffineBasis (Fin (n + 1)) ℝ (EuclSp n) where
  toFun := cornerVertex n
  ind' := sorry
  tot' := sorry

/-- The standard corner simplex `S_n = convexHull {0, e_1, …, e_n} ⊆ E_n`. -/
def cornerSimplex (n : ℕ) : Set (EuclSp n) :=
  convexHull ℝ (Set.range (cornerVertex n))

/-- The barycentric coordinates of a point `p` relative to the corner vertices,
defined as Mathlib's affine-basis coordinate map: the `i`-th coordinate is
`(cornerBasis n).coord i p` (`AffineBasis.coord`). Each coordinate is an affine
functional `E_n → ℝ`, hence continuous, and they sum to `1`. -/
noncomputable def baryCoord (n : ℕ) (p : EuclSp n) : Fin (n + 1) → ℝ :=
  fun i => (cornerBasis n).coord i p

/-- The support `{ i : x_i > 0 }` of the barycentric coordinates of `p`. -/
noncomputable def carrierSupp (n : ℕ) (p : EuclSp n) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun i => 0 < baryCoord n p i)

/-- The **carrier face** of `p`: the closed face of `S_n` spanned by the corner
vertices indexed by `carrierSupp p`. -/
noncomputable def carrierFace (n : ℕ) (p : EuclSp n) : Set (EuclSp n) :=
  convexHull ℝ (cornerVertex n '' (carrierSupp n p : Set (Fin (n + 1))))

/-- **Membership by coordinates.** A point lies in `S_n` iff all of its
barycentric coordinates are nonnegative. -/
theorem mem_cornerSimplex_iff (n : ℕ) (p : EuclSp n) :
    p ∈ cornerSimplex n ↔ ∀ i, 0 ≤ baryCoord n p i := by
  sorry

/-- **Triangulation of the corner simplex `S_n`.** A *finite* geometric simplicial
complex (extending `Geometry.SimplicialComplex ℝ (EuclSp n)`, which already
supplies affine independence of faces, downward closure, and the face-to-face
property `conv C ∩ conv C' ⊆ conv (C ∩ C')`), together with two further axioms:
*purity* — every face is contained in a maximal cell with `n + 1` vertices — and
*covering* — the convex hulls of the maximal cells cover `S_n`.

The field `cells` is the finite `Finset` of faces (`mem_cells` records that it
coincides with the underlying complex's `faces` set). Maximal cells are the faces
with `n + 1` vertices and facets the faces with `n` vertices. Affine independence,
downward closure (`face_closed`), the dimension bound (`dim_le`), and the
face-to-face equality (`face_to_face`) are now *derived* lemmas rather than
re-rolled axioms. -/
structure Triangulation (n : ℕ) extends Geometry.SimplicialComplex ℝ (EuclSp n) where
  /-- The cells of the triangulation, as a finite set. -/
  cells : Finset (Finset (EuclSp n))
  /-- `cells` is exactly the face set of the underlying simplicial complex. -/
  mem_cells : ∀ C, C ∈ cells ↔ C ∈ toSimplicialComplex.faces
  /-- **Purity.** Every cell is contained in a maximal cell with `n + 1` vertices. -/
  purity : ∀ C ∈ cells, ∃ M ∈ cells, C ⊆ M ∧ M.card = n + 1
  /-- **Covering.** The maximal cells cover `S_n`. -/
  covering :
    (⋃ C ∈ cells.filter (fun C => C.card = n + 1), convexHull ℝ (C : Set (EuclSp n)))
      = cornerSimplex n

namespace Triangulation

variable {n : ℕ}

/-- The vertices of every cell are affinely independent (inherited from the
underlying simplicial complex). -/
theorem cell_indep (T : Triangulation n) {C : Finset (EuclSp n)} (hC : C ∈ T.cells) :
    AffineIndependent ℝ ((↑) : C → EuclSp n) :=
  T.toSimplicialComplex.indep ((T.mem_cells C).mp hC)

/-- **Downward closure.** Every nonempty subset of a cell is a cell (inherited
`Geometry.SimplicialComplex.down_closed`). -/
theorem face_closed (T : Triangulation n) {C : Finset (EuclSp n)} (hC : C ∈ T.cells)
    {D : Finset (EuclSp n)} (hD : D.Nonempty) (hDC : D ⊆ C) : D ∈ T.cells := by
  rw [T.mem_cells] at hC ⊢
  exact T.toSimplicialComplex.down_closed hC hDC hD

/-- **Dimension bound.** Every cell has at most `n + 1` vertices (a consequence of
purity). -/
theorem dim_le (T : Triangulation n) {C : Finset (EuclSp n)} (hC : C ∈ T.cells) :
    C.card ≤ n + 1 := by
  obtain ⟨M, _, hCM, hcard⟩ := T.purity C hC
  exact hcard ▸ Finset.card_le_card hCM

/-- **Face-to-face.** Two cells meet exactly along the convex hull of their common
vertices (the `⊆` inclusion is inherited, the `⊇` inclusion is monotonicity). -/
theorem face_to_face (T : Triangulation n) {C C' : Finset (EuclSp n)}
    (hC : C ∈ T.cells) (hC' : C' ∈ T.cells) :
    convexHull ℝ (C : Set (EuclSp n)) ∩ convexHull ℝ (C' : Set (EuclSp n))
      = convexHull ℝ ((C ∩ C' : Finset (EuclSp n)) : Set (EuclSp n)) := by
  apply le_antisymm
  · rw [Finset.coe_inter]
    exact T.toSimplicialComplex.inter_subset_convexHull
      ((T.mem_cells C).mp hC) ((T.mem_cells C').mp hC')
  · exact Set.subset_inter
      (convexHull_mono (Finset.coe_subset.mpr Finset.inter_subset_left))
      (convexHull_mono (Finset.coe_subset.mpr Finset.inter_subset_right))

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
  cellLabel_card C := by
    have hCcard : (C : Finset (EuclSp n)).card = n + 1 := by
      have hCmem : (C : Finset (EuclSp n)) ∈ T.maximalCells := C.2
      rcases Finset.mem_filter.mp hCmem with ⟨_, hcard⟩
      exact hcard
    calc
      (((C : Finset (EuclSp n)).val).map ℓ).card = ((C : Finset (EuclSp n)).val).card := by
        simp [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
      _ = (C : Finset (EuclSp n)).card := by simp [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
      _ = n + 1 := hCcard
  facetLabel_card F := by
    have hFcard : (F : Finset (EuclSp n)).card = n := by
      have hFmem : (F : Finset (EuclSp n)) ∈ T.facets := F.2
      rcases Finset.mem_filter.mp hFmem with ⟨_, hcard⟩
      exact hcard
    calc
      (((F : Finset (EuclSp n)).val).map ℓ).card = ((F : Finset (EuclSp n)).val).card := by
        simp [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
      _ = (F : Finset (EuclSp n)).card := by simp [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
      _ = n := hFcard
  compat C F h := by
    have hsub : (F : Finset (EuclSp n)) ⊆ (C : Finset (EuclSp n)) := h
    have hCcard : (C : Finset (EuclSp n)).card = n + 1 := by
      have hCmem : (C : Finset (EuclSp n)) ∈ T.maximalCells := C.2
      rcases Finset.mem_filter.mp hCmem with ⟨_, hcard⟩
      exact hcard
    have hFcard : (F : Finset (EuclSp n)).card = n := by
      have hFmem : (F : Finset (EuclSp n)) ∈ T.facets := F.2
      rcases Finset.mem_filter.mp hFmem with ⟨_, hcard⟩
      exact hcard
    have hcard_sdiff : ((C : Finset (EuclSp n)) \ (F : Finset (EuclSp n))).card = 1 := by
      have h := Finset.card_sdiff_add_card_eq_card hsub
      rw [hFcard, hCcard] at h
      omega
    rcases (Finset.card_eq_one.mp hcard_sdiff) with ⟨v, hv⟩
    have hv_mem : v ∈ (C : Finset (EuclSp n)) := by
      have hmem_sdiff : v ∈ (C : Finset (EuclSp n)) \ (F : Finset (EuclSp n)) := by
        simp [hv]
      exact Finset.mem_sdiff.mp hmem_sdiff |>.left
    have h_val_sub : (F : Finset (EuclSp n)).val ≤ (C : Finset (EuclSp n)).val :=
      Finset.val_le_iff.mpr hsub
    have hCval_eq : (C : Finset (EuclSp n)).val = (F : Finset (EuclSp n)).val + ({v} : Multiset (EuclSp n)) := by
      have htemp : (C : Finset (EuclSp n)).val = ((C : Finset (EuclSp n)) \ (F : Finset (EuclSp n))).val + (F : Finset (EuclSp n)).val := by
        calc
          (C : Finset (EuclSp n)).val
              = ((C : Finset (EuclSp n)).val - (F : Finset (EuclSp n)).val) + (F : Finset (EuclSp n)).val := by
                symm; exact Multiset.add_sub_cancel h_val_sub
          _ = ((C : Finset (EuclSp n)) \ (F : Finset (EuclSp n))).val + (F : Finset (EuclSp n)).val := by
            simp [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
      calc
        (C : Finset (EuclSp n)).val
            = ((C : Finset (EuclSp n)) \ (F : Finset (EuclSp n))).val + (F : Finset (EuclSp n)).val := htemp
        _ = ({v} : Multiset (EuclSp n)) + (F : Finset (EuclSp n)).val := by
          simp [hv]
        _ = (F : Finset (EuclSp n)).val + ({v} : Multiset (EuclSp n)) := by
          rw [Multiset.add_comm]
    have hcell_map : (((C : Finset (EuclSp n)).val).map ℓ) = (((F : Finset (EuclSp n)).val).map ℓ) + ({ℓ v} : Multiset (Fin (n + 1))) := by
      calc
        (((C : Finset (EuclSp n)).val).map ℓ) = (((F : Finset (EuclSp n)).val + ({v} : Multiset (EuclSp n))).map ℓ) := by
          rw [hCval_eq]
        _ = (((F : Finset (EuclSp n)).val).map ℓ) + (({v} : Multiset (EuclSp n)).map ℓ) := by
          rw [Multiset.map_add]
        _ = (((F : Finset (EuclSp n)).val).map ℓ) + ({ℓ v} : Multiset (Fin (n + 1))) := by
          simp [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
    refine ⟨ℓ v, ?_⟩
    calc
      ((F : Finset (EuclSp n)).val).map ℓ
          = ((F : Finset (EuclSp n)).val).map ℓ + 0 := by simp [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
      _ = ((F : Finset (EuclSp n)).val).map ℓ + (({ℓ v} : Multiset (Fin (n + 1))).erase (ℓ v)) := by
        simp [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
      _ = (((F : Finset (EuclSp n)).val).map ℓ + ({ℓ v} : Multiset (Fin (n + 1)))).erase (ℓ v) := by
        rw [Multiset.erase_add_right_pos _ (by simp : ℓ v ∈ ({ℓ v} : Multiset (Fin (n + 1))))]
      _ = (((C : Finset (EuclSp n)).val).map ℓ).erase (ℓ v) := by
        rw [hcell_map]
  mult C a := by
    -- The facets incident to a maximal cell `C` biject with its vertices: each
    -- vertex `v ∈ C` gives the facet `C \ {v}`, whose label multiset is
    -- `(cellLabel C).erase (ℓ v)`. Hence the facets with label `(cellLabel C).erase a`
    -- are those obtained by deleting a vertex labeled `a`, and their number is the
    -- multiplicity `(cellLabel C).count a` of `a` among the vertex labels of `C`.
    sorry

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

/-- **Door incidence.** An interior `(n-1)`-face is a face of exactly two
maximal cells; a boundary `(n-1)`-face is a face of exactly one. -/
theorem door_incidence {n} (T : Triangulation n) {F : Finset (EuclSp n)}
    (hF : F ∈ T.facets) :
    (¬ (convexHull ℝ (F : Set (EuclSp n)) ⊆ frontier (cornerSimplex n)) →
        Nat.card {C // C ∈ T.maximalCells ∧ F ⊆ C} = 2) ∧
    ((convexHull ℝ (F : Set (EuclSp n)) ⊆ frontier (cornerSimplex n)) →
        Nat.card {C // C ∈ T.maximalCells ∧ F ⊆ C} = 1) := by
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
  classical
  -- door_incidence tells us there are exactly two maximal cells containing F
  have h_card := (door_incidence T hF).1 hint
  -- h_card : Nat.card {C // C ∈ T.maximalCells ∧ F ⊆ C} = 2
  have h_filter_card_eq : (T.maximalCells.filter (fun C => F ⊆ C)).card =
    Nat.card {C // C ∈ T.maximalCells ∧ F ⊆ C} :=
    (Nat.subtype_card (T.maximalCells.filter (fun C => F ⊆ C)) (by
      intro C; simp [Finset.mem_filter])).symm
  have h_cardS : (T.maximalCells.filter (fun C => F ⊆ C)).card = 2 := by
    rw [h_filter_card_eq, h_card]
  -- card = 2 gives two distinct cells
  rcases Finset.card_eq_two.mp h_cardS with ⟨C₁, C₂, hne, hS⟩
  have hC₁mem : C₁ ∈ T.maximalCells.filter (fun C => F ⊆ C) := by
    rw [hS]; simp [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  have hC₁max : C₁ ∈ T.maximalCells := (Finset.mem_filter.mp hC₁mem).1
  have hC₁F : F ⊆ C₁ := (Finset.mem_filter.mp hC₁mem).2
  have hC₂mem : C₂ ∈ T.maximalCells.filter (fun C => F ⊆ C) := by
    rw [hS]; simp [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  have hC₂max : C₂ ∈ T.maximalCells := (Finset.mem_filter.mp hC₂mem).1
  have hC₂F : F ⊆ C₂ := (Finset.mem_filter.mp hC₂mem).2
  -- the two cells lie on opposite sides of the hyperplane
  have h_opposite : ∃ w ∈ C₁, ∃ w' ∈ C₂, φ w * φ w' < 0 :=
    one_cell_per_side T hF φ hφ hker hC₁max hC₂max hC₁F hC₂F hne
  rcases h_opposite with ⟨w₁, hw₁, w₂, hw₂, hprod⟩
  have h_one_pos_one_neg : (0 < φ w₁ ∧ φ w₂ < 0) ∨ (0 < φ w₂ ∧ φ w₁ < 0) := by
    have h₁0 : φ w₁ ≠ 0 := by
      intro hz; rw [hz, zero_mul] at hprod; linarith
    have h₂0 : φ w₂ ≠ 0 := by
      intro hz; rw [hz, mul_zero] at hprod; linarith
    by_cases h₁pos : 0 < φ w₁
    · have h₂neg : φ w₂ < 0 := by
        by_contra! hge
        nlinarith
      exact Or.inl ⟨h₁pos, h₂neg⟩
    · have h₁neg : φ w₁ < 0 := by
        by_contra! hge
        -- hge : φ w₁ ≥ 0
        have hle : φ w₁ ≤ 0 := by linarith
        have h_eq : φ w₁ = 0 := by linarith
        exact h₁0 h_eq
      have h₂pos : 0 < φ w₂ := by
        by_contra! hle
        nlinarith
      exact Or.inr ⟨h₂pos, h₁neg⟩
  rcases h_one_pos_one_neg with ((⟨hpos₁, hneg₂⟩) | (⟨hpos₂, hneg₁⟩))
  · exact ⟨⟨C₁, hC₁max, hC₁F, w₁, hw₁, hpos₁⟩, ⟨C₂, hC₂max, hC₂F, w₂, hw₂, hneg₂⟩⟩
  · exact ⟨⟨C₂, hC₂max, hC₂F, w₂, hw₂, hpos₂⟩, ⟨C₁, hC₁max, hC₁F, w₁, hw₁, hneg₁⟩⟩

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

/-- **The triangulation model is balanced.** -/
theorem triangulation_model_balanced {n} (T : Triangulation n) (ℓ : EuclSp n → Fin (n + 1))
    (hℓ : IsSpernerLabeling T ℓ) :
    (triangulationModel T ℓ).Balanced := by
  let M := triangulationModel T ℓ
  dsimp [IncidenceModel.Balanced]
  constructor
  · intro F hF_not_bdry
    have hF_mem : F.val ∈ T.facets := F.property
    have h_card_eq : Nat.card {C : M.Cell // M.Inc C F} =
      Nat.card {C // C ∈ T.maximalCells ∧ F.val ⊆ C} := by
      apply Nat.card_congr
      refine {
        toFun := λ ⟨⟨C, hC⟩, hsub⟩ => ⟨C, hC, hsub⟩
        invFun := λ ⟨C, hC, hsub⟩ => ⟨⟨C, hC⟩, hsub⟩
        left_inv := by
          intro x; rcases x with ⟨⟨C, hC⟩, hsub⟩; rfl
        right_inv := by
          intro x; rcases x with ⟨C, hC, hsub⟩; rfl
      }
    rw [h_card_eq]
    have h_not_bdry : ¬ (convexHull ℝ ((F.val : Set (EuclSp n))) ⊆ frontier (cornerSimplex n)) :=
      hF_not_bdry
    have h_door := door_incidence T hF_mem
    exact h_door.1 h_not_bdry
  · intro F hF_bdry
    have hF_mem : F.val ∈ T.facets := F.property
    have h_card_eq : Nat.card {C : M.Cell // M.Inc C F} =
      Nat.card {C // C ∈ T.maximalCells ∧ F.val ⊆ C} := by
      apply Nat.card_congr
      refine {
        toFun := λ ⟨⟨C, hC⟩, hsub⟩ => ⟨C, hC, hsub⟩
        invFun := λ ⟨C, hC, hsub⟩ => ⟨⟨C, hC⟩, hsub⟩
        left_inv := by
          intro x; rcases x with ⟨⟨C, hC⟩, hsub⟩; rfl
        right_inv := by
          intro x; rcases x with ⟨C, hC, hsub⟩; rfl
      }
    rw [h_card_eq]
    have h_bdry : convexHull ℝ ((F.val : Set (EuclSp n))) ⊆ frontier (cornerSimplex n) :=
      hF_bdry
    have h_door := door_incidence T hF_mem
    exact h_door.2 h_bdry

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
  rcases facet_is_triangulation T with ⟨T', e, he⟩
  refine ⟨T', e, he, ?_⟩
  exact facet_labeling_sperner T ℓ hℓ he

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
