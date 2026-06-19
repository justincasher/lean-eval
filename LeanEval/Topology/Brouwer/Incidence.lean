import Mathlib

/-!
# Abstract Sperner combinatorics

Section 2 of the Brouwer blueprint: the finite combinatorics of Sperner's lemma,
developed over an abstract axiomatized labeled incidence model with no geometry.
-/

namespace LeanEval
namespace Topology

open scoped BigOperators

/-- **Abstract labeled incidence model** of dimension `n`: finite types of cells
and facets, an incidence relation, a boundary predicate, and label multisets of
sizes `n+1` (cells) and `n` (facets), with the compatibility axiom that an
incident facet's labels are obtained from its cell's labels by deleting one. -/
structure IncidenceModel (n : ℕ) where
  /-- The (finite) type of cells. -/
  Cell : Type
  /-- The (finite) type of facets. -/
  Facet : Type
  [cellFintype : Fintype Cell]
  [facetFintype : Fintype Facet]
  /-- Incidence relation between cells and facets. -/
  Inc : Cell → Facet → Prop
  /-- Boundary predicate on facets. -/
  bdry : Facet → Prop
  /-- The label multiset of a cell (`n+1` labels from `{0,…,n}`). -/
  cellLabel : Cell → Multiset (Fin (n + 1))
  /-- The label multiset of a facet (`n` labels from `{0,…,n}`). -/
  facetLabel : Facet → Multiset (Fin (n + 1))
  cellLabel_card : ∀ C, (cellLabel C).card = n + 1
  facetLabel_card : ∀ F, (facetLabel F).card = n
  compat : ∀ C F, Inc C F → ∃ a, facetLabel F = (cellLabel C).erase a

attribute [instance] IncidenceModel.cellFintype IncidenceModel.facetFintype

namespace IncidenceModel

variable {n : ℕ} (M : IncidenceModel n)

/-- A facet is a **door** if its label multiset is exactly `{0,…,n-1}` (each
label once), i.e. all of `Fin (n+1)` except the last label. -/
def IsDoor (F : M.Facet) : Prop :=
  M.facetLabel F = (Finset.univ.erase (Fin.last n)).val

/-- A cell is **rainbow** if its label multiset is exactly `{0,…,n}` (each label
once). -/
def IsRainbow (C : M.Cell) : Prop :=
  M.cellLabel C = (Finset.univ : Finset (Fin (n + 1))).val

/-- A model is **balanced** if every interior facet (`¬ bdry`) is incident to
exactly two cells and every boundary facet (`bdry`) to exactly one cell. -/
def Balanced : Prop :=
  (∀ F, ¬ M.bdry F → Nat.card {C // M.Inc C F} = 2) ∧
  (∀ F, M.bdry F → Nat.card {C // M.Inc C F} = 1)

end IncidenceModel

/-- **Rainbow cells have exactly one door.** -/
theorem cell_door_rainbow {n} (M : IncidenceModel n) (C : M.Cell) (h : M.IsRainbow C) :
    Nat.card {F // M.Inc C F ∧ M.IsDoor F} = 1 := by
  sorry

/-- **Non-rainbow cells have an even number of doors.** -/
theorem cell_door_nonrainbow {n} (M : IncidenceModel n) (C : M.Cell) (h : ¬ M.IsRainbow C) :
    Even (Nat.card {F // M.Inc C F ∧ M.IsDoor F}) := by
  sorry

/-- **Per-cell door parity.** The number of doors incident to a cell is odd iff
the cell is rainbow. -/
theorem cell_door_count {n} (M : IncidenceModel n) (C : M.Cell) :
    Odd (Nat.card {F // M.Inc C F ∧ M.IsDoor F}) ↔ M.IsRainbow C := by
  sorry

/-- **Door count has rainbow parity.** The total number of incident (cell, door)
pairs has the same parity as the number of rainbow cells. -/
theorem door_count_rainbow_parity {n} (M : IncidenceModel n) :
    (∑ C : M.Cell, Nat.card {F // M.Inc C F ∧ M.IsDoor F}) ≡
      Nat.card {C // M.IsRainbow C} [MOD 2] := by
  sorry

/-- **Door count via incidence.** In a balanced model the total incidence count
equals `2 · #(interior doors) + #(boundary doors)`. -/
theorem door_count_incidence {n} (M : IncidenceModel n) (h : M.Balanced) :
    (∑ C : M.Cell, Nat.card {F // M.Inc C F ∧ M.IsDoor F})
      = 2 * Nat.card {F // M.IsDoor F ∧ ¬ M.bdry F}
        + Nat.card {F // M.IsDoor F ∧ M.bdry F} := by
  sorry

/-- **Boundary parity count.** In a balanced model, the number of rainbow cells
has the same parity as the number of boundary doors. -/
theorem sperner_parity {n} (M : IncidenceModel n) (h : M.Balanced) :
    Nat.card {C // M.IsRainbow C} ≡ Nat.card {F // M.IsDoor F ∧ M.bdry F} [MOD 2] := by
  sorry

end Topology
end LeanEval
