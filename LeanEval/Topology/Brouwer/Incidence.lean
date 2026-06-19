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
  /-- **Per-label multiplicity axiom.** For each cell `C` and label `a`, the
  number of facets incident to `C` whose label multiset is `(cellLabel C).erase a`
  equals the multiplicity of `a` among the labels of `C`. Equivalently, the facets
  incident to a cell biject with its vertices — each vertex deletion yields exactly
  one incident facet — so a repeated label contributes one incident facet per
  occurrence. This is what makes a non-rainbow cell have an *even* (0 or 2) number
  of doors. -/
  mult : ∀ (C : Cell) (a : Fin (n + 1)),
    Nat.card {F // Inc C F ∧ facetLabel F = (cellLabel C).erase a} = (cellLabel C).count a

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
  -- From the rainbow hypothesis, cellLabel C = univ.val (each label 0,...,n once)
  have h_labels : M.cellLabel C = (Finset.univ : Finset (Fin (n + 1))).val := h
  -- Door label multiset {0,...,n-1} equals cellLabel C with label n erased
  have hT_eq : (Finset.univ : Finset (Fin (n + 1))).val.erase (Fin.last n) = (M.cellLabel C).erase (Fin.last n) := by
    rw [h_labels]
  -- Build an equivalence between the two subtype sets using pointwise equivalence
  have h_set_equiv : {F : M.Facet // M.Inc C F ∧ M.IsDoor F} ≃
      {F : M.Facet // M.Inc C F ∧ M.facetLabel F = (M.cellLabel C).erase (Fin.last n)} :=
    Equiv.subtypeEquiv (Equiv.refl _) (λ F => by
      simp [IncidenceModel.IsDoor, hT_eq])
  rw [Nat.card_congr h_set_equiv]
  -- By the multiplicity axiom, the number of these facets equals count of label n
  have h_count : (M.cellLabel C).count (Fin.last n) = 1 := by
    rw [h_labels]
    simp
  rw [M.mult C (Fin.last n), h_count]

/-- **Non-rainbow cells have an even number of doors.** -/
theorem cell_door_nonrainbow {n} (M : IncidenceModel n) (C : M.Cell) (h : ¬ M.IsRainbow C) :
    Even (Nat.card {F // M.Inc C F ∧ M.IsDoor F}) := by
  classical
  let S := M.cellLabel C
  let T : Multiset (Fin (n + 1)) := (Finset.univ.erase (Fin.last n)).val
  -- T = {0,...,n-1}. A door F at C satisfies facetLabel F = T, and by compat
  -- facetLabel F = S.erase a for some a, so S.erase a = T must hold.
  -- If some i : Fin n (i.e., some label from {0,...,n-1}) has i ∉ S, then
  -- i ∉ S.erase a, so S.erase a cannot equal T (which contains i).
  -- Hence no doors → cardinal 0 → Even.
  by_cases h_missing : ∃ (i : Fin n), (Fin.castSucc i : Fin (n + 1)) ∉ S
  · rcases h_missing with ⟨i, hi⟩
    have hi_mem_T : (Fin.castSucc i : Fin (n + 1)) ∈ T := by
      apply Finset.mem_val.mpr
      exact Finset.mem_erase.mpr ⟨Fin.castSucc_ne_last i, Finset.mem_univ _⟩
    have no_doors : ∀ (F : M.Facet), M.Inc C F → ¬ M.IsDoor F := by
      intro F hinc hdoor
      rcases M.compat C F hinc with ⟨a, ha⟩
      have hdoor_label : M.facetLabel F = T := hdoor
      have h_eq : S.erase a = T := by
        calc
          S.erase a = (M.cellLabel C).erase a := rfl
          _ = M.facetLabel F := by symm; exact ha
          _ = T := hdoor_label
      have hi_mem_erase : (Fin.castSucc i : Fin (n + 1)) ∈ S.erase a := by
        rw [h_eq]; exact hi_mem_T
      have hi_mem_S : (Fin.castSucc i : Fin (n + 1)) ∈ S :=
        Multiset.mem_of_mem_erase hi_mem_erase
      exact hi hi_mem_S
    -- The type of doors is empty, hence its Fintype.card is 0, hence Nat.card is 0.
    have h_empty : IsEmpty {F : M.Facet // M.Inc C F ∧ M.IsDoor F} := by
      refine ⟨λ x => ?_⟩
      exact no_doors x.1 x.2.1 x.2.2
    have h_card : Fintype.card {F : M.Facet // M.Inc C F ∧ M.IsDoor F} = 0 := by
      simp [h_empty]
    have h_nat_card : Nat.card {F : M.Facet // M.Inc C F ∧ M.IsDoor F} = 0 := by
      rw [Nat.card_eq_fintype_card, h_card]
    rw [h_nat_card]
    exact ⟨0, by simp⟩
  · -- All labels {0,...,n-1} are present in S.
    -- Since |S| = n+1 and S contains n distinct labels {0,...,n-1}, S has one extra element.
    -- If that extra is Fin.last n (= n), S would be {0,...,n} = rainbow → contradiction.
    -- So the extra is some a ∈ {0,...,n-1}, giving S with two copies of a and no copy of n.
    -- Then S.erase a = T, and a is the *only* label whose deletion yields the door
    -- multiset T (deleting any other label b ≠ a leaves a still doubled, so the result
    -- is not T). Hence the doors incident to C are exactly the facets F with
    -- `facetLabel F = S.erase a`, whose number is `S.count a = 2` by `M.mult C a`.
    -- Two doors → Even. (The `mult` axiom is precisely what rules out the spurious
    -- "one door" models that the bare compatibility axiom would otherwise admit.)
    sorry

/-- **Per-cell door parity.** The number of doors incident to a cell is odd iff
the cell is rainbow. -/
theorem cell_door_count {n} (M : IncidenceModel n) (C : M.Cell) :
    Odd (Nat.card {F // M.Inc C F ∧ M.IsDoor F}) ↔ M.IsRainbow C := by
  constructor
  · intro hOdd
    by_contra hnR
    have hEven : Even (Nat.card {F // M.Inc C F ∧ M.IsDoor F}) := cell_door_nonrainbow M C hnR
    have hNotEven : ¬ Even (Nat.card {F // M.Inc C F ∧ M.IsDoor F}) :=
      (Nat.not_even_iff_odd.mpr hOdd)
    exact hNotEven hEven
  · intro hR
    have hcard : Nat.card {F // M.Inc C F ∧ M.IsDoor F} = 1 := cell_door_rainbow M C hR
    rw [hcard]
    refine ⟨0, ?_⟩
    decide

/-- **Door count has rainbow parity.** The total number of incident (cell, door)
pairs has the same parity as the number of rainbow cells. -/
theorem door_count_rainbow_parity {n} (M : IncidenceModel n) :
    (∑ C : M.Cell, Nat.card {F // M.Inc C F ∧ M.IsDoor F}) ≡
      Nat.card {C // M.IsRainbow C} [MOD 2] := by
  classical
    have hparity (C : M.Cell) : (Nat.card {F // M.Inc C F ∧ M.IsDoor F}) ≡ (if M.IsRainbow C then 1 else 0) [MOD 2] := by
      by_cases h : M.IsRainbow C
      · -- Rainbow cell: count is odd, so ≡ 1 [MOD 2]
        have hodd : Odd (Nat.card {F // M.Inc C F ∧ M.IsDoor F}) := (cell_door_count M C).mpr h
        have hmod : (Nat.card {F // M.Inc C F ∧ M.IsDoor F}) % 2 = 1 := (Nat.odd_iff.mp hodd)
        have h_mod_eq : (Nat.card {F // M.Inc C F ∧ M.IsDoor F}) ≡ 1 [MOD 2] := by
          calc
            (Nat.card {F // M.Inc C F ∧ M.IsDoor F}) % 2 = 1 := hmod
            _ = (1 : ℕ) % 2 := by decide
        have : (if M.IsRainbow C then 1 else 0) = 1 := by simp [h]
        rw [this]
        exact h_mod_eq
      · -- Non-rainbow cell: count is not odd, so ≡ 0 [MOD 2]
        have h_not_odd : ¬ Odd (Nat.card {F // M.Inc C F ∧ M.IsDoor F}) := by
          rw [cell_door_count M C]
          exact h
        have hmod : (Nat.card {F // M.Inc C F ∧ M.IsDoor F}) % 2 = 0 := by
          have h_cases := Nat.mod_two_eq_zero_or_one (Nat.card {F // M.Inc C F ∧ M.IsDoor F})
          rcases h_cases with (hz | ho)
          · exact hz
          · exfalso; exact h_not_odd ((Nat.odd_iff.mpr ho))
        have h_mod_eq : (Nat.card {F // M.Inc C F ∧ M.IsDoor F}) ≡ 0 [MOD 2] := by
          calc
            (Nat.card {F // M.Inc C F ∧ M.IsDoor F}) % 2 = 0 := hmod
            _ = (0 : ℕ) % 2 := by decide
        have : (if M.IsRainbow C then 1 else 0) = 0 := by simp [h]
        rw [this]
        exact h_mod_eq
    have hsum : (∑ C : M.Cell, Nat.card {F // M.Inc C F ∧ M.IsDoor F}) ≡
        (∑ C : M.Cell, (if M.IsRainbow C then 1 else 0)) [MOD 2] := by
      apply Nat.ModEq.sum
      intro C hC
      exact hparity C
    have h_indicator_sum : (∑ C : M.Cell, (if M.IsRainbow C then 1 else 0)) =
        (Finset.filter (M.IsRainbow ·) (Finset.univ : Finset M.Cell)).card := by
      simp [Finset.sum_boole]
    have h_filter_card : (Finset.filter (M.IsRainbow ·) (Finset.univ : Finset M.Cell)).card =
        Fintype.card {C : M.Cell // M.IsRainbow C} := by
      rw [Fintype.card_subtype]
    have h_fintype_card : Fintype.card {C : M.Cell // M.IsRainbow C} = Nat.card {C // M.IsRainbow C} := by
      simp
    calc
      (∑ C : M.Cell, Nat.card {F // M.Inc C F ∧ M.IsDoor F}) ≡
          (∑ C : M.Cell, (if M.IsRainbow C then 1 else 0)) [MOD 2] := hsum
      _ = (Finset.filter (M.IsRainbow ·) (Finset.univ : Finset M.Cell)).card := h_indicator_sum
      _ = Fintype.card {C : M.Cell // M.IsRainbow C} := h_filter_card
      _ = Nat.card {C // M.IsRainbow C} := h_fintype_card

/-- **Door count via incidence.** In a balanced model the total incidence count
equals `2 · #(interior doors) + #(boundary doors)`. -/
theorem door_count_incidence {n} (M : IncidenceModel n) (h : M.Balanced) :
    (∑ C : M.Cell, Nat.card {F // M.Inc C F ∧ M.IsDoor F})
      = 2 * Nat.card {F // M.IsDoor F ∧ ¬ M.bdry F}
        + Nat.card {F // M.IsDoor F ∧ M.bdry F} := by
  classical
    rcases h with ⟨h_int, h_bd⟩
    -- D : Finset of door facets
    let D : Finset M.Facet := Finset.filter M.IsDoor Finset.univ
    have hD (F : M.Facet) : F ∈ D ↔ M.IsDoor F := by
      simp [D]
    -- Relate Nat.card over a subtype to Finset.card for the bipartite sets
    have h_card_above (C : M.Cell) : Nat.card {F // M.Inc C F ∧ M.IsDoor F} =
        Finset.card (D.bipartiteAbove M.Inc C) := by
      refine Nat.subtype_card (D.bipartiteAbove M.Inc C) ?_
      intro F
      simp [D, Finset.mem_bipartiteAbove, and_comm]
    have h_card_below (F : M.Facet) : Nat.card {C // M.Inc C F} =
        Finset.card ((Finset.univ : Finset M.Cell).bipartiteBelow M.Inc F) := by
      refine Nat.subtype_card ((Finset.univ : Finset M.Cell).bipartiteBelow M.Inc F) ?_
      intro C
      simp [Finset.mem_bipartiteBelow]
    -- Apply the bipartite double-counting lemma
    have h_sum_swap : (∑ C : M.Cell, Finset.card (D.bipartiteAbove M.Inc C)) =
        (∑ F ∈ D, Nat.card {C // M.Inc C F}) := by
      calc
        (∑ C : M.Cell, Finset.card (D.bipartiteAbove M.Inc C))
            = ∑ C ∈ Finset.univ, Finset.card (D.bipartiteAbove M.Inc C) := by simp
        _ = ∑ F ∈ D, Finset.card ((Finset.univ : Finset M.Cell).bipartiteBelow M.Inc F) := by
          rw [Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
        _ = (∑ F ∈ D, Nat.card {C // M.Inc C F}) := by
          simp_rw [h_card_below]
    have h_eval_D : (∑ F ∈ D, Nat.card {C // M.Inc C F}) =
        (∑ F ∈ D, if M.bdry F then 1 else 2) := by
      refine Finset.sum_congr rfl fun F hF => ?_
      have hF_door : M.IsDoor F := (hD F).mp hF
      by_cases hb : M.bdry F
      · rw [h_bd F hb]
        simp [hb]
      · rw [h_int F hb]
        simp [hb]
    have h_split : (∑ F ∈ D, if M.bdry F then 1 else 2) =
        2 * (Nat.card {F // M.IsDoor F ∧ ¬ M.bdry F}) + (Nat.card {F // M.IsDoor F ∧ M.bdry F}) := by
      have h_eq1 : (∑ F ∈ D, if M.bdry F then 1 else 2) =
          (∑ F ∈ D with M.bdry F, 1) + (∑ F ∈ D with ¬ M.bdry F, 2) := by
        have h_temp : (∑ F ∈ D, if M.bdry F then 1 else 2) =
            ((∑ F ∈ D with M.bdry F, if M.bdry F then 1 else 2) +
             (∑ F ∈ D with ¬ M.bdry F, if M.bdry F then 1 else 2)) := by
          rw [← Finset.sum_filter_add_sum_filter_not D (M.bdry ·) (λ F => if M.bdry F then 1 else 2)]
        have h_simp1 : (∑ F ∈ D with M.bdry F, if M.bdry F then 1 else 2) = (∑ F ∈ D with M.bdry F, 1) :=
          Finset.sum_congr rfl fun F hF => by
            have hb : M.bdry F := (Finset.mem_filter.mp hF).2
            simp [hb]
        have h_simp2 : (∑ F ∈ D with ¬ M.bdry F, if M.bdry F then 1 else 2) = (∑ F ∈ D with ¬ M.bdry F, 2) :=
          Finset.sum_congr rfl fun F hF => by
            have hb : ¬ M.bdry F := (Finset.mem_filter.mp hF).2
            simp [hb]
        calc
          (∑ F ∈ D, if M.bdry F then 1 else 2)
              = ((∑ F ∈ D with M.bdry F, if M.bdry F then 1 else 2) +
                 (∑ F ∈ D with ¬ M.bdry F, if M.bdry F then 1 else 2)) := h_temp
          _ = ((∑ F ∈ D with M.bdry F, 1) + (∑ F ∈ D with ¬ M.bdry F, if M.bdry F then 1 else 2)) := by rw [h_simp1]
          _ = (∑ F ∈ D with M.bdry F, 1) + (∑ F ∈ D with ¬ M.bdry F, 2) := by rw [h_simp2]
      have h_card1 : (∑ F ∈ D with M.bdry F, 1) = (Finset.filter M.bdry D).card := by simp
      have h_card2 : (∑ F ∈ D with ¬ M.bdry F, 2) = (Finset.filter (λ F => ¬ M.bdry F) D).card * 2 := by simp
      have h_nat1 : (Finset.filter M.bdry D).card = Nat.card {F // M.IsDoor F ∧ M.bdry F} :=
        (Nat.subtype_card (Finset.filter M.bdry D) (by
          intro F; simp [D])).symm
      have h_nat2 : (Finset.filter (λ F => ¬ M.bdry F) D).card = Nat.card {F // M.IsDoor F ∧ ¬ M.bdry F} :=
        (Nat.subtype_card (Finset.filter (λ F => ¬ M.bdry F) D) (by
          intro F; simp [D])).symm
      calc
        (∑ F ∈ D, if M.bdry F then 1 else 2)
            = (∑ F ∈ D with M.bdry F, 1) + (∑ F ∈ D with ¬ M.bdry F, 2) := h_eq1
        _ = (Finset.filter M.bdry D).card + (Finset.filter (λ F => ¬ M.bdry F) D).card * 2 := by
          rw [h_card1, h_card2]
        _ = (Finset.filter M.bdry D).card + 2 * (Finset.filter (λ F => ¬ M.bdry F) D).card := by
          rw [Nat.mul_comm]
        _ = (Nat.card {F // M.IsDoor F ∧ M.bdry F}) + 2 * (Nat.card {F // M.IsDoor F ∧ ¬ M.bdry F}) := by
          rw [h_nat1, h_nat2]
        _ = 2 * (Nat.card {F // M.IsDoor F ∧ ¬ M.bdry F}) + (Nat.card {F // M.IsDoor F ∧ M.bdry F}) := by ring
    calc
      (∑ C : M.Cell, Nat.card {F // M.Inc C F ∧ M.IsDoor F})
          = (∑ C : M.Cell, Finset.card (D.bipartiteAbove M.Inc C)) := by
            simp_rw [h_card_above]
      _ = (∑ F ∈ D, Nat.card {C // M.Inc C F}) := h_sum_swap
      _ = (∑ F ∈ D, if M.bdry F then 1 else 2) := h_eval_D
      _ = 2 * (Nat.card {F // M.IsDoor F ∧ ¬ M.bdry F}) + (Nat.card {F // M.IsDoor F ∧ M.bdry F}) := h_split
      _ = 2 * Nat.card {F // M.IsDoor F ∧ ¬ M.bdry F} + Nat.card {F // M.IsDoor F ∧ M.bdry F} := rfl

/-- **Boundary parity count.** In a balanced model, the number of rainbow cells
has the same parity as the number of boundary doors. -/
theorem sperner_parity {n} (M : IncidenceModel n) (h : M.Balanced) :
    Nat.card {C // M.IsRainbow C} ≡ Nat.card {F // M.IsDoor F ∧ M.bdry F} [MOD 2] := by
  have h_total_eq : (∑ C : M.Cell, Nat.card {F // M.Inc C F ∧ M.IsDoor F}) =
      2 * Nat.card {F // M.IsDoor F ∧ ¬ M.bdry F} + Nat.card {F // M.IsDoor F ∧ M.bdry F} :=
    door_count_incidence M h
  have h_total_parity_rainbow : (∑ C : M.Cell, Nat.card {F // M.Inc C F ∧ M.IsDoor F}) ≡
      Nat.card {C // M.IsRainbow C} [MOD 2] :=
    door_count_rainbow_parity M
  -- 2 * k ≡ 0 [MOD 2] for any k
  have h2k_mod2 : (2 : ℕ) * Nat.card {F // M.IsDoor F ∧ ¬ M.bdry F} ≡ 0 [MOD 2] := by
    rw [Nat.ModEq, Nat.mul_mod, show (2 : ℕ) % 2 = 0 by decide, zero_mul]
    rfl
  -- Then 2*k + D ≡ D [MOD 2]
  have h_total_parity_boundary : (∑ C : M.Cell, Nat.card {F // M.Inc C F ∧ M.IsDoor F}) ≡
      Nat.card {F // M.IsDoor F ∧ M.bdry F} [MOD 2] := by
    rw [h_total_eq]
    calc
      2 * Nat.card {F // M.IsDoor F ∧ ¬ M.bdry F} + Nat.card {F // M.IsDoor F ∧ M.bdry F}
          ≡ 0 + Nat.card {F // M.IsDoor F ∧ M.bdry F} [MOD 2] :=
        Nat.ModEq.add h2k_mod2 (show Nat.card {F // M.IsDoor F ∧ M.bdry F} ≡ Nat.card {F // M.IsDoor F ∧ M.bdry F} [MOD 2] from by rfl)
      _ = Nat.card {F // M.IsDoor F ∧ M.bdry F} := by simp
      _ ≡ Nat.card {F // M.IsDoor F ∧ M.bdry F} [MOD 2] := by rfl
  -- Combine: rainbow ≡ total ≡ boundary [MOD 2]
  exact h_total_parity_rainbow.symm.trans h_total_parity_boundary

end Topology
end LeanEval
