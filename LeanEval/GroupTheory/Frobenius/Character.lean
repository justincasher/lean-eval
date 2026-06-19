import Mathlib
import EvalTools.Markers

/-!
# Class functions and characters for Frobenius's theorem

General character-theoretic machinery over `ℂ` used in the proof of Frobenius's
theorem.  This file collects the elementary notions (class functions, the inner
product of class functions, irreducible and virtual characters) together with the
facts about characters of finite groups that do not yet refer to the Frobenius
group structure or to induction.
-/

namespace LeanEval
namespace GroupTheory

open scoped Classical
open CategoryTheory

variable {Γ : Type} [Group Γ] [Fintype Γ]

/-- **Class function** (`def:class-function`): a `ℂ`-valued function on `Γ` that is
constant on conjugacy classes. -/
def IsClassFunction (φ : Γ → ℂ) : Prop :=
  ∀ s γ : Γ, φ (s * γ * s⁻¹) = φ γ

/-- **Inner product of class functions** (`def:inner-product`):
`⟨α, β⟩ = |Γ|⁻¹ ∑_γ α γ * conj (β γ)`. -/
noncomputable def classInner (α β : Γ → ℂ) : ℂ :=
  (Fintype.card Γ : ℂ)⁻¹ * ∑ γ : Γ, α γ * (starRingEnd ℂ) (β γ)

/-- **Irreducible character** (`def:irreducible-character`): the character of a
simple finite-dimensional complex representation of `Γ`. -/
def IsIrreducibleCharacter (χ : Γ → ℂ) : Prop :=
  ∃ V : FDRep ℂ Γ, Simple V ∧ χ = V.character

/-- A **virtual character** is an integer combination of irreducible characters. -/
def IsVirtualCharacter (α : Γ → ℂ) : Prop :=
  ∃ (s : Finset (Γ → ℂ)) (c : (Γ → ℂ) → ℤ),
    (∀ χ ∈ s, IsIrreducibleCharacter χ) ∧ α = ∑ χ ∈ s, (c χ : ℂ) • χ

/-- **Eigenvalues of a representation element are roots of unity**
(`lem:rep-element-eigenvalues-roots-of-unity`).  For `V : FDRep ℂ Γ` and `g : Γ`,
the operator `V.ρ g` is diagonalisable with an eigenbasis `b` whose eigenvalues
`lam i` are roots of unity, and `V.character g = ∑ i, lam i`. -/
theorem rep_eigenvalues_rootsOfUnity (V : FDRep ℂ Γ) (g : Γ) :
    ∃ (b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V) (lam : Fin (Module.finrank ℂ V) → ℂ),
      (∀ i, ∃ n : ℕ, 0 < n ∧ lam i ^ n = 1) ∧
      (∀ i, (V.ρ g) (b i) = lam i • b i) ∧
      V.character g = ∑ i, lam i := by
  sorry

/-- **Character of an inverse is the conjugate** (`lem:char-inverse-conjugate`). -/
theorem char_inv_conj (V : FDRep ℂ Γ) (g : Γ) :
    V.character g⁻¹ = (starRingEnd ℂ) (V.character g) := by
  sorry

/-- **Inner product as a character sum** (`lem:inner-product-as-character-sum`). -/
theorem inner_as_char_sum (V W : FDRep ℂ Γ) :
    classInner V.character W.character
      = (Fintype.card Γ : ℂ)⁻¹ * ∑ g : Γ, V.character g * W.character g⁻¹ := by
  sorry

/-- **Inner product equals the dimension of equivariant maps**
(`lem:inner-product-eq-dim-hom`): `⟨χ_V, χ_W⟩ = dim_ℂ Hom_Γ(W, V)`. -/
theorem inner_eq_dim_hom (V W : FDRep ℂ Γ) :
    classInner V.character W.character = (Module.finrank ℂ (W ⟶ V) : ℂ) := by
  haveI : Invertible (Fintype.card Γ : ℂ) := by
    apply invertibleOfNonzero
    have h : Fintype.card Γ ≠ 0 := Fintype.card_pos.ne'
    exact Nat.cast_ne_zero.mpr h
  calc
    classInner V.character W.character
        = (Fintype.card Γ : ℂ)⁻¹ * ∑ g : Γ, V.character g * W.character g⁻¹ := by
      rw [inner_as_char_sum V W]
    _ = ⅟(Fintype.card Γ : ℂ) • ∑ g : Γ, V.character g * W.character g⁻¹ := by
      simp [invOf_eq_inv, smul_eq_mul]
    _ = (Module.finrank ℂ (W ⟶ V) : ℂ) := by
      rw [FDRep.scalar_product_char_eq_finrank_equivariant W V]

/-- **Character inner products are integers** (`lem:character-inner-product-integer`).
For irreducible characters the inner product is `δ_{ij} ∈ {0,1}`. -/
theorem char_inner_product_integer (V W : FDRep ℂ Γ) [Simple V] [Simple W] :
    classInner V.character W.character = if Nonempty (V ≅ W) then (1 : ℂ) else 0 := by
  sorry

/-- **Irreducible characters are an orthonormal basis of class functions**
(`lem:irr-characters-orthonormal-basis`).  *Accepted assumption*: the spanning
half is not available in Mathlib.  Stated as: every class function is a
`ℂ`-combination of irreducible characters, and a class function orthogonal to all
irreducible characters vanishes. -/
theorem irr_characters_orthonormal_basis :
    (∀ α : Γ → ℂ, IsClassFunction α →
        ∃ (s : Finset (Γ → ℂ)) (c : (Γ → ℂ) → ℂ),
          (∀ χ ∈ s, IsIrreducibleCharacter χ) ∧ α = ∑ χ ∈ s, c χ • χ) ∧
    (∀ α : Γ → ℂ, IsClassFunction α →
        (∀ χ : Γ → ℂ, IsIrreducibleCharacter χ → classInner α χ = 0) → α = 0) := by
  sorry

/-- **Trace equal to degree forces all eigenvalues to be one**
(`lem:char-eq-degree-implies-eigenvalues-one`). -/
theorem char_eq_degree_eigenvalues_one (V : FDRep ℂ Γ) (g : Γ)
    (b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V) (lam : Fin (Module.finrank ℂ V) → ℂ)
    (hroot : ∀ i, ∃ n : ℕ, 0 < n ∧ lam i ^ n = 1)
    (heig : ∀ i, (V.ρ g) (b i) = lam i • b i)
    (hsum : V.character g = ∑ i, lam i)
    (hchar : V.character g = V.character 1) :
    ∀ i, lam i = 1 := by
  intro i
  -- Each eigenvalue is a root of unity, hence has norm 1
  have hnorm : ∀ i, ‖lam i‖ = 1 := by
    intro i
    rcases hroot i with ⟨n, hnpos, hn⟩
    have hnpos' : n ≠ 0 := by linarith
    exact Complex.norm_eq_one_of_pow_eq_one hn hnpos'
  -- The character at the identity equals the dimension (finrank)
  have hdim : V.character 1 = (Module.finrank ℂ V : ℂ) := by
    simpa using FDRep.char_one V
  have hsum_dim : ∑ i, lam i = (Module.finrank ℂ V : ℂ) := by
    rw [← hsum, hchar, hdim]
  -- Therefore the norm of the sum equals the sum of the norms (equality in the triangle inequality)
  have hsum_norm : ‖∑ i, lam i‖ = ∑ i, ‖lam i‖ := by
    calc
      ‖∑ i, lam i‖ = ‖(Module.finrank ℂ V : ℂ)‖ := by rw [hsum_dim]
      _ = (Module.finrank ℂ V : ℝ) := by simp
      _ = ∑ i : Fin (Module.finrank ℂ V), (1 : ℝ) := by simp
      _ = ∑ i, ‖lam i‖ := by simp [hnorm]
  -- Lemma: equality of the full triangle inequality implies equality for any sub-sum
  have sub_sum_norm_eq (s : Finset (Fin (Module.finrank ℂ V))) :
      ‖∑ i ∈ s, lam i‖ = ∑ i ∈ s, ‖lam i‖ := by
    classical
    have htotal : (∑ i : Fin (Module.finrank ℂ V), lam i) =
        ((∑ i ∈ s, lam i) + (∑ i ∈ sᶜ, lam i)) := by
      rw [Finset.sum_add_sum_compl]
    have hsum_full_eq : ‖(∑ i ∈ s, lam i) + (∑ i ∈ sᶜ, lam i)‖ =
        (∑ i ∈ s, ‖lam i‖) + (∑ i ∈ sᶜ, ‖lam i‖) := by
      calc
        ‖(∑ i ∈ s, lam i) + (∑ i ∈ sᶜ, lam i)‖ = ‖∑ i : Fin (Module.finrank ℂ V), lam i‖ := by
          rw [htotal]
        _ = ∑ i : Fin (Module.finrank ℂ V), ‖lam i‖ := hsum_norm
        _ = (∑ i ∈ s, ‖lam i‖) + (∑ i ∈ sᶜ, ‖lam i‖) := by rw [Finset.sum_add_sum_compl]
    have hineq1 : ‖(∑ i ∈ s, lam i) + (∑ i ∈ sᶜ, lam i)‖ ≤ ‖∑ i ∈ s, lam i‖ + ‖∑ i ∈ sᶜ, lam i‖ :=
      norm_add_le _ _
    have hineq2 : ‖∑ i ∈ s, lam i‖ + ‖∑ i ∈ sᶜ, lam i‖ ≤ (∑ i ∈ s, ‖lam i‖) + (∑ i ∈ sᶜ, ‖lam i‖) :=
      add_le_add (norm_sum_le (s := s) lam) (norm_sum_le (s := sᶜ) lam)
    have hsum_chain : ‖∑ i ∈ s, lam i‖ + ‖∑ i ∈ sᶜ, lam i‖ = (∑ i ∈ s, ‖lam i‖) + (∑ i ∈ sᶜ, ‖lam i‖) := by
      linarith
    have hA_le : ‖∑ i ∈ s, lam i‖ ≤ ∑ i ∈ s, ‖lam i‖ := norm_sum_le (s := s) lam
    have hAc_le : ‖∑ i ∈ sᶜ, lam i‖ ≤ ∑ i ∈ sᶜ, ‖lam i‖ := norm_sum_le (s := sᶜ) lam
    linarith
  -- For any two indices j, k, the two-term sum also achieves triangle equality
  have hnorm_pair : ∀ j k, ‖lam j + lam k‖ = ‖lam j‖ + ‖lam k‖ := by
    intro j k
    by_cases hjk : j = k
    · subst hjk
      have h_two_mul : lam j + lam j = (2 : ℂ) * lam j := by ring
      calc
        ‖lam j + lam j‖ = ‖(2 : ℂ) * lam j‖ := by rw [h_two_mul]
        _ = ‖(2 : ℂ)‖ * ‖lam j‖ := by rw [norm_mul]
        _ = (2 : ℝ) * 1 := by simp [hnorm j]
        _ = (1 : ℝ) + 1 := by norm_num
        _ = ‖lam j‖ + ‖lam j‖ := by simp [hnorm j]
    · have hpair := sub_sum_norm_eq ({j, k} : Finset (Fin (Module.finrank ℂ V)))
      have hsum_simp : (∑ i ∈ ({j, k} : Finset (Fin (Module.finrank ℂ V))), lam i) = lam j + lam k := by
        rw [Finset.sum_insert (by simpa [Finset.mem_singleton] using hjk), Finset.sum_singleton]
      have hsum_norm_simp : (∑ i ∈ ({j, k} : Finset (Fin (Module.finrank ℂ V))), ‖lam i‖) = ‖lam j‖ + ‖lam k‖ := by
        rw [Finset.sum_insert (by simpa [Finset.mem_singleton] using hjk), Finset.sum_singleton]
      simpa [hsum_simp, hsum_norm_simp] using hpair
  -- Since all eigenvalues have equal norm (=1) and triangle equality holds pairwise,
  -- they are all equal
  have h_all_eq : ∀ j, lam j = lam i := by
    intro j
    exact (eq_of_norm_eq_of_norm_add_eq (by rw [hnorm i, hnorm j]) (hnorm_pair i j)).symm
  -- Their common value λ = lam i satisfies d • λ = d, so λ = 1 (where d = finrank)
  by_cases hzero_finrank : Module.finrank ℂ V = 0
  · -- If finrank = 0, then V is 0-dimensional, Fin 0 is empty, so i cannot exist
    exact Fin.elim0 (hzero_finrank ▸ i)
  · -- finrank ≠ 0, so we can cancel in the equation d • λ = d
    have hsum_as_const : ∑ j : Fin (Module.finrank ℂ V), lam i = (Module.finrank ℂ V : ℂ) := by
      calc
        ∑ j : Fin (Module.finrank ℂ V), lam i = ∑ j : Fin (Module.finrank ℂ V), lam j := by
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [h_all_eq j]
        _ = (Module.finrank ℂ V : ℂ) := hsum_dim
    have h_factor : (Module.finrank ℂ V : ℂ) * lam i = (Module.finrank ℂ V : ℂ) := by
      calc
        (Module.finrank ℂ V : ℂ) * lam i = ∑ j : Fin (Module.finrank ℂ V), lam i := by
          simp
        _ = (Module.finrank ℂ V : ℂ) := hsum_as_const
    have h_finrank_ne_zero : (Module.finrank ℂ V : ℂ) ≠ 0 := by
      intro hzero
      apply hzero_finrank
      exact_mod_cast hzero
    field_simp [h_finrank_ne_zero] at h_factor
    exact h_factor

/-- **Trace equals degree iff the element acts trivially**
(`lem:trace-eq-degree-iff-identity`). -/
theorem trace_eq_degree_iff_identity (V : FDRep ℂ Γ) (g : Γ) :
    V.ρ g = 1 ↔ V.character g = V.character 1 := by
  constructor
  · intro h
    calc
      V.character g = LinearMap.trace ℂ V (V.ρ g) := rfl
      _ = LinearMap.trace ℂ V (1 : V →ₗ[ℂ] V) := by rw [h]
      _ = (Module.finrank ℂ V : ℂ) := by simp
      _ = V.character 1 := by rw [FDRep.char_one]
  · intro hchar
    rcases rep_eigenvalues_rootsOfUnity V g with ⟨b, lam, hroot, heig, hsum⟩
    have h_lam_one : ∀ i, lam i = 1 :=
      char_eq_degree_eigenvalues_one V g b lam hroot heig hsum hchar
    apply Module.Basis.ext b
    intro i
    have h_rho : (V.ρ g) (b i) = b i := by
      calc
        (V.ρ g) (b i) = lam i • b i := heig i
        _ = 1 • b i := by simpa [h_lam_one i]
        _ = b i := by simp
    simpa [h_rho]

/-- **A norm-one virtual character is `±` an irreducible character**
(`lem:norm-one-virtual-is-plus-minus-irr`). -/
theorem norm_one_virtual_is_plus_minus_irr {α : Γ → ℂ} (hα : IsVirtualCharacter α)
    (hnorm : classInner α α = 1) :
    ∃ ζ : Γ → ℂ, IsIrreducibleCharacter ζ ∧ (α = ζ ∨ α = -ζ) := by
  sorry

/-- **A norm-one virtual character of positive degree is irreducible**
(`lem:norm-one-virtual-is-irreducible`). -/
theorem norm_one_virtual_is_irreducible {α : Γ → ℂ} (hα : IsVirtualCharacter α)
    (hnorm : classInner α α = 1) (hdeg : 0 < (α 1).re) :
    IsIrreducibleCharacter α := by
  rcases norm_one_virtual_is_plus_minus_irr hα hnorm with ⟨ζ, hζ, h|h⟩
  · -- case α = ζ, then we are done
    rw [h]
    exact hζ
  · -- case α = -ζ; this would give (α 1).re = -((ζ 1).re) < 0, contradicting hdeg
    rw [h] at hdeg
    have h_nonneg : 0 ≤ (ζ 1).re := by
      rcases hζ with ⟨V, hV_simple, hV_char⟩
      have h_char1 : V.character 1 = (Module.finrank ℂ V : ℂ) := FDRep.char_one V
      have h_ζ1 : ζ 1 = V.character 1 := by rw [hV_char]
      rw [h_ζ1, h_char1]
      simpa using Nat.cast_nonneg (Module.finrank ℂ V)
    have h_neg : ((-ζ) 1).re = -((ζ 1).re) := by simp
    rw [h_neg] at hdeg
    linarith

end GroupTheory
end LeanEval
