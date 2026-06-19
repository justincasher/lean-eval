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
  sorry

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
  sorry

/-- **Trace equals degree iff the element acts trivially**
(`lem:trace-eq-degree-iff-identity`). -/
theorem trace_eq_degree_iff_identity (V : FDRep ℂ Γ) (g : Γ) :
    V.ρ g = 1 ↔ V.character g = V.character 1 := by
  sorry

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
  sorry

end GroupTheory
end LeanEval
