import Mathlib
import EvalTools.Markers
import LeanEval.GroupTheory.Frobenius.Basic
import LeanEval.GroupTheory.Frobenius.Character

/-!
# Induced class functions, the lift, and the Frobenius kernel

This file defines the induced class function `Ind_H^G φ` and the lift `χ̃` of an
irreducible character of a point stabiliser, and assembles the character-theoretic
proof that the Frobenius kernel is a normal subgroup.
-/

namespace LeanEval
namespace GroupTheory

open scoped Classical
open CategoryTheory MulAction

variable {G : Type} [Group G] [Fintype G]
variable {X : Type} [MulAction G X]

/-- **Induced class function** (`def:induced-class-function`):
`(Ind_H^G φ)(g) = |H|⁻¹ ∑_{x : x⁻¹ g x ∈ H} φ(x⁻¹ g x)`. -/
noncomputable def indClassFun (H : Subgroup G) (φ : ↥H → ℂ) (g : G) : ℂ :=
  (Nat.card H : ℂ)⁻¹ *
    ∑ x : G, if hx : x⁻¹ * g * x ∈ H then φ ⟨x⁻¹ * g * x, hx⟩ else 0

/-- **Lifted class function** (`def:lifted-class-function`):
`χ̃ = Ind_H^G (χ - χ(1)·1_H) + χ(1)·1_G`. -/
noncomputable def liftClassFun (H : Subgroup G) (χ : ↥H → ℂ) (g : G) : ℂ :=
  indClassFun H (fun h => χ h - χ 1) g + χ 1

/-- **Induction yields a class function** (`lem:induced-is-class-function`). -/
theorem indClassFun_isClassFunction (H : Subgroup G) (φ : ↥H → ℂ) :
    IsClassFunction (indClassFun H φ) := by
  sorry

/-- **Induced value at the identity** (`lem:induced-value-at-one`):
`(Ind_H^G φ)(1) = [G:H] · φ(1)`. -/
theorem indClassFun_one (H : Subgroup G) (φ : ↥H → ℂ) :
    indClassFun H φ 1 = (H.index : ℂ) * φ 1 := by
  sorry

/-- **Coset basis of the induced representation** (`lem:ind-coset-basis`).
The induced representation exists as `W : FDRep ℂ G` with character `Ind_H^G χ_V`
and dimension `[G:H] · dim V` (the coset basis `{t ⊗ eⱼ}`). -/
theorem ind_coset_basis (H : Subgroup G) (V : FDRep ℂ H) :
    ∃ W : FDRep ℂ G,
      indClassFun H V.character = W.character ∧
      Module.finrank ℂ W = H.index * Module.finrank ℂ V := by
  sorry

/-- **Block-monomial matrix of the induced action** (`lem:ind-block-matrix`).
The character of the induced representation `W` is the sum, over cosets `tH`, of the
diagonal blocks, which contribute only when `t⁻¹ g t ∈ H` (with value `χ_V(t⁻¹ g t)`). -/
theorem ind_block_matrix (H : Subgroup G) [Fintype (G ⧸ H)] (V : FDRep ℂ H)
    (W : FDRep ℂ G) (hW : indClassFun H V.character = W.character) (g : G) :
    W.character g = ∑ q : G ⧸ H,
      if hq : (Quotient.out q)⁻¹ * g * (Quotient.out q) ∈ H
      then V.character ⟨_, hq⟩ else 0 := by
  sorry

/-- **Trace of the induced action as a sum over conjugators** (`lem:ind-trace-sum`).
The transversal sum over cosets equals the normalised sum over all of `G`. -/
theorem ind_trace_sum (H : Subgroup G) [Fintype (G ⧸ H)] (φ : ↥H → ℂ) (g : G) :
    indClassFun H φ g = ∑ q : G ⧸ H,
      if hq : (Quotient.out q)⁻¹ * g * (Quotient.out q) ∈ H
      then φ ⟨_, hq⟩ else 0 := by
  sorry

/-- **Induced class function is the character of `ind`** (`lem:induced-is-char-of-ind`).
If `φ = χ_V` is the character of an `H`-representation `V`, then `Ind_H^G φ` is the
character of the induced `G`-representation. -/
theorem induced_is_char_of_ind (H : Subgroup G) (V : FDRep ℂ H) :
    ∃ W : FDRep ℂ G, indClassFun H V.character = W.character := by
  sorry

/-- **Induced inner product as a `Hom`-dimension** (`lem:ind-inner-as-hom-dim`). -/
theorem ind_inner_as_hom_dim (H : Subgroup G) (V : FDRep ℂ H) (W : FDRep ℂ G)
    (Ind : FDRep ℂ G) (hInd : indClassFun H V.character = Ind.character) :
    classInner (indClassFun H V.character) W.character
      = (Module.finrank ℂ (W ⟶ Ind) : ℂ) := by
  sorry

/-- **Restricted inner product as a `Hom`-dimension** (`lem:res-inner-as-hom-dim`). -/
theorem res_inner_as_hom_dim (H : Subgroup G) [Fintype ↥H] (V : FDRep ℂ H)
    (W : FDRep ℂ G) (Res : FDRep ℂ H)
    (hRes : Res.character = fun h : ↥H => W.character (h : G)) :
    classInner (Γ := ↥H) V.character (fun h : ↥H => W.character (h : G))
      = (Module.finrank ℂ (Res ⟶ V) : ℂ) := by
  sorry

/-- **Frobenius reciprocity for characters** (`lem:frobenius-reciprocity-char`). -/
theorem frobenius_reciprocity_char (H : Subgroup G) [Fintype ↥H] (V : FDRep ℂ H)
    (W : FDRep ℂ G) :
    classInner (indClassFun H V.character) W.character
      = classInner (Γ := ↥H) V.character (fun h : ↥H => W.character (h : G)) := by
  sorry

/-- **Frobenius reciprocity** (`lem:frobenius-reciprocity`) for class functions. -/
theorem frobenius_reciprocity (H : Subgroup G) [Fintype ↥H] (φ : ↥H → ℂ) (ψ : G → ℂ)
    (hφ : IsClassFunction (Γ := ↥H) φ) (hψ : IsClassFunction ψ) :
    classInner (indClassFun H φ) ψ
      = classInner (Γ := ↥H) φ (fun h : ↥H => ψ (h : G)) := by
  sorry

/-- **Induced function vanishes on the kernel** (`lem:induced-vanishing-on-kernel`).
For a fixed-point-free `g`, `(Ind_H^G φ)(g) = 0` where `H = Stab(x₀)`. -/
theorem indClassFun_vanishing_on_kernel (hF : FrobeniusHypotheses G X) (x₀ : X)
    (φ : ↥(stabilizer G x₀) → ℂ) {g : G} (hg : ∀ x : X, g • x ≠ x) :
    indClassFun (stabilizer G x₀) φ g = 0 := by
  sorry

/-- **Induced function restricts to `H` when `φ(1) = 0`** (`lem:induced-restriction-to-H`). -/
theorem indClassFun_restriction_to_H (hF : FrobeniusHypotheses G X) (x₀ : X)
    (φ : ↥(stabilizer G x₀) → ℂ) (hφ : IsClassFunction (Γ := ↥(stabilizer G x₀)) φ)
    (hφ1 : φ 1 = 0) (h : ↥(stabilizer G x₀)) :
    indClassFun (stabilizer G x₀) φ (h : G) = φ h := by
  sorry

/-- **Induced value of a vanishing class function** (`lem:induced-vanishing-restriction`). -/
theorem indClassFun_vanishing_restriction (hF : FrobeniusHypotheses G X) (x₀ : X)
    (φ : ↥(stabilizer G x₀) → ℂ) (hφ : IsClassFunction (Γ := ↥(stabilizer G x₀)) φ)
    (hφ1 : φ 1 = 0) :
    (∀ h : ↥(stabilizer G x₀), indClassFun (stabilizer G x₀) φ (h : G) = φ h) ∧
    (∀ g : G, (∀ x : X, g • x ≠ x) → indClassFun (stabilizer G x₀) φ g = 0) := by
  sorry

/-- **The lift is a virtual character** (`lem:lift-is-virtual-character`). -/
theorem liftClassFun_isVirtualCharacter (H : Subgroup G) [Fintype ↥H] {χ : ↥H → ℂ}
    (hχ : IsIrreducibleCharacter (Γ := ↥H) χ) :
    IsVirtualCharacter (liftClassFun H χ) := by
  sorry

/-- **The lift restricts to `χ`** (`lem:lift-restricts`): `χ̃(h) = χ(h)` for `h ∈ H`. -/
theorem liftClassFun_restricts (hF : FrobeniusHypotheses G X) (x₀ : X)
    {χ : ↥(stabilizer G x₀) → ℂ} (hχ : IsClassFunction (Γ := ↥(stabilizer G x₀)) χ)
    (h : ↥(stabilizer G x₀)) :
    liftClassFun (stabilizer G x₀) χ (h : G) = χ h := by
  sorry

/-- **Self inner product of the difference `θ` on `H`** (`lem:theta-inner-self`):
`⟨θ, θ⟩_H = 1 + χ(1)²` for `θ = χ - χ(1)·1_H`. -/
theorem theta_inner_self (H : Subgroup G) [Fintype ↥H] {χ : ↥H → ℂ}
    (hχ : IsIrreducibleCharacter (Γ := ↥H) χ) (hntriv : χ ≠ fun _ => 1) :
    classInner (Γ := ↥H) (fun h => χ h - χ 1) (fun h => χ h - χ 1) = 1 + (χ 1) ^ 2 := by
  sorry

/-- **Self inner product of the induced part** (`lem:lift-inner-self`). -/
theorem lift_inner_self (hF : FrobeniusHypotheses G X) (x₀ : X)
    [Fintype ↥(stabilizer G x₀)] {χ : ↥(stabilizer G x₀) → ℂ}
    (hχ : IsIrreducibleCharacter (Γ := ↥(stabilizer G x₀)) χ) (hntriv : χ ≠ fun _ => 1) :
    classInner (indClassFun (stabilizer G x₀) (fun h => χ h - χ 1))
               (indClassFun (stabilizer G x₀) (fun h => χ h - χ 1)) = 1 + (χ 1) ^ 2 := by
  sorry

/-- **Inner product of the induced part with the trivial character** (`lem:lift-inner-trivial`). -/
theorem lift_inner_trivial (hF : FrobeniusHypotheses G X) (x₀ : X)
    [Fintype ↥(stabilizer G x₀)] {χ : ↥(stabilizer G x₀) → ℂ}
    (hχ : IsIrreducibleCharacter (Γ := ↥(stabilizer G x₀)) χ) (hntriv : χ ≠ fun _ => 1) :
    classInner (indClassFun (stabilizer G x₀) (fun h => χ h - χ 1)) (fun _ : G => 1) = -(χ 1) := by
  sorry

/-- **The lift has norm one** (`lem:lift-norm-one`): `⟨χ̃, χ̃⟩_G = 1`. -/
theorem lift_norm_one (hF : FrobeniusHypotheses G X) (x₀ : X)
    [Fintype ↥(stabilizer G x₀)] {χ : ↥(stabilizer G x₀) → ℂ}
    (hχ : IsIrreducibleCharacter (Γ := ↥(stabilizer G x₀)) χ) (hntriv : χ ≠ fun _ => 1) :
    classInner (liftClassFun (stabilizer G x₀) χ) (liftClassFun (stabilizer G x₀) χ) = 1 := by
  sorry

/-- **The lift is an irreducible character of `G`** (`lem:lift-is-irreducible`). -/
theorem liftClassFun_isIrreducible (hF : FrobeniusHypotheses G X) (x₀ : X)
    [Fintype ↥(stabilizer G x₀)] {χ : ↥(stabilizer G x₀) → ℂ}
    (hχ : IsIrreducibleCharacter (Γ := ↥(stabilizer G x₀)) χ) (hntriv : χ ≠ fun _ => 1) :
    IsIrreducibleCharacter (liftClassFun (stabilizer G x₀) χ) := by
  sorry

/-- **Kernel of the lifted homomorphism is a normal subgroup**
(`lem:lifted-kernel-is-normal-subgroup`): `{g | ρ̃(g) = 1}` is normal in `G`. -/
theorem lifted_kernel_isNormalSubgroup (V : FDRep ℂ G) :
    ∃ N : Subgroup G, N.Normal ∧ (N : Set G) = {g : G | V.ρ g = 1} := by
  sorry

/-- **Kernel of the lifted representation is normal** (`lem:kernel-normal`):
the trace-defined kernel `{g | χ̃(g) = χ̃(1)}` equals `{g | ρ̃(g) = 1}` and is normal. -/
theorem kernel_normal (hF : FrobeniusHypotheses G X) (x₀ : X)
    [Fintype ↥(stabilizer G x₀)] {χ : ↥(stabilizer G x₀) → ℂ}
    (hχ : IsIrreducibleCharacter (Γ := ↥(stabilizer G x₀)) χ) (hntriv : χ ≠ fun _ => 1) :
    ∃ N : Subgroup G, N.Normal ∧
      (N : Set G) = {g : G | liftClassFun (stabilizer G x₀) χ g
        = liftClassFun (stabilizer G x₀) χ 1} := by
  sorry

/-- **The Frobenius kernel lies in every lifted kernel** (`lem:frobenius-kernel-in-each`):
`K ⊆ ker χ̃`. -/
theorem frobenius_kernel_in_each (hF : FrobeniusHypotheses G X) (x₀ : X)
    {χ : ↥(stabilizer G x₀) → ℂ} (hχ : IsClassFunction (Γ := ↥(stabilizer G x₀)) χ)
    {g : G} (hg : g ∈ frobeniusKernel G X) :
    liftClassFun (stabilizer G x₀) χ g = liftClassFun (stabilizer G x₀) χ 1 := by
  sorry

/-- **Irreducible characters separate non-identity elements from `1`** (`lem:irr-separates`). -/
theorem irr_separates (H : Subgroup G) [Fintype ↥H] {h : ↥H} (hh : h ≠ 1) :
    ∃ χ : ↥H → ℂ, IsIrreducibleCharacter (Γ := ↥H) χ ∧ χ h ≠ χ 1 := by
  sorry

/-- **The intersection of lifted kernels lies in the Frobenius kernel**
(`lem:intersection-subset-kernel`): `⋂_χ ker χ̃ ⊆ K`. -/
theorem intersection_subset_kernel (hF : FrobeniusHypotheses G X) (x₀ : X)
    [Fintype ↥(stabilizer G x₀)] {g : G}
    (hg : ∀ χ : ↥(stabilizer G x₀) → ℂ, IsIrreducibleCharacter (Γ := ↥(stabilizer G x₀)) χ →
      liftClassFun (stabilizer G x₀) χ g = liftClassFun (stabilizer G x₀) χ 1) :
    g ∈ frobeniusKernel G X := by
  sorry

/-- **The intersection of lifted kernels is the Frobenius kernel**
(`lem:intersection-equals-kernel`): `⋂_χ ker χ̃ = K` as subsets of `G`. -/
theorem intersection_equals_kernel (hF : FrobeniusHypotheses G X) (x₀ : X)
    [Fintype ↥(stabilizer G x₀)] :
    {g : G | ∀ χ : ↥(stabilizer G x₀) → ℂ, IsIrreducibleCharacter (Γ := ↥(stabilizer G x₀)) χ →
        liftClassFun (stabilizer G x₀) χ g = liftClassFun (stabilizer G x₀) χ 1}
      = frobeniusKernel G X := by
  sorry

end GroupTheory
end LeanEval
