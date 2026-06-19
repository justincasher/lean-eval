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
  dsimp [indClassFun]
  have h1 : (1 : G) ∈ H := H.one_mem
  have hsum : ∑ x : G, (if hx : x⁻¹ * 1 * x ∈ H then φ ⟨x⁻¹ * 1 * x, hx⟩ else 0) =
      (Fintype.card G : ℂ) * φ 1 := by
    calc
      ∑ x : G, (if hx : x⁻¹ * 1 * x ∈ H then φ ⟨x⁻¹ * 1 * x, hx⟩ else 0) = ∑ x : G, φ 1 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        have hx1 : x⁻¹ * 1 * x = 1 := by simp
        have hmem : x⁻¹ * 1 * x ∈ H := by
          rw [hx1]
          exact h1
        rw [dif_pos hmem]
        have h_subtype : (⟨x⁻¹ * 1 * x, hmem⟩ : ↥H) = (1 : ↥H) := by
          ext; simpa using hx1
        rw [h_subtype]
      _ = (Fintype.card G : ℂ) * φ 1 := by simp
  rw [hsum]
  have hcard_eq' : (H.index : ℂ) * (Nat.card H : ℂ) = (Fintype.card G : ℂ) := by
    calc
      (H.index : ℂ) * (Nat.card H : ℂ) = (Nat.card G : ℂ) := by
        have h := Subgroup.index_mul_card H
        simpa [mul_comm] using congrArg (fun n : ℕ => (n : ℂ)) h
      _ = (Fintype.card G : ℂ) := by simp
  have hcardH_nonzero : (Nat.card H : ℂ) ≠ 0 := by
    have h_nonempty : Nonempty (↥H) := ⟨⟨1, H.one_mem⟩⟩
    have h_finite : Finite (↥H) := by infer_instance
    have h0 : Nat.card H ≠ 0 := (Nat.card_ne_zero.mpr ⟨h_nonempty, h_finite⟩)
    exact_mod_cast h0
  calc
    (Nat.card H : ℂ)⁻¹ * ((Fintype.card G : ℂ) * φ 1) = ((Nat.card H : ℂ)⁻¹ * (Fintype.card G : ℂ)) * φ 1 := by ring
    _ = (H.index : ℂ) * φ 1 := by
      have h : (Nat.card H : ℂ)⁻¹ * (Fintype.card G : ℂ) = (H.index : ℂ) := by
        field_simp [hcardH_nonzero]
        rw [mul_comm, hcard_eq'.symm]
      rw [h]

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
  obtain ⟨W, h⟩ := ind_coset_basis H V
  exact ⟨W, h.1⟩

/-- **Induced inner product as a `Hom`-dimension** (`lem:ind-inner-as-hom-dim`). -/
theorem ind_inner_as_hom_dim (H : Subgroup G) (V : FDRep ℂ H) (W : FDRep ℂ G)
    (Ind : FDRep ℂ G) (hInd : indClassFun H V.character = Ind.character) :
    classInner (indClassFun H V.character) W.character
      = (Module.finrank ℂ (W ⟶ Ind) : ℂ) := by
  calc
    classInner (indClassFun H V.character) W.character
        = classInner Ind.character W.character := by rw [hInd]
    _ = (Module.finrank ℂ (W ⟶ Ind) : ℂ) := by rw [inner_eq_dim_hom Ind W]

/-- **Restricted inner product as a `Hom`-dimension** (`lem:res-inner-as-hom-dim`). -/
theorem res_inner_as_hom_dim (H : Subgroup G) [Fintype ↥H] (V : FDRep ℂ H)
    (W : FDRep ℂ G) (Res : FDRep ℂ H)
    (hRes : Res.character = fun h : ↥H => W.character (h : G)) :
    classInner (Γ := ↥H) V.character (fun h : ↥H => W.character (h : G))
      = (Module.finrank ℂ (Res ⟶ V) : ℂ) := by
  calc
    classInner (Γ := ↥H) V.character (fun h : ↥H => W.character (h : G))
        = classInner (Γ := ↥H) V.character Res.character := by rw [hRes]
    _ = (Module.finrank ℂ (Res ⟶ V) : ℂ) := by rw [inner_eq_dim_hom V Res]

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
  -- linearity of classInner in the first argument (for group G)
  have h_cl_smul_left_G (c : ℂ) (α β : G → ℂ) : classInner (c • α) β = c * classInner α β := by
    dsimp [classInner, Pi.smul_apply]
    simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
  have h_cl_add_left_G (α₁ α₂ β : G → ℂ) : classInner (α₁ + α₂) β = classInner α₁ β + classInner α₂ β := by
    simp [classInner, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]
  have h_cl_zero_left_G (β : G → ℂ) : classInner (0 : G → ℂ) β = 0 := by
    simp [classInner]

  -- conjugate-linearity of classInner in the second argument (for group G)
  have h_cl_smul_right_G (c : ℂ) (α β : G → ℂ) : classInner α (c • β) = (starRingEnd ℂ) c * classInner α β := by
    dsimp [classInner, Pi.smul_apply]
    simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
  have h_cl_add_right_G (α β₁ β₂ : G → ℂ) : classInner α (β₁ + β₂) = classInner α β₁ + classInner α β₂ := by
    simp [classInner, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have h_cl_zero_right_G (α : G → ℂ) : classInner α (0 : G → ℂ) = 0 := by
    simp [classInner]

  -- linearity of classInner in the first argument (for subgroup H)
  have h_cl_smul_left_H (c : ℂ) (α β : ↥H → ℂ) : classInner (c • α) β = c * classInner α β := by
    dsimp [classInner, Pi.smul_apply]
    simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
  have h_cl_add_left_H (α₁ α₂ β : ↥H → ℂ) : classInner (α₁ + α₂) β = classInner α₁ β + classInner α₂ β := by
    simp [classInner, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]
  have h_cl_zero_left_H (β : ↥H → ℂ) : classInner (0 : ↥H → ℂ) β = 0 := by
    simp [classInner]

  -- conjugate-linearity of classInner in the second argument (for subgroup H)
  have h_cl_smul_right_H (c : ℂ) (α β : ↥H → ℂ) : classInner α (c • β) = (starRingEnd ℂ) c * classInner α β := by
    dsimp [classInner, Pi.smul_apply]
    simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
  have h_cl_add_right_H (α β₁ β₂ : ↥H → ℂ) : classInner α (β₁ + β₂) = classInner α β₁ + classInner α β₂ := by
    simp [classInner, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have h_cl_zero_right_H (α : ↥H → ℂ) : classInner α (0 : ↥H → ℂ) = 0 := by
    simp [classInner]

  -- sum versions of the above (generalized)
  have h_cl_sum_left_G_ind (s : Finset (↥H → ℂ)) (c : (↥H → ℂ) → ℂ) (β : G → ℂ) :
      classInner (∑ χ ∈ s, c χ • (indClassFun H χ)) β = ∑ χ ∈ s, c χ * classInner (indClassFun H χ) β := by
    refine Finset.induction_on s ?_ ?_
    · simp [h_cl_zero_left_G]
    · intro χ s hχ ih
      rw [Finset.sum_insert hχ, h_cl_add_left_G, h_cl_smul_left_G, ih, Finset.sum_insert hχ]

  have h_cl_sum_right_H_restrict (t : Finset (G → ℂ)) (d : (G → ℂ) → ℂ) (α : ↥H → ℂ) :
      classInner α (∑ ξ ∈ t, d ξ • (fun h : ↥H => ξ (h : G))) =
        ∑ ξ ∈ t, (starRingEnd ℂ) (d ξ) * classInner α (fun h : ↥H => ξ (h : G)) := by
    refine Finset.induction_on t ?_ ?_
    · simp [h_cl_zero_right_H]
    · intro ξ t hξ ih
      rw [Finset.sum_insert hξ, h_cl_add_right_H, h_cl_smul_right_H, ih, Finset.sum_insert hξ]

  have h_cl_sum_left_H_self (s : Finset (↥H → ℂ)) (c : (↥H → ℂ) → ℂ) (β : ↥H → ℂ) :
      classInner (∑ χ ∈ s, c χ • χ) β = ∑ χ ∈ s, c χ * classInner χ β := by
    refine Finset.induction_on s ?_ ?_
    · simp [h_cl_zero_left_H]
    · intro χ s hχ ih
      rw [Finset.sum_insert hχ, h_cl_add_left_H, h_cl_smul_left_H, ih, Finset.sum_insert hχ]

  have h_cl_sum_right_G_self (t : Finset (G → ℂ)) (d : (G → ℂ) → ℂ) (α : G → ℂ) :
      classInner α (∑ ξ ∈ t, d ξ • ξ) = ∑ ξ ∈ t, (starRingEnd ℂ) (d ξ) * classInner α ξ := by
    refine Finset.induction_on t ?_ ?_
    · simp [h_cl_zero_right_G]
    · intro ξ t hξ ih
      rw [Finset.sum_insert hξ, h_cl_add_right_G, h_cl_smul_right_G, ih, Finset.sum_insert hξ]

  -- linearity of indClassFun
  have h_ind_smul (c : ℂ) (χ : ↥H → ℂ) : indClassFun H (c • χ) = c • indClassFun H χ := by
    ext g
    dsimp [indClassFun, Pi.smul_apply]
    simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
  have h_ind_add (χ₁ χ₂ : ↥H → ℂ) : indClassFun H (χ₁ + χ₂) = indClassFun H χ₁ + indClassFun H χ₂ := by
    ext g
    calc
      indClassFun H (χ₁ + χ₂) g
          = (Nat.card H : ℂ)⁻¹ * ∑ x : G, (if hx : x⁻¹ * g * x ∈ H then ((χ₁ + χ₂) ⟨x⁻¹ * g * x, hx⟩) else 0) := rfl
      _ = (Nat.card H : ℂ)⁻¹ * ∑ x : G, (if hx : x⁻¹ * g * x ∈ H then χ₁ ⟨x⁻¹ * g * x, hx⟩ + χ₂ ⟨x⁻¹ * g * x, hx⟩ else 0) := by
        simp
      _ = (Nat.card H : ℂ)⁻¹ * ∑ x : G, ((if hx : x⁻¹ * g * x ∈ H then χ₁ ⟨x⁻¹ * g * x, hx⟩ else 0) + (if hx : x⁻¹ * g * x ∈ H then χ₂ ⟨x⁻¹ * g * x, hx⟩ else 0)) := by
        refine congrArg (fun (t : G → ℂ) => (Nat.card H : ℂ)⁻¹ * ∑ x : G, t x) ?_
        ext x
        split_ifs <;> simp
      _ = (Nat.card H : ℂ)⁻¹ * ((∑ x : G, if hx : x⁻¹ * g * x ∈ H then χ₁ ⟨x⁻¹ * g * x, hx⟩ else 0) + (∑ x : G, if hx : x⁻¹ * g * x ∈ H then χ₂ ⟨x⁻¹ * g * x, hx⟩ else 0)) := by
        simp [Finset.sum_add_distrib]
      _ = (Nat.card H : ℂ)⁻¹ * (∑ x : G, if hx : x⁻¹ * g * x ∈ H then χ₁ ⟨x⁻¹ * g * x, hx⟩ else 0) + (Nat.card H : ℂ)⁻¹ * (∑ x : G, if hx : x⁻¹ * g * x ∈ H then χ₂ ⟨x⁻¹ * g * x, hx⟩ else 0) := by
        ring
      _ = indClassFun H χ₁ g + indClassFun H χ₂ g := rfl
  have h_ind_zero : indClassFun H (0 : ↥H → ℂ) = (0 : G → ℂ) := by
    ext g; simp [indClassFun, Pi.zero_apply]
  have h_ind_sum (s : Finset (↥H → ℂ)) (c : (↥H → ℂ) → ℂ) :
      indClassFun H (∑ χ ∈ s, c χ • χ) = ∑ χ ∈ s, c χ • (indClassFun H χ) := by
    refine Finset.induction_on s ?_ ?_
    · simp [h_ind_zero]
    · intro χ s hχ ih
      rw [Finset.sum_insert hχ, h_ind_add, h_ind_smul, ih, Finset.sum_insert hχ]

  -- Step 1: For each irreducible character ξ of G, the reciprocity holds for all class functions φ' of H
  have h_for_irr_ξ (ξ : G → ℂ) (hξ_irr : IsIrreducibleCharacter (Γ := G) ξ) (φ' : ↥H → ℂ)
      (hφ' : IsClassFunction (Γ := ↥H) φ') :
      classInner (indClassFun H φ') ξ = classInner (Γ := ↥H) φ' (fun h : ↥H => ξ (h : G)) := by
    rcases (irr_characters_orthonormal_basis (Γ := ↥H)).1 φ' hφ' with ⟨s, c, hs_irr, hφ'_eq⟩
    rcases hξ_irr with ⟨W, hW_simple, hW_char⟩
    rw [hφ'_eq, h_ind_sum s c, hW_char]
    calc
      classInner (∑ χ ∈ s, c χ • (indClassFun H χ)) W.character
          = ∑ χ ∈ s, c χ * classInner (indClassFun H χ) W.character := by
        rw [h_cl_sum_left_G_ind s c W.character]
      _ = ∑ χ ∈ s, c χ * classInner (Γ := ↥H) χ (fun h : ↥H => W.character (h : G)) := by
        refine Finset.sum_congr rfl fun χ hχ => ?_
        rcases hs_irr χ hχ with ⟨V, hV_simple, hV_char⟩
        rw [hV_char, frobenius_reciprocity_char H V W]
      _ = classInner (Γ := ↥H) (∑ χ ∈ s, c χ • χ) (fun h : ↥H => W.character (h : G)) := by
        rw [h_cl_sum_left_H_self s c (fun h : ↥H => W.character (h : G))]

  -- Step 2: decompose ψ and apply h_for_irr_ξ to each irreducible component
  rcases (irr_characters_orthonormal_basis (Γ := G)).1 ψ hψ with ⟨t, d, ht_irr, hψ_eq⟩
  rw [hψ_eq]
  calc
    classInner (indClassFun H φ) (∑ ξ ∈ t, d ξ • ξ)
        = ∑ ξ ∈ t, (starRingEnd ℂ) (d ξ) * classInner (indClassFun H φ) ξ := by
      rw [h_cl_sum_right_G_self t d (indClassFun H φ)]
    _ = ∑ ξ ∈ t, (starRingEnd ℂ) (d ξ) * classInner (Γ := ↥H) φ (fun h : ↥H => ξ (h : G)) := by
      refine Finset.sum_congr rfl fun ξ hξ => ?_
      rw [h_for_irr_ξ ξ (ht_irr ξ hξ) φ hφ]
    _ = classInner (Γ := ↥H) φ (∑ ξ ∈ t, d ξ • (fun h : ↥H => ξ (h : G))) := by
      rw [h_cl_sum_right_H_restrict t d φ]
    _ = classInner (Γ := ↥H) φ (fun h : ↥H => (∑ ξ ∈ t, d ξ • ξ) (h : G)) := by
      congr; ext h; simp

/-- **Induced function vanishes on the kernel** (`lem:induced-vanishing-on-kernel`).
For a fixed-point-free `g`, `(Ind_H^G φ)(g) = 0` where `H = Stab(x₀)`. -/
theorem indClassFun_vanishing_on_kernel (hF : FrobeniusHypotheses G X) (x₀ : X)
    (φ : ↥(stabilizer G x₀) → ℂ) {g : G} (hg : ∀ x : X, g • x ≠ x) :
    indClassFun (stabilizer G x₀) φ g = 0 := by
  -- If `x⁻¹ * g * x ∈ stabilizer G x₀`, then `g • (x • x₀) = x • x₀`, contradicting `hg`.
  have no_conj : ∀ x : G, x⁻¹ * g * x ∉ stabilizer G x₀ := by
    intro x
    intro hx
    have hx_stab : (x⁻¹ * g * x) • x₀ = x₀ := MulAction.mem_stabilizer_iff.mp hx
    have hcalc : (x⁻¹ * g * x) • (x₀ : X) = x⁻¹ • (g • (x • x₀)) := by
      simp [mul_smul]
    have htemp : x⁻¹ • (g • (x • x₀)) = x₀ := by
      rw [← hcalc, hx_stab]
    have hg_fixed : g • (x • x₀) = x • x₀ := by
      calc
        g • (x • x₀) = (x * x⁻¹) • (g • (x • x₀)) := by simp
        _ = x • (x⁻¹ • (g • (x • x₀))) := by rw [mul_smul]
        _ = x • x₀ := by simp [htemp]
    exact hg (x • x₀) hg_fixed
  dsimp [indClassFun]
  simp [no_conj]

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
  constructor
  · intro h
    exact indClassFun_restriction_to_H hF x₀ φ hφ hφ1 h
  · intro g hg
    exact indClassFun_vanishing_on_kernel hF x₀ φ hg

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
  /- Apply indClassFun_vanishing_restriction to θ = χ - χ(1) -/
  set θ := fun (h' : ↥(stabilizer G x₀)) => χ h' - χ 1 with hθ
  have hθ1 : θ 1 = 0 := by
    dsimp [θ]
    simp
  have hθ_class : IsClassFunction (Γ := ↥(stabilizer G x₀)) θ := by
    intro s γ
    dsimp [θ]
    rw [hχ s γ]
  have h_ind := (indClassFun_vanishing_restriction hF x₀ θ hθ_class hθ1).1 h
  /- Unfold liftClassFun -/
  dsimp [liftClassFun]
  calc
    indClassFun (stabilizer G x₀) θ (h : G) + χ 1 = θ h + χ 1 := by rw [h_ind]
    _ = (χ h - χ 1) + χ 1 := by rfl
    _ = χ h := by ring

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
  let H := stabilizer G x₀
  let θ : ↥H → ℂ := fun h => χ h - χ 1
  let F : G → ℂ := indClassFun H θ
  let c : ℂ := χ 1
  let C : G → ℂ := fun _ => c
  have h_lift : liftClassFun H χ = F + C := by
    ext g
    simp [liftClassFun, F, θ, c, C]
  rw [h_lift]
  have h_add_left (a b c_fun : G → ℂ) : classInner (a + b) c_fun = classInner a c_fun + classInner b c_fun := by
    dsimp [classInner]
    simp [Finset.sum_add_distrib, mul_add, add_mul]
  have h_add_right (a b c_fun : G → ℂ) : classInner a (b + c_fun) = classInner a b + classInner a c_fun := by
    dsimp [classInner]
    simp [Finset.sum_add_distrib, mul_add, star_add]
  have h_smul_const_right (a : G → ℂ) (d : ℂ) : classInner a (fun (_ : G) => d) = (starRingEnd ℂ) d * classInner a (fun (_ : G) => 1) := by
    dsimp [classInner]
    calc
      (Fintype.card G : ℂ)⁻¹ * ∑ γ : G, a γ * (starRingEnd ℂ) d
          = (Fintype.card G : ℂ)⁻¹ * ((∑ γ : G, a γ) * (starRingEnd ℂ) d) := by rw [Finset.sum_mul]
      _ = (starRingEnd ℂ) d * ((Fintype.card G : ℂ)⁻¹ * (∑ γ : G, a γ)) := by ring
      _ = (starRingEnd ℂ) d * ((Fintype.card G : ℂ)⁻¹ * ∑ γ : G, a γ * (starRingEnd ℂ) (1 : ℂ)) := by simp
      _ = (starRingEnd ℂ) d * classInner a (fun (_ : G) => 1) := rfl
  have h_const_smul_left (d : ℂ) (f : G → ℂ) : classInner (fun (_ : G) => d) f = d * classInner (fun (_ : G) => 1) f := by
    dsimp [classInner]
    simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
  have h_const_const (d e : ℂ) : classInner (fun (_ : G) => d) (fun (_ : G) => e) = d * (starRingEnd ℂ) e := by
    dsimp [classInner]
    simp
  have h_FF : classInner F F = 1 + c ^ 2 := by
    simpa [F, θ, c] using lift_inner_self hF x₀ hχ hntriv
  have h_F_one : classInner F (fun (_ : G) => 1) = -(c) := by
    simpa [F, θ, c] using lift_inner_trivial hF x₀ hχ hntriv
  have hc_real : starRingEnd ℂ c = c := by
    dsimp [c]
    rcases hχ with ⟨V, hV_simple, hV_char⟩
    have h_char1 : V.character 1 = (Module.finrank ℂ V : ℂ) := FDRep.char_one V
    calc
      starRingEnd ℂ (χ 1) = starRingEnd ℂ (V.character 1) := by rw [hV_char]
      _ = starRingEnd ℂ ((Module.finrank ℂ V : ℂ)) := by rw [h_char1]
      _ = (Module.finrank ℂ V : ℂ) := by simp
      _ = χ 1 := by rw [hV_char, h_char1]
  have h_one_F : classInner (fun (_ : G) => 1) F = -c := by
    calc
      classInner (fun (_ : G) => 1) F = starRingEnd ℂ (classInner F (fun (_ : G) => 1)) := by
        dsimp [classInner]
        simp
      _ = starRingEnd ℂ (-c) := by rw [h_F_one]
      _ = -starRingEnd ℂ c := by simp
      _ = -c := by rw [hc_real]
  calc
    classInner (F + C) (F + C) = classInner F (F + C) + classInner C (F + C) := by rw [h_add_left]
    _ = (classInner F F + classInner F C) + (classInner C F + classInner C C) := by rw [h_add_right, h_add_right]
    _ = classInner F F + classInner F C + classInner C F + classInner C C := by ring
    _ = classInner F F + ((starRingEnd ℂ) c * classInner F (fun (_ : G) => 1))
        + (c * classInner (fun (_ : G) => 1) F) + (c * (starRingEnd ℂ) c) := by
      rw [h_smul_const_right F c, h_const_smul_left c F, h_const_const c c]
    _ = classInner F F + (c * classInner F (fun (_ : G) => 1))
        + (c * classInner (fun (_ : G) => 1) F) + (c ^ 2) := by
      rw [show (starRingEnd ℂ) c * classInner F (fun (_ : G) => 1) = c * classInner F (fun (_ : G) => 1) from by rw [hc_real]]
      rw [show c * (starRingEnd ℂ) c = c ^ 2 from by rw [hc_real]; ring]
    _ = (1 + c ^ 2) + c * (-c) + c * (-c) + c ^ 2 := by
      rw [h_FF, h_F_one, h_one_F]
    _ = 1 := by ring

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
  refine ⟨MonoidHom.ker V.ρ, MonoidHom.normal_ker V.ρ, ?_⟩
  ext g
  simp [MonoidHom.mem_ker, Set.mem_setOf_eq]

/-- **Kernel of the lifted representation is normal** (`lem:kernel-normal`):
the trace-defined kernel `{g | χ̃(g) = χ̃(1)}` equals `{g | ρ̃(g) = 1}` and is normal. -/
theorem kernel_normal (hF : FrobeniusHypotheses G X) (x₀ : X)
    [Fintype ↥(stabilizer G x₀)] {χ : ↥(stabilizer G x₀) → ℂ}
    (hχ : IsIrreducibleCharacter (Γ := ↥(stabilizer G x₀)) χ) (hntriv : χ ≠ fun _ => 1) :
    ∃ N : Subgroup G, N.Normal ∧
      (N : Set G) = {g : G | liftClassFun (stabilizer G x₀) χ g
        = liftClassFun (stabilizer G x₀) χ 1} := by
  have h_lift_irr : IsIrreducibleCharacter (liftClassFun (stabilizer G x₀) χ) :=
    liftClassFun_isIrreducible hF x₀ hχ hntriv
  rcases h_lift_irr with ⟨V, _, hV_char⟩
  rcases lifted_kernel_isNormalSubgroup V with ⟨N, hN_normal, hN_set⟩
  refine ⟨N, hN_normal, ?_⟩
  rw [hN_set]
  ext g
  constructor
  · intro hg
    have h_trace := (trace_eq_degree_iff_identity V g).mp hg
    rw [hV_char]
    exact h_trace
  · intro hg
    apply (trace_eq_degree_iff_identity V g).mpr
    calc
      V.character g = liftClassFun (stabilizer G x₀) χ g := by rw [hV_char.symm]
      _ = liftClassFun (stabilizer G x₀) χ 1 := hg
      _ = V.character 1 := by rw [hV_char]

/-- **The Frobenius kernel lies in every lifted kernel** (`lem:frobenius-kernel-in-each`):
`K ⊆ ker χ̃`. -/
theorem frobenius_kernel_in_each (hF : FrobeniusHypotheses G X) (x₀ : X)
    {χ : ↥(stabilizer G x₀) → ℂ} (hχ : IsClassFunction (Γ := ↥(stabilizer G x₀)) χ)
    {g : G} (hg : g ∈ frobeniusKernel G X) :
    liftClassFun (stabilizer G x₀) χ g = liftClassFun (stabilizer G x₀) χ 1 := by
  rcases hg with (hg1 | hgfree)
  · subst hg1; rfl
  · let H := stabilizer G x₀
    set θ : ↥H → ℂ := fun h => χ h - χ 1 with hθ
    have hθ1 : θ 1 = 0 := by
      dsimp [θ]; simp
    have h_ind_g : indClassFun H θ g = 0 :=
      indClassFun_vanishing_on_kernel hF x₀ θ hgfree
    have h_ind_one : indClassFun H θ 1 = 0 := by
      rw [indClassFun_one H θ, hθ1, mul_zero]
    calc
      liftClassFun H χ g = indClassFun H θ g + χ 1 := rfl
      _ = 0 + χ 1 := by rw [h_ind_g]
      _ = χ 1 := by simp
      _ = indClassFun H θ 1 + χ 1 := by rw [h_ind_one, zero_add]
      _ = liftClassFun H χ 1 := rfl

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
  by_contra! hg_notK
  have hg1 : g ≠ 1 := by
    intro h_eq
    apply hg_notK
    subst h_eq
    simp [frobeniusKernel]
  have hg_fixes : ∃ x : X, g • x = x := by
    by_contra! h_all_free
    apply hg_notK
    simp [frobeniusKernel, h_all_free]
  rcases hg_fixes with ⟨x, hx⟩
  have hgK : ¬ ∀ x : X, g • x ≠ x := by
    intro h_all_free
    exact h_all_free x hx
  rcases non_kernel_conjugate_to_H hF x₀ hg1 hgK with ⟨s, hs_mem, hs1⟩
  let H := stabilizer G x₀
  have h_mem : s⁻¹ * g * s ∈ H := hs_mem
  have hh_ne_one : (⟨s⁻¹ * g * s, h_mem⟩ : ↥H) ≠ 1 := by
    intro h_eq
    apply hs1
    exact Subtype.mk.inj h_eq
  rcases irr_separates H hh_ne_one with ⟨χ, hχ_irr, hχ_ne⟩
  -- The character χ is a class function (by FDRep.char_conj)
  have hχ_class : IsClassFunction (Γ := H) χ := by
    rcases hχ_irr with ⟨V, hV_simple, hV_char⟩
    rw [hV_char]
    intro s γ
    exact FDRep.char_conj V γ s
  -- indClassFun is invariant under conjugation: indClassFun H φ (s⁻¹ * g * s) = indClassFun H φ g
  have h_ind_conj (φ : ↥H → ℂ) : indClassFun H φ (s⁻¹ * g * s) = indClassFun H φ g := by
    dsimp [indClassFun]
    congr 1
    refine Finset.sum_bij (fun x _ => s * x) (by intro x hx; simp) ?_ ?_ ?_
    · intro x₁ hx₁ x₂ hx₂ h
      -- s * x₁ = s * x₂ → x₁ = x₂ in a group
      simpa [mul_assoc] using congrArg (fun t : G => s⁻¹ * t) h
    · intro y hy
      refine ⟨s⁻¹ * y, Finset.mem_univ _, ?_⟩
      simp
    · intro x hx
      have hcalc : x⁻¹ * (s⁻¹ * g * s) * x = (s * x)⁻¹ * g * (s * x) := by
        group
      simp [hcalc]
  -- LiftClassFun is also invariant under conjugation
  have h_lift_conj : liftClassFun H χ (s⁻¹ * g * s) = liftClassFun H χ g := by
    dsimp [liftClassFun]
    rw [h_ind_conj (fun h' => χ h' - χ 1)]
  -- We know χ̃(h) = χ(h) for h ∈ H, and χ̃(1) = χ(1)
  have h_restrict_h : liftClassFun H χ (s⁻¹ * g * s) = χ ⟨s⁻¹ * g * s, h_mem⟩ :=
    liftClassFun_restricts hF x₀ hχ_class ⟨s⁻¹ * g * s, h_mem⟩
  have h_restrict_one : liftClassFun H χ 1 = χ 1 :=
    liftClassFun_restricts hF x₀ hχ_class 1
  -- Now we have χ̃(g) = χ̃(h) = χ(h) ≠ χ(1) = χ̃(1), contradicting hg
  have h_contra : liftClassFun H χ g ≠ liftClassFun H χ 1 := by
    calc
      liftClassFun H χ g = liftClassFun H χ (s⁻¹ * g * s) := by
        rw [h_lift_conj]
      _ = χ ⟨s⁻¹ * g * s, h_mem⟩ := h_restrict_h
      _ ≠ χ 1 := hχ_ne
      _ = liftClassFun H χ 1 := by
        rw [h_restrict_one]
  exact h_contra (hg χ hχ_irr)

/-- **The intersection of lifted kernels is the Frobenius kernel**
(`lem:intersection-equals-kernel`): `⋂_χ ker χ̃ = K` as subsets of `G`. -/
theorem intersection_equals_kernel (hF : FrobeniusHypotheses G X) (x₀ : X)
    [Fintype ↥(stabilizer G x₀)] :
    {g : G | ∀ χ : ↥(stabilizer G x₀) → ℂ, IsIrreducibleCharacter (Γ := ↥(stabilizer G x₀)) χ →
        liftClassFun (stabilizer G x₀) χ g = liftClassFun (stabilizer G x₀) χ 1}
      = frobeniusKernel G X := by
  ext g
  constructor
  · intro hg
    exact intersection_subset_kernel hF x₀ hg
  · intro hg
    intro χ hχ
    have hχ_class : IsClassFunction (Γ := ↥(stabilizer G x₀)) χ := by
      rcases hχ with ⟨V, hV_simple, hV_char⟩
      rw [hV_char]
      intro s γ
      simpa using FDRep.char_conj V γ s
    exact frobenius_kernel_in_each hF x₀ hχ_class hg

end GroupTheory
end LeanEval
