import Mathlib
import EvalTools.Markers

/-!
# Frobenius groups: basic definitions and the elementary group-theoretic lemmas

This file collects the purely group-theoretic part of Frobenius's theorem: the
bundle of Frobenius hypotheses, the Frobenius kernel, and the consequences of the
Frobenius condition (trivial intersection of distinct stabilisers, the dichotomy
for non-identity elements, and the conjugation lemmas about the point stabiliser
`H = Stab(x₀)`).
-/

namespace LeanEval
namespace GroupTheory

open MulAction

variable {G X : Type*} [Group G] [MulAction G X]

/-- **Frobenius group hypotheses** (`def:frobenius-hypotheses`).

The bundle of hypotheses on a finite group `G` acting on a finite set `X`:
(i) the action is faithful; (ii) it is transitive; (iii) `|X| ≥ 2`; (iv) every
point stabiliser is non-trivial; and (v) the *Frobenius condition*: no
non-identity element fixes two distinct points. -/
structure FrobeniusHypotheses (G X : Type*) [Group G] [MulAction G X] : Prop where
  /-- The action is faithful. -/
  faithful : ∀ g : G, (∀ x : X, g • x = x) → g = 1
  /-- The action is transitive. -/
  exists_smul_eq : ∀ x y : X, ∃ g : G, g • x = y
  /-- `|X| ≥ 2`. -/
  two_le_card : 2 ≤ Nat.card X
  /-- Every point stabiliser is non-trivial. -/
  stabilizer_ne_bot : ∀ x : X, stabilizer G x ≠ ⊥
  /-- The Frobenius condition: no non-identity element fixes two distinct points. -/
  frobenius : ∀ g : G, g ≠ 1 → ∀ x y : X, g • x = x → g • y = y → x = y

/-- **The Frobenius kernel** (`def:frobenius-kernel`): the identity together with
all elements acting without a fixed point. -/
def frobeniusKernel (G X : Type*) [Group G] [MulAction G X] : Set G :=
  {1} ∪ {g : G | ∀ x : X, g • x ≠ x}

/-- **Trivial intersection of distinct stabilisers** (`lem:trivial-intersection`).
If `x ≠ y` then `Stab(x) ⊓ Stab(y) = ⊥`. -/
theorem stabilizer_inf_eq_bot (hF : FrobeniusHypotheses G X) {x y : X} (hxy : x ≠ y) :
    stabilizer G x ⊓ stabilizer G y = ⊥ := by
  apply Subgroup.ext
  intro g
  constructor
  · intro hg
    have hgx : g • x = x := (MulAction.mem_stabilizer_iff.mp hg.1)
    have hgy : g • y = y := (MulAction.mem_stabilizer_iff.mp hg.2)
    by_contra hg1
    have : x = y := hF.frobenius g hg1 x y hgx hgy
    exact hxy this
  · intro hg
    have hg1 : g = 1 := (Subgroup.mem_bot.mp hg)
    subst hg1
    have hx1 : (1 : G) ∈ stabilizer G x := by
      rw [MulAction.mem_stabilizer_iff, one_smul]
    have hy1 : (1 : G) ∈ stabilizer G y := by
      rw [MulAction.mem_stabilizer_iff, one_smul]
    exact Subgroup.mem_inf.mpr ⟨hx1, hy1⟩

/-- **Dichotomy for non-identity elements** (`lem:partition`).
A non-identity `g` either fixes no point of `X`, or fixes exactly one point. -/
theorem partition (hF : FrobeniusHypotheses G X) {g : G} (hg : g ≠ 1) :
    (∀ x : X, g • x ≠ x) ∨ ∃! x : X, g • x = x := by
  by_cases h : ∀ x : X, g • x ≠ x
  · exact Or.inl h
  · rcases not_forall.mp h with ⟨x, hx⟩
    have hx' : g • x = x := by
      simpa using hx
    refine Or.inr ⟨x, hx', ?_⟩
    intro y hy
    exact (hF.frobenius g hg x y hx' hy).symm

/-- **Conjugators carrying a non-identity element of `H` into `H` lie in `H`**
(`lem:conjugators-into-H-are-H`), with `H = Stab(x₀)`. -/
theorem conjugators_into_H (hF : FrobeniusHypotheses G X) (x₀ : X) {h : G}
    (hhH : h ∈ stabilizer G x₀) (hh1 : h ≠ 1) {x : G}
    (hx : x⁻¹ * h * x ∈ stabilizer G x₀) : x ∈ stabilizer G x₀ := by
  -- h fixes x₀
  have hh_fixed : h • x₀ = x₀ := mem_stabilizer_iff.mp hhH
  -- the conjugate (x⁻¹ * h * x) fixes x₀
  have hx_fixed : (x⁻¹ * h * x) • x₀ = x₀ := mem_stabilizer_iff.mp hx
  -- rewrite the conjugate action: (x⁻¹ * h * x) • x₀ = x⁻¹ • (h • (x • x₀))
  have h_temp : x⁻¹ • (h • (x • x₀)) = x₀ := by
    calc
      x⁻¹ • (h • (x • x₀)) = (x⁻¹ * h * x) • x₀ := by
        simp [mul_smul]
      _ = x₀ := hx_fixed
  -- therefore h also fixes (x • x₀)
  have h_fixed_xx₀ : h • (x • x₀) = x • x₀ := by
    calc
      h • (x • x₀) = (x * x⁻¹) • (h • (x • x₀)) := by simp
      _ = x • (x⁻¹ • (h • (x • x₀))) := by rw [mul_smul]
      _ = x • x₀ := by simp [h_temp]
  -- now h ≠ 1 fixes both x₀ and (x • x₀)
  by_cases h_eq : x • x₀ = x₀
  · -- x fixes x₀, so x ∈ stabilizer G x₀
    exact mem_stabilizer_iff.mpr h_eq
  · -- if x • x₀ ≠ x₀, Frobenius condition forces a contradiction
    have h_contra : x₀ = x • x₀ := hF.frobenius h hh1 x₀ (x • x₀) hh_fixed h_fixed_xx₀
    exfalso
    exact h_eq h_contra.symm

/-- **A point-fixing non-identity element is conjugate into `H ∖ {1}`**
(`lem:non-kernel-conjugate-to-H`), with `H = Stab(x₀)`. -/
theorem non_kernel_conjugate_to_H (hF : FrobeniusHypotheses G X) (x₀ : X) {g : G}
    (hg : g ≠ 1) (hgK : ¬ ∀ x : X, g • x ≠ x) :
    ∃ s : G, s⁻¹ * g * s ∈ stabilizer G x₀ ∧ s⁻¹ * g * s ≠ 1 := by
  -- Since g ≠ 1, by the partition lemma it either fixes no point or fixes exactly one
  have h_part := partition hF hg
  rcases h_part with (h_no_fix | h_unique_fix)
  · -- g fixes no point, contradicting hgK
    exfalso; exact hgK h_no_fix
  · -- g fixes exactly one point x
    rcases h_unique_fix with ⟨x, hx_fix, hx_unique⟩
    -- By transitivity, there is s such that s • x₀ = x
    rcases hF.exists_smul_eq x₀ x with ⟨s, hs⟩
    refine ⟨s, ?_, ?_⟩
    · -- Show s⁻¹ * g * s ∈ stabilizer G x₀
      rw [MulAction.mem_stabilizer_iff]
      calc
        (s⁻¹ * g * s) • x₀ = (s⁻¹ * g) • (s • x₀) := by
          rw [SemigroupAction.mul_smul]
        _ = s⁻¹ • (g • (s • x₀)) := by
          rw [SemigroupAction.mul_smul]
        _ = s⁻¹ • (g • x) := by rw [hs]
        _ = s⁻¹ • x := by rw [hx_fix]
        _ = s⁻¹ • (s • x₀) := by rw [hs]
        _ = (s⁻¹ * s) • x₀ := by
          rw [SemigroupAction.mul_smul]
        _ = (1 : G) • x₀ := by
          rw [inv_mul_cancel]
        _ = x₀ := by
          simp
    · -- Show s⁻¹ * g * s ≠ 1
      intro h_eq
      apply hg
      calc
        g = s * (s⁻¹ * g * s) * s⁻¹ := by
          group
        _ = s * 1 * s⁻¹ := by rw [h_eq]
        _ = 1 := by group

end GroupTheory
end LeanEval
