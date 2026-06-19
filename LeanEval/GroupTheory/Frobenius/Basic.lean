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
  sorry

/-- **Dichotomy for non-identity elements** (`lem:partition`).
A non-identity `g` either fixes no point of `X`, or fixes exactly one point. -/
theorem partition (hF : FrobeniusHypotheses G X) {g : G} (hg : g ≠ 1) :
    (∀ x : X, g • x ≠ x) ∨ ∃! x : X, g • x = x := by
  sorry

/-- **Conjugators carrying a non-identity element of `H` into `H` lie in `H`**
(`lem:conjugators-into-H-are-H`), with `H = Stab(x₀)`. -/
theorem conjugators_into_H (hF : FrobeniusHypotheses G X) (x₀ : X) {h : G}
    (hhH : h ∈ stabilizer G x₀) (hh1 : h ≠ 1) {x : G}
    (hx : x⁻¹ * h * x ∈ stabilizer G x₀) : x ∈ stabilizer G x₀ := by
  sorry

/-- **A point-fixing non-identity element is conjugate into `H ∖ {1}`**
(`lem:non-kernel-conjugate-to-H`), with `H = Stab(x₀)`. -/
theorem non_kernel_conjugate_to_H (hF : FrobeniusHypotheses G X) (x₀ : X) {g : G}
    (hg : g ≠ 1) (hgK : ¬ ∀ x : X, g • x ≠ x) :
    ∃ s : G, s⁻¹ * g * s ∈ stabilizer G x₀ ∧ s⁻¹ * g * s ≠ 1 := by
  sorry

end GroupTheory
end LeanEval
