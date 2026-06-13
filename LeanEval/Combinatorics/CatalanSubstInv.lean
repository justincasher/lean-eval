import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.Data.Nat.Choose.Central
import EvalTools.Markers

namespace LeanEval
namespace Combinatorics

open PowerSeries

/-!
The Catalan generating function via compositional inversion.

The Catalan numbers `C_n = (2n choose n) / (n + 1)` arise as the coefficients of the
compositional inverse of the power series `X - X²`. This is one of the most classical
applications of Lagrange inversion in enumerative combinatorics: the generating function
`C(x) = ∑ C_n x^{n+1}` satisfies `C(x) - C(x)² = x`, so `C` is the compositional inverse
of the polynomial `P(x) = x - x²`.

Equivalently, `C(x) = (1 - √(1 - 4x)) / 2`.

This identity connects formal power series inversion (`substInv`) to the enumeration of
Dyck paths, binary trees, triangulations of polygons, and many other combinatorial structures.
-/

/-- The Catalan generating function with rational coefficients, obtained from Mathlib's
`catalanSeries ∈ ℕ⟦X⟧` by applying the coefficient map induced by `ℕ → ℚ`. Its `n`-th
coefficient is `(catalan n : ℚ)`. -/
noncomputable def catalanSeriesRat : ℚ⟦X⟧ :=
  PowerSeries.map (Nat.castRingHom ℚ) catalanSeries

/-- The leading coefficient `[X¹] (X - X²) = 1` is invertible, which is what `substInv`
requires of `X - X²`. -/
instance invertible_coeff_one_X_sub_X_sq :
    Invertible (coeff 1 ((X : ℚ⟦X⟧) - X ^ 2)) := by
  simp [coeff_X, coeff_X_pow]; exact invertibleOne

/-- **Substituting into `X - X²`.** For any `D ∈ ℚ⟦X⟧` with zero constant term, substituting
`D` into `X - X²` equals `D - D²`. -/
lemma subst_X_sub_X_sq (D : ℚ⟦X⟧) (hD : constantCoeff D = 0) :
    subst D ((X : ℚ⟦X⟧) - X ^ 2) = D - D ^ 2 := by
  sorry

/-- **Catalan series identity over `ℚ`.** The rational Catalan series satisfies
`Ĉ² · X + 1 = Ĉ`. -/
lemma catalanSeriesRat_sq_mul_X_add_one :
    catalanSeriesRat ^ 2 * X + 1 = catalanSeriesRat := by
  sorry

/-- **The shifted series inverts `X - X²`.** Writing `D = X · Ĉ`, we have `D - D² = X`. -/
lemma X_mul_catalanSeriesRat_sub_sq :
    (X * catalanSeriesRat) - (X * catalanSeriesRat) ^ 2 = (X : ℚ⟦X⟧) := by
  sorry

/-- **`X - X²` is substitutable.** Its constant coefficient vanishes, so it `HasSubst`. -/
lemma hasSubst_X_sub_X_sq : HasSubst ((X : ℚ⟦X⟧) - X ^ 2) := by
  sorry

/-- **Uniqueness of the compositional inverse.** If `D` has zero constant term and substituting
`D` into `X - X²` gives `X`, then `D` is the compositional inverse of `X - X²`. -/
lemma substInv_eq_of_subst_eq_X (D : ℚ⟦X⟧) (hD : constantCoeff D = 0)
    (h : subst D ((X : ℚ⟦X⟧) - X ^ 2) = X) :
    D = substInv ((X : ℚ⟦X⟧) - X ^ 2) := by
  sorry

/-- **Identification of the inverse.** The compositional inverse of `X - X²` is `X · Ĉ`. -/
lemma substInv_X_sub_X_sq_eq :
    substInv ((X : ℚ⟦X⟧) - X ^ 2) = X * catalanSeriesRat := by
  sorry

/-- **Closed form of the Catalan number over `ℚ`.** `catalan n = (2n choose n) / (n + 1)`. -/
lemma catalan_rat_eq (n : ℕ) :
    (catalan n : ℚ) = (Nat.choose (2 * n) n : ℚ) / (n + 1) := by
  sorry

@[eval_problem]
theorem substInv_X_sub_X_sq_eq_catalan (n : ℕ) :
    haveI : Invertible (coeff 1 ((X : ℚ⟦X⟧) - X ^ 2)) := by
      simp [coeff_X, coeff_X_pow]; exact invertibleOne
    coeff (n + 1) (substInv ((X : ℚ⟦X⟧) - X ^ 2)) =
      (Nat.choose (2 * n) n : ℚ) / (↑n + 1) := by
  sorry

end Combinatorics
end LeanEval
