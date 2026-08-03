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
  have hD_hasSubst : HasSubst D := HasSubst.of_constantCoeff_zero hD
  calc
    subst D ((X : ℚ⟦X⟧) - X ^ 2) = subst D X - subst D (X ^ 2) := by
      rw [subst_sub hD_hasSubst]
    _ = D - subst D (X ^ 2) := by
      rw [subst_X hD_hasSubst]
    _ = D - (subst D X) ^ 2 := by
      rw [subst_pow hD_hasSubst]
    _ = D - D ^ 2 := by
      rw [subst_X hD_hasSubst]

/-- **Catalan series identity over `ℚ`.** The rational Catalan series satisfies
`Ĉ² · X + 1 = Ĉ`. -/
lemma catalanSeriesRat_sq_mul_X_add_one :
    catalanSeriesRat ^ 2 * X + 1 = catalanSeriesRat := by
  have h := congrArg (PowerSeries.map (Nat.castRingHom ℚ))
    PowerSeries.catalanSeries_sq_mul_X_add_one
  simpa [catalanSeriesRat, map_add, map_mul, map_pow, map_one, PowerSeries.map_X] using h

/-- **The shifted series inverts `X - X²`.** Writing `D = X · Ĉ`, we have `D - D² = X`. -/
lemma X_mul_catalanSeriesRat_sub_sq :
    (X * catalanSeriesRat) - (X * catalanSeriesRat) ^ 2 = (X : ℚ⟦X⟧) := by
  calc
    (X * catalanSeriesRat) - (X * catalanSeriesRat) ^ 2
        = X * catalanSeriesRat - (X ^ 2 * catalanSeriesRat ^ 2) := by ring
    _ = X * catalanSeriesRat - (X * (catalanSeriesRat ^ 2 * X)) := by ring
    _ = X * (catalanSeriesRat - catalanSeriesRat ^ 2 * X) := by ring
    _ = X * ((catalanSeriesRat ^ 2 * X + 1) - catalanSeriesRat ^ 2 * X) := by
      rw [catalanSeriesRat_sq_mul_X_add_one]
    _ = X * 1 := by ring
    _ = X := by simp

/-- **`X - X²` is substitutable.** Its constant coefficient vanishes, so it `HasSubst`. -/
lemma hasSubst_X_sub_X_sq : HasSubst ((X : ℚ⟦X⟧) - X ^ 2) := by
  refine HasSubst.of_constantCoeff_zero ?_
  calc
    constantCoeff ((X : ℚ⟦X⟧) - X ^ 2) = constantCoeff (X : ℚ⟦X⟧) - constantCoeff (X ^ 2) := by
      rw [map_sub]
    _ = constantCoeff (X : ℚ⟦X⟧) - ((constantCoeff (X : ℚ⟦X⟧)) ^ 2) := by
      rw [map_pow]
    _ = (0 : ℚ) - ((0 : ℚ) ^ 2) := by
      simp
    _ = 0 := by
      simp

/-- **Uniqueness of the compositional inverse.** If `D` has zero constant term and substituting
`D` into `X - X²` gives `X`, then `D` is the compositional inverse of `X - X²`. -/
lemma substInv_eq_of_subst_eq_X (D : ℚ⟦X⟧) (hD : constantCoeff D = 0)
    (h : subst D ((X : ℚ⟦X⟧) - X ^ 2) = X) :
    D = substInv ((X : ℚ⟦X⟧) - X ^ 2) := by
  set P := (X : ℚ⟦X⟧) - X ^ 2 with hP
  set C := substInv P with hC
  have hP_const : constantCoeff P = 0 := by
    dsimp [P]
    simp
  have hD_hasSubst : HasSubst D := HasSubst.of_constantCoeff_zero hD
  have hP_hasSubst : HasSubst P := HasSubst.of_constantCoeff_zero hP_const
  have h_substInv : subst P C = X := by
    have h_temp := subst_substInv_left (hP := hP_const) (P := P)
    simpa [hC] using h_temp
  have hDC : D = C := by
    calc
      D = subst D (X : ℚ⟦X⟧) := by
        exact (subst_X (R := ℚ) hD_hasSubst).symm
      _ = subst D (subst P C) := by rw [h_substInv]
      _ = subst (subst D P) C := by
        rw [subst_comp_subst_apply (R := ℚ) hP_hasSubst hD_hasSubst C]
      _ = subst (X : ℚ⟦X⟧) C := by rw [h]
      _ = C := by rw [X_subst (R := ℚ)]
  simpa [hP, hC] using hDC

/-- **Identification of the inverse.** The compositional inverse of `X - X²` is `X · Ĉ`. -/
lemma substInv_X_sub_X_sq_eq :
    substInv ((X : ℚ⟦X⟧) - X ^ 2) = X * catalanSeriesRat := by
  have hD_const : constantCoeff (X * catalanSeriesRat) = 0 := by
    simp
  have h_subst : subst (X * catalanSeriesRat) ((X : ℚ⟦X⟧) - X ^ 2) = X := by
    calc
      subst (X * catalanSeriesRat) ((X : ℚ⟦X⟧) - X ^ 2) = (X * catalanSeriesRat) - (X * catalanSeriesRat) ^ 2 :=
        subst_X_sub_X_sq (X * catalanSeriesRat) hD_const
      _ = X := X_mul_catalanSeriesRat_sub_sq
  have h_eq := substInv_eq_of_subst_eq_X (X * catalanSeriesRat) hD_const h_subst
  exact h_eq.symm

/-- **Closed form of the Catalan number over `ℚ`.** `catalan n = (2n choose n) / (n + 1)`. -/
lemma catalan_rat_eq (n : ℕ) :
    (catalan n : ℚ) = (Nat.choose (2 * n) n : ℚ) / (n + 1) := by
  have h_eq : (n + 1 : ℚ) * (catalan n : ℚ) = (Nat.choose (2 * n) n : ℚ) := by
    calc
      (n + 1 : ℚ) * (catalan n : ℚ) = ((n + 1 : ℕ) * catalan n : ℚ) := by simp
      _ = ((Nat.centralBinom n : ℕ) : ℚ) := by
        simpa using congrArg (fun x : ℕ => (x : ℚ)) (succ_mul_catalan_eq_centralBinom n)
      _ = (Nat.choose (2 * n) n : ℚ) := by
        simpa using congrArg (Nat.cast : ℕ → ℚ) (Nat.centralBinom_eq_two_mul_choose n)
  have hnpos : (n + 1 : ℚ) ≠ 0 := by
    have h : (Nat.succ n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    simpa [Nat.cast_succ] using h
  apply (eq_div_iff hnpos).mpr
  simpa [mul_comm] using h_eq

@[eval_problem]
theorem substInv_X_sub_X_sq_eq_catalan (n : ℕ) :
    haveI : Invertible (coeff 1 ((X : ℚ⟦X⟧) - X ^ 2)) := by
      simp [coeff_X, coeff_X_pow]; exact invertibleOne
    coeff (n + 1) (substInv ((X : ℚ⟦X⟧) - X ^ 2)) =
      (Nat.choose (2 * n) n : ℚ) / (↑n + 1) := by
  rw [substInv_X_sub_X_sq_eq, coeff_succ_X_mul]
  simp [catalanSeriesRat, catalanSeries_coeff, catalan_rat_eq]

end Combinatorics
end LeanEval
