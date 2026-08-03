import Mathlib
import ChallengeDeps
namespace LeanEval
namespace ConvexGeometry

/-!
# Linear programming: maximum principle and vertex optimality

§101 of Oliver Knill's *Some Fundamental Theorems in Mathematics*.

* **Maximum principle** (main): a local maximiser of a linear program's
  objective on the feasible region is automatically a global maximiser, and
  whenever the objective is non-constant (`c ≠ 0`) the maximiser lies on the
  topological frontier of the feasible region.
* **Vertex optimality** (additional, the existence content of Dantzig's simplex
  algorithm): every linear program with a nonempty bounded feasible region
  attains its optimum at an extreme point (vertex) of that region.

The program is the standard inequality form `maximise c · x` subject to
`A x ≤ b` and `0 ≤ x`. mathlib has the convex-geometry primitives used here
(`IsLocalMaxOn`, `IsMaxOn`, `frontier`, `Set.extremePoints`, Krein–Milman) but
neither the LP maximum principle nor the existence of an optimal vertex as named
results.
-/

open Matrix







namespace LinearProgram

variable {m n : ℕ}





































end LinearProgram

/-- **Maximum principle for linear programming** (§101). A local maximiser of
the LP objective on the feasible region is automatically a global maximiser; and
whenever the objective is non-constant (`c ≠ 0`), the maximiser lies on the
topological frontier of the feasible region. -/
theorem lp_maximum_principle {m n : ℕ} (lp : LinearProgram m n)
    (x : Fin m → ℝ) (_hx : x ∈ lp.feasible)
    (_hlocal : IsLocalMaxOn lp.objective lp.feasible x) :
    IsMaxOn lp.objective lp.feasible x ∧
      (lp.c ≠ 0 → x ∈ frontier lp.feasible) := by
  have hmax : IsMaxOn lp.objective lp.feasible x :=
    LinearProgram.isMaxOn_of_isLocalMaxOn lp _hx _hlocal
  refine ⟨hmax, ?_⟩
  intro hc
  exact LinearProgram.mem_frontier_of_isMaxOn lp _hx hmax hc

/-- **Vertex optimality** (§101; the existence content of Dantzig's 1947 simplex
algorithm). Every linear program with a nonempty bounded feasible region admits a
global maximiser that is an extreme point (vertex) of the feasible region. -/
theorem simplex_algorithm {m n : ℕ} (lp : LinearProgram m n)
    (_hfeas : lp.feasible.Nonempty) (_hbdd : Bornology.IsBounded lp.feasible) :
    ∃ x ∈ lp.feasible, IsMaxOn lp.objective lp.feasible x ∧
      x ∈ Set.extremePoints ℝ lp.feasible := by
  -- M is the maximiser set
  have hM_compact : IsCompact lp.maximizerSet :=
    lp.maximizerSet_isCompact _hbdd
  have hM_nonempty : lp.maximizerSet.Nonempty :=
    lp.maximizerSet_nonempty _hfeas _hbdd
  -- by the Krein-Milman lemma, M has an extreme point
  have h_extreme : (lp.maximizerSet.extremePoints ℝ).Nonempty :=
    hM_compact.extremePoints_nonempty hM_nonempty
  rcases h_extreme with ⟨x, hx_extreme_M⟩
  -- x ∈ M
  have hx_M : x ∈ lp.maximizerSet := hx_extreme_M.1
  -- So x is feasible and a global maximiser
  have hx_feasible : x ∈ lp.feasible := hx_M.1
  have hx_maximiser : IsMaxOn lp.objective lp.feasible x := by
    intro y hy
    exact hx_M.2 y hy
  -- Since M is an exposed (hence extreme) subset of the feasible region,
  -- an extreme point of M is an extreme point of the feasible region
  have hM_exposed : IsExposed ℝ lp.feasible lp.maximizerSet :=
    lp.maximizerSet_isExposed
  have hM_extreme : IsExtreme ℝ lp.feasible lp.maximizerSet :=
    hM_exposed.isExtreme
  have hx_extreme_feasible : x ∈ Set.extremePoints ℝ lp.feasible :=
    hM_extreme.extremePoints_subset_extremePoints hx_extreme_M
  exact ⟨x, hx_feasible, hx_maximiser, hx_extreme_feasible⟩

end ConvexGeometry
end LeanEval
