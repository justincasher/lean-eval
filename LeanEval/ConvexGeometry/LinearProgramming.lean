import Mathlib
import EvalTools.Markers

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

/-- **The self dot product of a nonzero vector is positive** (§101). For
`c ∈ ℝ^m` with `c ≠ 0`, one has `0 < c ⬝ᵥ c`. -/
theorem dotProduct_self_pos {m : ℕ} {c : Fin m → ℝ} (hc : c ≠ 0) :
    0 < c ⬝ᵥ c := by
  sorry

/-- **Moving along `c` strictly increases the objective** (§101). For
`c ≠ 0`, any `x`, and `t > 0`, one has `c ⬝ᵥ x < c ⬝ᵥ (x + t • c)`. -/
theorem dotProduct_lt_add_smul_self {m : ℕ} {c : Fin m → ℝ} (hc : c ≠ 0)
    (x : Fin m → ℝ) {t : ℝ} (ht : 0 < t) : c ⬝ᵥ x < c ⬝ᵥ (x + t • c) := by
  sorry

/-- A **linear program** in standard inequality form on `ℝ^m` with `n`
constraints: maximise `c · x` subject to `A x ≤ b` and `0 ≤ x`. -/
structure LinearProgram (m n : ℕ) where
  /-- Coefficient vector of the objective `c · x`. -/
  c : Fin m → ℝ
  /-- Right-hand side of the inequality constraints `A x ≤ b`. -/
  b : Fin n → ℝ
  /-- Constraint matrix. -/
  A : Matrix (Fin n) (Fin m) ℝ

namespace LinearProgram

variable {m n : ℕ}

/-- The **feasible region** of `lp`: the vectors `x ∈ ℝ^m` with `A x ≤ b` and
`0 ≤ x`, a convex polyhedron in `ℝ^m`. -/
def feasible (lp : LinearProgram m n) : Set (Fin m → ℝ) :=
  {x | lp.A *ᵥ x ≤ lp.b ∧ 0 ≤ x}

/-- The **objective** `f(x) = c · x`. -/
def objective (lp : LinearProgram m n) (x : Fin m → ℝ) : ℝ :=
  lp.c ⬝ᵥ x

/-- The **set of global maximisers** of the objective on the feasible region. -/
def maximizerSet (lp : LinearProgram m n) : Set (Fin m → ℝ) :=
  {x | x ∈ lp.feasible ∧ ∀ y ∈ lp.feasible, lp.objective y ≤ lp.objective x}

/-- **Feasible region as an intersection of half-spaces** (§101). The feasible
region is the intersection of the half-spaces `(A x)_i ≤ b_i` over rows `i` and
`0 ≤ x_j` over coordinates `j`. -/
theorem feasible_eq_iInter (lp : LinearProgram m n) :
    lp.feasible =
      (⋂ i, {x : Fin m → ℝ | (lp.A *ᵥ x) i ≤ lp.b i}) ∩
        (⋂ j, {x : Fin m → ℝ | 0 ≤ x j}) := by
  sorry

/-- **Each constraint row is a continuous linear functional** (§101). For each
constraint row `i`, the map `x ↦ (A x)_i` is linear and continuous. -/
theorem mulVec_coord_isLinear_continuous (lp : LinearProgram m n) (i : Fin n) :
    IsLinearMap ℝ (fun x : Fin m → ℝ => (lp.A *ᵥ x) i) ∧
      Continuous (fun x : Fin m → ℝ => (lp.A *ᵥ x) i) := by
  sorry

/-- **Feasible region is convex** (§101). -/
theorem feasible_convex (lp : LinearProgram m n) : Convex ℝ lp.feasible := by
  sorry

/-- **Objective is concave** (§101). The objective is a concave function on the
feasible region. -/
theorem objective_concaveOn (lp : LinearProgram m n) :
    ConcaveOn ℝ lp.feasible lp.objective := by
  sorry

/-- **Local maximisers are global** (§101). A feasible local maximiser of the
objective on the feasible region is a global maximiser. -/
theorem isMaxOn_of_isLocalMaxOn (lp : LinearProgram m n) {x : Fin m → ℝ}
    (hx : x ∈ lp.feasible) (hlocal : IsLocalMaxOn lp.objective lp.feasible x) :
    IsMaxOn lp.objective lp.feasible x := by
  sorry

/-- **A small step stays feasible** (§101). If `B(x, ε) ⊆ feasible` and
`t * ‖c‖ < ε` with `t > 0`, then `x + t • c` is feasible. -/
theorem add_smul_mem_feasible (lp : LinearProgram m n) {x : Fin m → ℝ} {ε : ℝ}
    (hε : 0 < ε) (hball : Metric.ball x ε ⊆ lp.feasible) {t : ℝ} (ht : 0 < t)
    (htc : t * ‖lp.c‖ < ε) : x + t • lp.c ∈ lp.feasible := by
  sorry

/-- **A feasible ball yields a strictly better feasible point** (§101). If
`B(x, ε) ⊆ feasible` and `c ≠ 0`, then there is a feasible `y` with
`objective x < objective y`. -/
theorem exists_mem_feasible_objective_lt (lp : LinearProgram m n) {x : Fin m → ℝ}
    {ε : ℝ} (hε : 0 < ε) (hball : Metric.ball x ε ⊆ lp.feasible)
    (hc : lp.c ≠ 0) : ∃ y ∈ lp.feasible, lp.objective x < lp.objective y := by
  sorry

/-- **A maximiser is not interior** (§101). If `x` is a global maximiser and
`c ≠ 0`, then `x` is not in the interior of the feasible region. -/
theorem not_mem_interior_of_isMaxOn (lp : LinearProgram m n) {x : Fin m → ℝ}
    (hmax : IsMaxOn lp.objective lp.feasible x) (hc : lp.c ≠ 0) :
    x ∉ interior lp.feasible := by
  sorry

/-- **Maximiser lies on the frontier** (§101). If `x` is feasible, a global
maximiser, and `c ≠ 0`, then `x` lies on the frontier of the feasible region. -/
theorem mem_frontier_of_isMaxOn (lp : LinearProgram m n) {x : Fin m → ℝ}
    (hx : x ∈ lp.feasible) (hmax : IsMaxOn lp.objective lp.feasible x)
    (hc : lp.c ≠ 0) : x ∈ frontier lp.feasible := by
  sorry

/-- **Feasible region is closed** (§101). -/
theorem feasible_isClosed (lp : LinearProgram m n) : IsClosed lp.feasible := by
  sorry

/-- **Bounded feasible regions are compact** (§101). -/
theorem feasible_isCompact (lp : LinearProgram m n)
    (hbdd : Bornology.IsBounded lp.feasible) : IsCompact lp.feasible := by
  sorry

/-- **The objective as a continuous linear map** (§101). The objective is linear
and continuous. -/
theorem objective_isLinear_continuous (lp : LinearProgram m n) :
    IsLinearMap ℝ lp.objective ∧ Continuous lp.objective := by
  sorry

/-- **The maximiser set is an extreme subset** (§101). The set of global
maximisers is an exposed (hence extreme) subset of the feasible region. -/
theorem maximizerSet_isExposed (lp : LinearProgram m n) :
    IsExposed ℝ lp.feasible lp.maximizerSet := by
  sorry

/-- **The maximiser set is compact** (§101). If the feasible region is bounded,
the maximiser set is compact. -/
theorem maximizerSet_isCompact (lp : LinearProgram m n)
    (hbdd : Bornology.IsBounded lp.feasible) : IsCompact lp.maximizerSet := by
  sorry

/-- **The maximiser set is nonempty** (§101). If the feasible region is nonempty
and bounded, the maximiser set is nonempty. -/
theorem maximizerSet_nonempty (lp : LinearProgram m n)
    (hfeas : lp.feasible.Nonempty) (hbdd : Bornology.IsBounded lp.feasible) :
    lp.maximizerSet.Nonempty := by
  sorry

end LinearProgram

/-- **Maximum principle for linear programming** (§101). A local maximiser of
the LP objective on the feasible region is automatically a global maximiser; and
whenever the objective is non-constant (`c ≠ 0`), the maximiser lies on the
topological frontier of the feasible region. -/
@[eval_problem]
theorem lp_maximum_principle {m n : ℕ} (lp : LinearProgram m n)
    (x : Fin m → ℝ) (_hx : x ∈ lp.feasible)
    (_hlocal : IsLocalMaxOn lp.objective lp.feasible x) :
    IsMaxOn lp.objective lp.feasible x ∧
      (lp.c ≠ 0 → x ∈ frontier lp.feasible) := by
  sorry

/-- **Vertex optimality** (§101; the existence content of Dantzig's 1947 simplex
algorithm). Every linear program with a nonempty bounded feasible region admits a
global maximiser that is an extreme point (vertex) of the feasible region. -/
@[eval_problem]
theorem simplex_algorithm {m n : ℕ} (lp : LinearProgram m n)
    (_hfeas : lp.feasible.Nonempty) (_hbdd : Bornology.IsBounded lp.feasible) :
    ∃ x ∈ lp.feasible, IsMaxOn lp.objective lp.feasible x ∧
      x ∈ Set.extremePoints ℝ lp.feasible := by
  sorry

end ConvexGeometry
end LeanEval
