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
  have hnonneg : 0 ≤ c ⬝ᵥ c :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg (c i)
  have hne : c ⬝ᵥ c ≠ 0 := mt (dotProduct_self_eq_zero.mp) hc
  exact lt_of_le_of_ne hnonneg hne.symm

/-- **Moving along `c` strictly increases the objective** (§101). For
`c ≠ 0`, any `x`, and `t > 0`, one has `c ⬝ᵥ x < c ⬝ᵥ (x + t • c)`. -/
theorem dotProduct_lt_add_smul_self {m : ℕ} {c : Fin m → ℝ} (hc : c ≠ 0)
    (x : Fin m → ℝ) {t : ℝ} (ht : 0 < t) : c ⬝ᵥ x < c ⬝ᵥ (x + t • c) := by
  have hpos : 0 < c ⬝ᵥ c := dotProduct_self_pos hc
  have hpos_smul : 0 < t • (c ⬝ᵥ c) := by
    rw [smul_eq_mul]
    exact mul_pos ht hpos
  calc
    c ⬝ᵥ x < c ⬝ᵥ x + t • (c ⬝ᵥ c) := by
      exact lt_add_of_pos_right _ hpos_smul
    _ = c ⬝ᵥ x + c ⬝ᵥ (t • c) := by
      rw [dotProduct_smul]
    _ = c ⬝ᵥ (x + t • c) := by
      rw [dotProduct_add]

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
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hAx, hx_nonneg⟩
    have hAx' := Pi.le_def.mp hAx
    have hx_nonneg' := Pi.le_def.mp hx_nonneg
    constructor
    · apply Set.mem_iInter.mpr
      intro i
      simpa using hAx' i
    · apply Set.mem_iInter.mpr
      intro j
      simpa [Pi.zero_apply] using hx_nonneg' j
  · intro hx
    rcases hx with ⟨hAx, hx_nonneg⟩
    have hAx' := Set.mem_iInter.mp hAx
    have hx_nonneg' := Set.mem_iInter.mp hx_nonneg
    refine ⟨Pi.le_def.mpr hAx', Pi.le_def.mpr hx_nonneg'⟩

/-- **Each constraint row is a continuous linear functional** (§101). For each
constraint row `i`, the map `x ↦ (A x)_i` is linear and continuous. -/
theorem mulVec_coord_isLinear_continuous (lp : LinearProgram m n) (i : Fin n) :
    IsLinearMap ℝ (fun x : Fin m → ℝ => (lp.A *ᵥ x) i) ∧
      Continuous (fun x : Fin m → ℝ => (lp.A *ᵥ x) i) := by
  let f : (Fin m → ℝ) →ₗ[ℝ] ℝ :=
    (LinearMap.proj i).comp (Matrix.mulVecLin lp.A)
  have h_lin : IsLinearMap ℝ (fun x : Fin m → ℝ => (lp.A *ᵥ x) i) := f.isLinear
  have h_cont : Continuous (fun x : Fin m → ℝ => (lp.A *ᵥ x) i) := by
    -- `Fin m → ℝ` is finite-dimensional because `Fin m` is finite,
    -- so every linear map out of it is continuous.
    have : FiniteDimensional ℝ (Fin m → ℝ) := inferInstance
    exact f.continuous_of_finiteDimensional
  exact And.intro h_lin h_cont

/-- **Feasible region is convex** (§101). -/
theorem feasible_convex (lp : LinearProgram m n) : Convex ℝ lp.feasible := by
  rw [feasible_eq_iInter]
  refine (convex_iInter ?_).inter (convex_iInter ?_)
  · intro i
    have hlin := (mulVec_coord_isLinear_continuous lp i).1
    exact convex_halfSpace_le hlin (lp.b i)
  · intro j
    have hlin : IsLinearMap ℝ (fun (x : Fin m → ℝ) => x j) :=
      { map_add := by intro x y; rfl
        map_smul := by intro r x; rfl }
    exact convex_halfSpace_ge hlin 0

/-- **Objective is concave** (§101). The objective is a concave function on the
feasible region. -/
theorem objective_concaveOn (lp : LinearProgram m n) :
    ConcaveOn ℝ lp.feasible lp.objective := by
  have hconvex : Convex ℝ lp.feasible := feasible_convex lp
  have h_concave : ConcaveOn ℝ lp.feasible (fun x : Fin m → ℝ => lp.c ⬝ᵥ x) := by
    let f : (Fin m → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun x => lp.c ⬝ᵥ x
        map_add' := by
          intro x y
          rw [dotProduct_add]
        map_smul' := by
          intro r x
          simp [dotProduct_smul]
      }
    exact LinearMap.concaveOn f hconvex
  simpa [objective]

/-- **Local maximisers are global** (§101). A feasible local maximiser of the
objective on the feasible region is a global maximiser. -/
theorem isMaxOn_of_isLocalMaxOn (lp : LinearProgram m n) {x : Fin m → ℝ}
    (hx : x ∈ lp.feasible) (hlocal : IsLocalMaxOn lp.objective lp.feasible x) :
    IsMaxOn lp.objective lp.feasible x :=
  IsMaxOn.of_isLocalMaxOn_of_concaveOn hx hlocal (lp.objective_concaveOn)

/-- **A small step stays feasible** (§101). If `B(x, ε) ⊆ feasible` and
`t * ‖c‖ < ε` with `t > 0`, then `x + t • c` is feasible. -/
theorem add_smul_mem_feasible (lp : LinearProgram m n) {x : Fin m → ℝ} {ε : ℝ}
    (_hε : 0 < ε) (hball : Metric.ball x ε ⊆ lp.feasible) {t : ℝ} (ht : 0 < t)
    (htc : t * ‖lp.c‖ < ε) : x + t • lp.c ∈ lp.feasible := by
  have hmem : x + t • lp.c ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    have : (x + t • lp.c) - x = t • lp.c := by simp
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    exact htc
  exact hball hmem

/-- **A feasible ball yields a strictly better feasible point** (§101). If
`B(x, ε) ⊆ feasible` and `c ≠ 0`, then there is a feasible `y` with
`objective x < objective y`. -/
theorem exists_mem_feasible_objective_lt (lp : LinearProgram m n) {x : Fin m → ℝ}
    {ε : ℝ} (hε : 0 < ε) (hball : Metric.ball x ε ⊆ lp.feasible)
    (hc : lp.c ≠ 0) : ∃ y ∈ lp.feasible, lp.objective x < lp.objective y := by
  have hc_norm_pos : 0 < ‖lp.c‖ := by
    rwa [norm_pos_iff]
  set t := ε / (2 * ‖lp.c‖) with ht_def
  have ht_pos : 0 < t := by
    refine div_pos hε ?_
    nlinarith
  have htc : t * ‖lp.c‖ < ε := by
    calc
      t * ‖lp.c‖ = (ε / (2 * ‖lp.c‖)) * ‖lp.c‖ := rfl
      _ = ε / 2 := by
        field_simp [hc_norm_pos.ne.symm]
      _ < ε := by nlinarith
  have hy_feasible : x + t • lp.c ∈ lp.feasible :=
    add_smul_mem_feasible lp hε hball ht_pos htc
  have h_objective_lt : lp.objective x < lp.objective (x + t • lp.c) := by
    dsimp [objective]
    exact dotProduct_lt_add_smul_self hc x ht_pos
  exact ⟨x + t • lp.c, hy_feasible, h_objective_lt⟩

/-- **A maximiser is not interior** (§101). If `x` is a global maximiser and
`c ≠ 0`, then `x` is not in the interior of the feasible region. -/
theorem not_mem_interior_of_isMaxOn (lp : LinearProgram m n) {x : Fin m → ℝ}
    (hmax : IsMaxOn lp.objective lp.feasible x) (hc : lp.c ≠ 0) :
    x ∉ interior lp.feasible := by
  intro hxint
  have h_open : IsOpen (interior lp.feasible) := isOpen_interior
  rcases Metric.isOpen_iff.mp h_open x hxint with ⟨ε, hε, hball⟩
  -- hball : Metric.ball x ε ⊆ interior lp.feasible
  have hball_feas : Metric.ball x ε ⊆ lp.feasible :=
    hball.trans interior_subset
  rcases exists_mem_feasible_objective_lt lp hε hball_feas hc with ⟨y, hy, hlt⟩
  have hineq : lp.objective y ≤ lp.objective x := by
    simpa using hmax hy
  linarith

/-- **Maximiser lies on the frontier** (§101). If `x` is feasible, a global
maximiser, and `c ≠ 0`, then `x` lies on the frontier of the feasible region. -/
theorem mem_frontier_of_isMaxOn (lp : LinearProgram m n) {x : Fin m → ℝ}
    (hx : x ∈ lp.feasible) (hmax : IsMaxOn lp.objective lp.feasible x)
    (hc : lp.c ≠ 0) : x ∈ frontier lp.feasible := by
  have hx_not_interior : x ∉ interior lp.feasible :=
    not_mem_interior_of_isMaxOn lp hmax hc
  exact ((mem_frontier_iff_notMem_interior hx).mpr hx_not_interior)

/-- **Feasible region is closed** (§101). -/
theorem feasible_isClosed (lp : LinearProgram m n) : IsClosed lp.feasible := by
  rw [feasible_eq_iInter]
  refine IsClosed.inter (isClosed_iInter ?_) (isClosed_iInter ?_)
  · intro i
    exact isClosed_le ((mulVec_coord_isLinear_continuous lp i).2)
      (continuous_const : Continuous fun (_ : Fin m → ℝ) => lp.b i)
  · intro j
    exact isClosed_le (continuous_const : Continuous fun (_ : Fin m → ℝ) => (0 : ℝ))
      (continuous_apply j)

/-- **Bounded feasible regions are compact** (§101). -/
theorem feasible_isCompact (lp : LinearProgram m n)
    (hbdd : Bornology.IsBounded lp.feasible) : IsCompact lp.feasible := by
  have hclosed : IsClosed lp.feasible := feasible_isClosed lp
  exact Metric.isCompact_of_isClosed_isBounded hclosed hbdd

/-- **The objective as a continuous linear map** (§101). The objective is linear
and continuous. -/
theorem objective_isLinear_continuous (lp : LinearProgram m n) :
    IsLinearMap ℝ lp.objective ∧ Continuous lp.objective := by
  have h_lin : IsLinearMap ℝ lp.objective := by
    refine IsLinearMap.mk ?_ ?_
    · intro x y
      simp [objective, dotProduct_add]
    · intro r x
      simp [objective, dotProduct_smul]
  have h_cont : Continuous lp.objective := by
    let f : (Fin m → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := lp.objective
        map_add' := by
          intro x y; simp [objective, dotProduct_add]
        map_smul' := by
          intro r x; simp [objective, dotProduct_smul] }
    have : FiniteDimensional ℝ (Fin m → ℝ) := by infer_instance
    exact f.continuous_of_finiteDimensional
  exact And.intro h_lin h_cont

/-- **The maximiser set is an extreme subset** (§101). The set of global
maximisers is an exposed (hence extreme) subset of the feasible region. -/
theorem maximizerSet_isExposed (lp : LinearProgram m n) :
    IsExposed ℝ lp.feasible lp.maximizerSet := by
  -- Construct the objective as a continuous linear functional
  let f : (Fin m → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := lp.objective
      map_add' := by
        intro x y
        simp [objective, dotProduct_add]
      map_smul' := by
        intro r x
        simp [objective, dotProduct_smul]
    }
  have h_cont : Continuous f :=
    f.continuous_of_finiteDimensional
  let l : StrongDual ℝ (Fin m → ℝ) :=
    { toFun := f
      map_add' := f.map_add'
      map_smul' := f.map_smul'
      cont := h_cont
    }
  have h_eq : lp.maximizerSet = l.toExposed lp.feasible := by
    ext x
    simp [maximizerSet, ContinuousLinearMap.toExposed, objective, l, f]
  rw [h_eq]
  exact ContinuousLinearMap.toExposed.isExposed (l := l) (A := lp.feasible)

/-- **The maximiser set is compact** (§101). If the feasible region is bounded,
the maximiser set is compact. -/
theorem maximizerSet_isCompact (lp : LinearProgram m n)
    (hbdd : Bornology.IsBounded lp.feasible) : IsCompact lp.maximizerSet := by
  have h_exposed : IsExposed ℝ lp.feasible lp.maximizerSet := lp.maximizerSet_isExposed
  have h_closed_feasible : IsClosed lp.feasible := lp.feasible_isClosed
  have h_closed : IsClosed lp.maximizerSet := h_exposed.isClosed h_closed_feasible
  have h_subset : lp.maximizerSet ⊆ lp.feasible := by
    intro x hx
    rw [maximizerSet] at hx
    exact hx.1
  have h_compact_feasible : IsCompact lp.feasible := lp.feasible_isCompact hbdd
  exact h_compact_feasible.of_isClosed_subset h_closed h_subset

/-- **The maximiser set is nonempty** (§101). If the feasible region is nonempty
and bounded, the maximiser set is nonempty. -/
theorem maximizerSet_nonempty (lp : LinearProgram m n)
    (hfeas : lp.feasible.Nonempty) (hbdd : Bornology.IsBounded lp.feasible) :
    lp.maximizerSet.Nonempty := by
  have h_compact : IsCompact lp.feasible := feasible_isCompact lp hbdd
  have h_cont : Continuous lp.objective := (objective_isLinear_continuous lp).2
  have h_cont_on : ContinuousOn lp.objective lp.feasible := h_cont.continuousOn
  rcases h_compact.exists_isMaxOn hfeas h_cont_on with ⟨x, hx, hx_max⟩
  refine ⟨x, ?_⟩
  rw [LinearProgram.maximizerSet, Set.mem_setOf_eq]
  exact And.intro hx hx_max

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
  have hmax : IsMaxOn lp.objective lp.feasible x :=
    LinearProgram.isMaxOn_of_isLocalMaxOn lp _hx _hlocal
  refine ⟨hmax, ?_⟩
  intro hc
  exact LinearProgram.mem_frontier_of_isMaxOn lp _hx hmax hc

/-- **Vertex optimality** (§101; the existence content of Dantzig's 1947 simplex
algorithm). Every linear program with a nonempty bounded feasible region admits a
global maximiser that is an extreme point (vertex) of the feasible region. -/
@[eval_problem]
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
