import Mathlib
import LeanEval.Topology.Brouwer.Triangulation
import LeanEval.Topology.Brouwer.Subdivision
import LeanEval.Topology.Brouwer.FixedPoint

/-!
# Brouwer for the standard simplex

Section 5 of the Brouwer blueprint: the labeling induced by a self-map, its
Sperner property, the uniform coordinate modulus, the approximate-fixedness of
rainbow cells, and the conclusion that `S_n` has the fixed-point property.
-/

namespace LeanEval
namespace Topology

open scoped BigOperators
open Set Filter Topology

/-- **A non-increasing positive coordinate exists.** For nonnegative tuples
summing to `1`, there is an index `i` with `x i > 0` and `y i ≤ x i`. -/
theorem label_pigeonhole {n} (x y : Fin (n + 1) → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (hxs : ∑ i, x i = 1) (hys : ∑ i, y i = 1) :
    ∃ i, 0 < x i ∧ y i ≤ x i := by
  let p : Fin (n + 1) → Prop := fun i => 0 < x i
  let J : Finset (Fin (n + 1)) := Finset.filter p Finset.univ
  have hJ_nonempty : J.Nonempty := by
    have h_total_pos : 0 < ∑ i, x i := by
      rw [hxs]
      norm_num
    by_contra! hJ
    -- hJ : J = ∅. Show all x i ≤ 0, then sum ≤ 0 contradicts sum = 1 > 0
    have hx_nonpos : ∀ i, x i ≤ 0 := by
      intro i
      by_contra! hpos
      have hiJ : i ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hpos⟩
      rw [hJ] at hiJ
      exact Finset.notMem_empty i hiJ
    have hsum_nonpos : ∑ i, x i ≤ 0 :=
      Finset.sum_nonpos (fun i _ => hx_nonpos i)
    linarith
  have hzero_comp : ∀ i, i ∉ J → x i = 0 := by
    intro i hi
    have hx_nonpos : x i ≤ 0 := by
      by_contra! hpos
      apply hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hpos⟩
    have hx_nonneg := hx i
    linarith
  have h_sub : J ⊆ Finset.univ := Finset.filter_subset (p := p) Finset.univ
  have hJ_sum_x : ∑ i ∈ J, x i = 1 := by
    calc
      ∑ i ∈ J, x i = ∑ i ∈ Finset.univ, x i := by
        refine Finset.sum_subset h_sub ?_
        intro i hi_univ hi_not_J
        exact hzero_comp i hi_not_J
      _ = ∑ i, x i := rfl
      _ = 1 := hxs
  have hJ_sum_y : ∑ i ∈ J, y i ≤ 1 := by
    calc
      ∑ i ∈ J, y i ≤ ∑ i, y i :=
        Finset.sum_le_univ_sum_of_nonneg hy
      _ = 1 := hys
  have hsum_le : ∑ i ∈ J, y i ≤ ∑ i ∈ J, x i := by
    linarith
  rcases Finset.exists_le_of_sum_le hJ_nonempty hsum_le with ⟨i, hiJ, hiyx⟩
  have hposx : 0 < x i := by
    rcases Finset.mem_filter.mp hiJ with ⟨_, hpos⟩
    exact hpos
  exact ⟨i, hposx, hiyx⟩

/-- **Labeling induced by a self-map.** Given `g`, each vertex `v` is labeled by
some index `i` with `x_i(v) > 0` and `x_i(g v) ≤ x_i(v)` (existence guaranteed by
`label_pigeonhole` for points of `S_n`). -/
noncomputable def inducedLabeling {n} (g : EuclSp n → EuclSp n) (v : EuclSp n) : Fin (n + 1) :=
  if h : ∃ i, 0 < baryCoord n v i ∧ baryCoord n (g v) i ≤ baryCoord n v i then h.choose else 0

/-- For points in the corner simplex, the barycentric coordinates are nonnegative. -/
lemma cornerSimplex_baryCoord_nonneg {n} {v : EuclSp n} (hv : v ∈ cornerSimplex n)
    (i : Fin (n + 1)) : 0 ≤ baryCoord n v i :=
  (mem_cornerSimplex_iff n v).mp hv i

/-- For points in the corner simplex, the barycentric coordinates sum to 1. -/
lemma cornerSimplex_baryCoord_sum_one {n} {v : EuclSp n} (hv : v ∈ cornerSimplex n) :
    (∑ i : Fin (n + 1), baryCoord n v i) = 1 := by
  simpa [baryCoord] using (cornerBasis n).sum_coord_apply_eq_one v

/-- **The induced labeling is Sperner** for any triangulation. -/
theorem induced_is_sperner {n} (g : EuclSp n → EuclSp n)
    (hmaps : Set.MapsTo g (cornerSimplex n) (cornerSimplex n)) (T : Triangulation n) :
    IsSpernerLabeling T (inducedLabeling g) := by
  intro v hv
  have hv_corner : v ∈ cornerSimplex n := by
    rcases T.purity ({v} : Finset (EuclSp n)) hv with ⟨M, hM, hsub, hcard⟩
    have hM_max : M ∈ T.maximalCells := Finset.mem_filter.mpr ⟨hM, hcard⟩
    have hM_cover : convexHull ℝ (M : Set (EuclSp n)) ⊆ cornerSimplex n := by
      calc
        convexHull ℝ (M : Set (EuclSp n))
            ⊆ ⋃ C ∈ T.cells.filter (fun C => C.card = n + 1), convexHull ℝ (C : Set (EuclSp n)) :=
          Set.subset_biUnion hM_max
        _ = cornerSimplex n := T.covering
    have hv_M : v ∈ (M : Set (EuclSp n)) := by
      have hmem : v ∈ ({v} : Finset (EuclSp n)) := by simp
      exact Finset.mem_of_subset hsub hmem
    have hv_hull : v ∈ convexHull ℝ (M : Set (EuclSp n)) :=
      subset_convexHull ℝ (M : Set (EuclSp n)) hv_M
    exact hM_cover hv_hull
  have hgv_corner : g v ∈ cornerSimplex n := hmaps hv_corner
  have h_nonneg_v : ∀ i : Fin (n + 1), 0 ≤ baryCoord n v i :=
    cornerSimplex_baryCoord_nonneg hv_corner
  have h_nonneg_gv : ∀ i : Fin (n + 1), 0 ≤ baryCoord n (g v) i :=
    cornerSimplex_baryCoord_nonneg hgv_corner
  have h_sum_v : (∑ i : Fin (n + 1), baryCoord n v i) = 1 :=
    cornerSimplex_baryCoord_sum_one hv_corner
  have h_sum_gv : (∑ i : Fin (n + 1), baryCoord n (g v) i) = 1 :=
    cornerSimplex_baryCoord_sum_one hgv_corner
  have h_exists : ∃ i, 0 < baryCoord n v i ∧ baryCoord n (g v) i ≤ baryCoord n v i :=
    label_pigeonhole (baryCoord n v) (baryCoord n (g v)) h_nonneg_v h_nonneg_gv h_sum_v h_sum_gv
  dsimp [inducedLabeling]
  simp [h_exists]
  rcases h_exists.choose_spec with ⟨hpos, _⟩
  dsimp [carrierSupp]
  simp [hpos]

/-- **Uniform coordinate modulus.** There is a modulus `ω` with `ω ε → 0` as
`ε → 0⁺` controlling the variation of all barycentric coordinates of `p` and of
`g p` over `S_n`. -/
theorem coordinate_modulus {n} (g : EuclSp n → EuclSp n)
    (hg : ContinuousOn g (cornerSimplex n)) :
    ∃ ω : ℝ → ℝ, Filter.Tendsto ω (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      (∀ ε, 0 < ε → 0 < ω ε) ∧
      ∀ ε, 0 < ε → ∀ p ∈ cornerSimplex n, ∀ q ∈ cornerSimplex n, ‖p - q‖ < ε →
        ∀ i, |baryCoord n p i - baryCoord n q i| ≤ ω ε ∧
             |baryCoord n (g p) i - baryCoord n (g q) i| ≤ ω ε := by
  sorry

/-- **Rainbow cell has a witness vertex per label.** For each label `i` a rainbow
cell `C` has a vertex `v_i` labeled `i`, satisfying `x_i(g v_i) ≤ x_i(v_i)`. -/
theorem rainbow_vertex_bound {n} (g : EuclSp n → EuclSp n) (T : Triangulation n)
    {C : Finset (EuclSp n)} (hC : IsRainbowCell T (inducedLabeling g) C) (i : Fin (n + 1)) :
    ∃ v ∈ C, inducedLabeling g v = i ∧ baryCoord n (g v) i ≤ baryCoord n v i := by
  sorry

/-- **One-sided coordinate bound on a rainbow cell.** If the mesh is `< ε` and
`C` is rainbow, every `x ∈ conv C` satisfies `x_i(g x) ≤ x_i(x) + ω ε`. -/
theorem rainbow_one_sided {n} (g : EuclSp n → EuclSp n) (T : Triangulation n)
    (ω : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) (hmesh : T.mesh < ε)
    (hω : ∀ ε, 0 < ε → ∀ p ∈ cornerSimplex n, ∀ q ∈ cornerSimplex n, ‖p - q‖ < ε →
        ∀ i, |baryCoord n p i - baryCoord n q i| ≤ ω ε ∧
             |baryCoord n (g p) i - baryCoord n (g q) i| ≤ ω ε)
    {C : Finset (EuclSp n)} (hC : IsRainbowCell T (inducedLabeling g) C)
    {x : EuclSp n} (hx : x ∈ convexHull ℝ (C : Set (EuclSp n))) (i : Fin (n + 1)) :
    baryCoord n (g x) i ≤ baryCoord n x i + ω ε := by
  sorry

/-- **A rainbow cell is approximately fixed.** Under the hypotheses of
`rainbow_one_sided`, every `x ∈ conv C` satisfies
`|x_i(g x) - x_i(x)| ≤ (n+1) · ω ε` for all `i`. -/
theorem rainbow_approx_fixed {n} (g : EuclSp n → EuclSp n) (T : Triangulation n)
    (ω : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) (hmesh : T.mesh < ε)
    (hω : ∀ ε, 0 < ε → ∀ p ∈ cornerSimplex n, ∀ q ∈ cornerSimplex n, ‖p - q‖ < ε →
        ∀ i, |baryCoord n p i - baryCoord n q i| ≤ ω ε ∧
             |baryCoord n (g p) i - baryCoord n (g q) i| ≤ ω ε)
    {C : Finset (EuclSp n)} (hC : IsRainbowCell T (inducedLabeling g) C)
    {x : EuclSp n} (hx : x ∈ convexHull ℝ (C : Set (EuclSp n))) (i : Fin (n + 1)) :
    |baryCoord n (g x) i - baryCoord n x i| ≤ (n + 1) * ω ε := by
  sorry

/-- **Vanishing displacement yields a fixed point.** If `K` is compact, `g`
continuous on `K` mapping `K` into `K`, and some sequence in `K` has displacement
`‖g x_k - x_k‖ → 0`, then `g` has a fixed point in `K`. -/
theorem approx_fixed_limit {d} {K : Set (EuclSp d)} (hK : IsCompact K)
    (g : EuclSp d → EuclSp d) (hg : ContinuousOn g K) (hmaps : Set.MapsTo g K K)
    (x : ℕ → EuclSp d) (hx : ∀ k, x k ∈ K)
    (hlim : Filter.Tendsto (fun k => ‖g (x k) - x k‖) Filter.atTop (nhds 0)) :
    ∃ z ∈ K, g z = z := by
  sorry

/-- **Brouwer for the standard simplex.** The corner simplex `S_n` has the
fixed-point property. -/
theorem simplex_brouwer {n} : HasFPP (cornerSimplex n) := by
  sorry

end Topology
end LeanEval
