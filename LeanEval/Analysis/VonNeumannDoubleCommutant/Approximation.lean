import Mathlib
import EvalTools.Markers
import LeanEval.Analysis.VonNeumannDoubleCommutant.Orbit
import LeanEval.Analysis.VonNeumannDoubleCommutant.Amplification
import LeanEval.Analysis.VonNeumannDoubleCommutant.Blocks

/-!
# Finite-family approximation and the SOT closure

This file completes the hard implication of von Neumann's double commutant
theorem. It bridges the single-vector approximation (`single_vector_approx` in
`Orbit.lean`) to a finite-family statement via the diagonal amplification
(`Amplification.lean`, `Blocks.lean`), and then translates the approximation
property into membership in the strong operator topology (SOT) closure.

Blueprint labels: `lem:coord-norm-le` through `lem:sot-closed-mem`.
-/

namespace LeanEval
namespace Analysis

open scoped ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {n : ℕ}

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
/-- `lem:coord-norm-le`: for `v ∈ H^n = PiLp 2 (fun _ : Fin n => H)` and any index
`i`, the coordinate norm is bounded by the `ℓ²` norm, `‖v_i‖ ≤ ‖v‖`. -/
theorem coord_norm_le (v : PiLp 2 (fun _ : Fin n => H)) (i : Fin n) :
    ‖v.ofLp i‖ ≤ ‖v‖ :=
  PiLp.norm_apply_le v i

/-- `lem:closure-coord-approx`: if the vector `(T x_i)_i ∈ H^n` lies in the closure
of `{(A x_i)_i : A ∈ S}`, then for every `ε > 0` there is `A ∈ S` with
`‖T x_i - A x_i‖ < ε` for all `i`. -/
theorem closure_coord_approx (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (T : H →L[ℂ] H) (x : Fin n → H)
    (hmem : (WithLp.toLp 2 (fun i => T (x i)) : PiLp 2 (fun _ : Fin n => H)) ∈
      closure {y : PiLp 2 (fun _ : Fin n => H) |
        ∃ A ∈ S, (WithLp.toLp 2 (fun i => A (x i))) = y})
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A ∈ S, ∀ i : Fin n, ‖T (x i) - A (x i)‖ < ε := by
  have hm_iff := (Metric.mem_closure_iff).mp hmem
  have h_ex := hm_iff ε hε
  rcases h_ex with ⟨y, hy, hdist⟩
  rcases hy with ⟨A, hA, hy_eq⟩
  refine ⟨A, hA, λ i => ?_⟩
  have h_norm : ‖(WithLp.toLp 2 (fun i => T (x i)) - WithLp.toLp 2 (fun i => A (x i)))‖ < ε := by
    simpa [hy_eq, dist_eq_norm] using hdist
  have h_coord : ‖((WithLp.toLp 2 (fun i => T (x i)) - WithLp.toLp 2 (fun i => A (x i))).ofLp i)‖ < ε :=
    lt_of_le_of_lt (coord_norm_le _ i) h_norm
  simpa using h_coord

/-- `lem:double-commutant-approx`: for `T ∈ S''`, a finite family `x : Fin n → H`
and `ε > 0`, there exists `A ∈ S` with `‖T x_i - A x_i‖ < ε` for all `i`. This is
the key bridge from the single-vector approximation to finitely many vectors,
obtained by amplification. -/
theorem double_commutant_approx (S : StarSubalgebra ℂ (H →L[ℂ] H))
    {T : H →L[ℂ] H}
    (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (x : Fin n → H) {ε : ℝ} (hε : 0 < ε) :
    ∃ A ∈ S, ∀ i : Fin n, ‖T (x i) - A (x i)‖ < ε := by
  -- ξ = (x_i)_i in H^n
  set ξ : PiLp 2 (fun _ : Fin n => H) := WithLp.toLp 2 (fun i : Fin n => x i) with hξ
  -- R := Δ(S)
  set R := amplificationSubalgebra (n := n) S with hR
  -- Show Δ(T) ∈ R''
  have hT_amp : amplificationMap (n := n) T ∈ Set.centralizer (Set.centralizer (R : Set _)) := by
    exact amplification_double_commutant (n := n) S T hT
  -- Apply single_vector_approx: Δ(T) ξ ∈ closure {A ξ | A ∈ R}
  have h_sva : amplificationMap (n := n) T ξ ∈
      closure {y : PiLp 2 (fun _ : Fin n => H) | ∃ A ∈ R, A ξ = y} :=
    single_vector_approx R hT_amp ξ
  -- Lemma: amplificationMap A ξ = WithLp.toLp (A (x i))_i
  have h_amp_eq (A : H →L[ℂ] H) : amplificationMap A ξ = (WithLp.toLp 2 (fun i : Fin n => A (x i)) : PiLp 2 (fun _ : Fin n => H)) := by
    apply (PiLp.ext_iff (p := 2) (ι := Fin n) (α := fun _ : Fin n => H)).mpr
    intro i
    simp [amplificationMap_apply, ξ, hξ]
  -- The closure set in h_sva equals the closure set needed for closure_coord_approx
  have h_set_eq : {y : PiLp 2 (fun _ : Fin n => H) | ∃ A ∈ R, A ξ = y} =
      {y : PiLp 2 (fun _ : Fin n => H) | ∃ A₀ ∈ S, (WithLp.toLp 2 (fun i : Fin n => A₀ (x i))) = y} := by
    ext y
    constructor
    · intro ⟨A, hA, hAy⟩
      rw [hR, amplificationSubalgebra, StarSubalgebra.mem_map] at hA
      rcases hA with ⟨A₀, hA₀S, hA_eq⟩
      have hA_eq' : amplificationMap A₀ = A := by
        change amplificationMap A₀ = A at hA_eq
        exact hA_eq
      refine ⟨A₀, hA₀S, ?_⟩
      rw [← hA_eq'] at hAy
      rw [h_amp_eq A₀] at hAy
      exact hAy
    · intro ⟨A₀, hA₀S, hy⟩
      have hA₀R : amplificationMap A₀ ∈ R := by
        rw [hR, amplificationSubalgebra]
        apply StarSubalgebra.mem_map.mpr
        exact ⟨A₀, hA₀S, rfl⟩
      refine ⟨amplificationMap A₀, hA₀R, ?_⟩
      calc
        amplificationMap A₀ ξ = (WithLp.toLp 2 (fun i : Fin n => A₀ (x i)) : PiLp 2 (fun _ : Fin n => H)) := h_amp_eq A₀
        _ = y := hy
  -- Combine to get the membership needed by closure_coord_approx
  rw [h_set_eq] at h_sva
  have h_mem : (WithLp.toLp 2 (fun i => T (x i)) : PiLp 2 (fun _ : Fin n => H)) ∈
      closure {y : PiLp 2 (fun _ : Fin n => H) | ∃ A ∈ S, (WithLp.toLp 2 (fun i => A (x i))) = y} := by
    rw [← h_amp_eq T]
    exact h_sva
  -- Apply the coordinate-wise approximation lemma
  exact closure_coord_approx S T x h_mem hε

omit [CompleteSpace H] in
/-- `lem:sot-nhds-zero-basis`: in the SOT type copy `PointwiseConvergenceCLM`, the
neighbourhood filter of `0` has a basis given by the sets
`W_{x, ε} = {U | ∀ i, ‖U (x i)‖ < ε}`, indexed by finite families
`x : Fin n → H` and reals `ε > 0`. -/
theorem sot_hasBasis_nhds_zero :
    (nhds (0 : PointwiseConvergenceCLM (RingHom.id ℂ) H H)).HasBasis
      (fun p : Σ n : ℕ, (Fin n → H) × ℝ => 0 < p.2.2)
      (fun p : Σ n : ℕ, (Fin n → H) × ℝ =>
        {U : PointwiseConvergenceCLM (RingHom.id ℂ) H H | ∀ i, ‖U (p.2.1 i)‖ < p.2.2}) := by
  have hbasis := PointwiseConvergenceCLM.hasBasis_nhds_zero (E := H) (F := H) (σ := RingHom.id ℂ)
  apply Filter.HasBasis.mk
  intro t
  constructor
  · intro ht
    rcases hbasis.mem_iff.mp ht with ⟨⟨F, V⟩, ⟨hFfin, hV0⟩, hsub⟩
    rcases Metric.mem_nhds_iff.mp hV0 with ⟨ε, hε, hball⟩
    haveI : Fintype (F : Set H) := Set.Finite.fintype hFfin
    let n := Fintype.card (F : Set H)
    let e : (F : Set H) ≃ Fin n := Fintype.equivFin (F : Set H)
    let x : Fin n → H := λ i => ((e.symm i : (F : Set H)).val : H)
    refine ⟨⟨n, (x, ε)⟩, hε, ?_⟩
    intro U hU
    apply hsub
    intro y hy
    have hy' : U y ∈ Metric.ball (0 : H) ε := by
      have hy_range : y ∈ Set.range x := by
        let y' : (F : Set H) := ⟨y, hy⟩
        let i : Fin n := e y'
        refine ⟨i, ?_⟩
        dsimp [x, i, y']
        have : e.symm (e ⟨y, hy⟩) = ⟨y, hy⟩ := Equiv.symm_apply_apply e ⟨y, hy⟩
        simp
      rcases hy_range with ⟨i, hi⟩
      have hUi : ‖U (x i)‖ < ε := hU i
      have hUy : U y = U (x i) := by rw [hi]
      rw [hUy]
      apply Metric.mem_ball.mpr
      simpa [dist_eq_norm] using hUi
    exact hball hy'
  · intro h
    rcases h with ⟨p, hp, hsub⟩
    rcases p with ⟨n, xε⟩
    rcases xε with ⟨x, ε⟩
    have hε : 0 < ε := hp
    have hfin : Finite (Set.range x) := Set.finite_range x
    have hball_mem : Metric.ball (0 : H) ε ∈ nhds (0 : H) := Metric.ball_mem_nhds (0 : H) hε
    have hmem : {U : PointwiseConvergenceCLM (RingHom.id ℂ) H H |
      ∀ y ∈ Set.range x, U y ∈ Metric.ball (0 : H) ε} ∈ nhds (0 : _) :=
      hbasis.mem_iff.mpr ⟨(Set.range x, Metric.ball 0 ε), ⟨hfin, hball_mem⟩, Set.Subset.refl _⟩
    have h_eq : {U : PointwiseConvergenceCLM (RingHom.id ℂ) H H |
      ∀ y ∈ Set.range x, U y ∈ Metric.ball (0 : H) ε} =
      {U : PointwiseConvergenceCLM (RingHom.id ℂ) H H | ∀ i, ‖U (x i)‖ < ε} := by
      ext U
      constructor
      · intro hU i
        have hball : U (x i) ∈ Metric.ball (0 : H) ε := hU (x i) ⟨i, rfl⟩
        simpa [dist_eq_norm] using Metric.mem_ball.mp hball
      · intro hU y hy
        rcases hy with ⟨i, rfl⟩
        simpa [dist_eq_norm] using hU i
    rw [h_eq] at hmem
    exact Filter.mem_of_superset hmem hsub

omit [CompleteSpace H] in
/-- `lem:sot-nhds-basis`: for `T₀` in the SOT type copy, the neighbourhood filter of
`T₀` has a basis given by the sets `V_{x, ε} = {U | ∀ i, ‖U (x i) - T₀ (x i)‖ < ε}`,
indexed by finite families `x : Fin n → H` and reals `ε > 0`. -/
theorem sot_hasBasis_nhds (T₀ : PointwiseConvergenceCLM (RingHom.id ℂ) H H) :
    (nhds T₀).HasBasis
      (fun p : Σ n : ℕ, (Fin n → H) × ℝ => 0 < p.2.2)
      (fun p : Σ n : ℕ, (Fin n → H) × ℝ =>
        {U : PointwiseConvergenceCLM (RingHom.id ℂ) H H |
          ∀ i, ‖U (p.2.1 i) - T₀ (p.2.1 i)‖ < p.2.2}) := by
  have hzero : (nhds (0 : PointwiseConvergenceCLM (RingHom.id ℂ) H H)).HasBasis
    (fun p : Σ n : ℕ, (Fin n → H) × ℝ => 0 < p.2.2)
    (fun p : Σ n : ℕ, (Fin n → H) × ℝ =>
      {U : PointwiseConvergenceCLM (RingHom.id ℂ) H H | ∀ i, ‖U (p.2.1 i)‖ < p.2.2}) :=
    sot_hasBasis_nhds_zero
  have h_trans : Filter.map (T₀ + ·) (nhds (0 : PointwiseConvergenceCLM (RingHom.id ℂ) H H)) = nhds T₀ := by
    calc
      Filter.map (T₀ + ·) (nhds (0 : PointwiseConvergenceCLM (RingHom.id ℂ) H H)) = nhds ((T₀ + ·) (0 : _)) :=
        (Homeomorph.addLeft T₀).map_nhds_eq 0
      _ = nhds T₀ := by simp
  have hbasis' : (nhds T₀).HasBasis
    (fun p : Σ n : ℕ, (Fin n → H) × ℝ => 0 < p.2.2)
    (fun p => (T₀ + ·) '' {U : PointwiseConvergenceCLM (RingHom.id ℂ) H H |
      ∀ i, ‖U (p.2.1 i)‖ < p.2.2}) := by
    simpa [h_trans] using hzero.map (T₀ + ·)
  have hs_eq : ∀ p, (fun p' : Σ n : ℕ, (Fin n → H) × ℝ => 0 < p'.2.2) p →
    ((T₀ + ·) '' {U : PointwiseConvergenceCLM (RingHom.id ℂ) H H | ∀ i, ‖U (p.2.1 i)‖ < p.2.2}) =
    {U : PointwiseConvergenceCLM (RingHom.id ℂ) H H | ∀ i, ‖U (p.2.1 i) - T₀ (p.2.1 i)‖ < p.2.2} := by
    intro p hp
    ext V
    constructor
    · rintro ⟨U, hU, rfl⟩
      intro i
      have hUi := hU i
      simpa [sub_self, add_sub_cancel_right] using hUi
    · intro hV
      refine ⟨V - T₀, ?_, ?_⟩
      · intro i
        simpa [sub_eq_add_neg] using hV i
      · simp
  exact hbasis'.congr (fun i => Iff.rfl) hs_eq

/-- `lem:sot-closure-membership`: an operator `T` satisfies
`ι_S T ∈ closure (ι_S '' S)` in the SOT type copy iff for every finite family
`x : Fin n → H` and every `ε > 0` there is `A ∈ S` with `‖T x_i - A x_i‖ < ε` for
all `i`. Here `ι_S = ContinuousLinearMap.toPointwiseConvergenceCLM`. -/
theorem sot_closure_membership (S : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H) :
    ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H T ∈
        closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
          (S : Set (H →L[ℂ] H))) ↔
      ∀ (n : ℕ) (x : Fin n → H) {ε : ℝ}, 0 < ε →
        ∃ A ∈ S, ∀ i : Fin n, ‖T (x i) - A (x i)‖ < ε := by
  let ι := ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
  have hι_apply (f : H →L[ℂ] H) (v : H) : (ι f) v = f v :=
    congrArg (· v) (ContinuousLinearMap.toPointwiseConvergenceCLM_apply ℂ (RingHom.id ℂ) H H f)
  have hbasis : (nhds (ι T)).HasBasis (fun p : Σ n : ℕ, (Fin n → H) × ℝ => 0 < p.2.2)
      (fun p : Σ n : ℕ, (Fin n → H) × ℝ => {U | ∀ i, ‖U (p.2.1 i) - (ι T) (p.2.1 i)‖ < p.2.2}) :=
    sot_hasBasis_nhds (ι T)
  rw [mem_closure_iff_nhds_basis' hbasis]
  constructor
  · intro h n x ε hε
    have h_nonempty : ({U | ∀ i, ‖U (x i) - (ι T) (x i)‖ < ε} ∩ (ι '' (S : Set (H →L[ℂ] H)))).Nonempty :=
      h ⟨n, (x, ε)⟩ hε
    rcases h_nonempty with ⟨U, hUmn⟩
    have hUV : U ∈ {U | ∀ i, ‖U (x i) - (ι T) (x i)‖ < ε} := hUmn.1
    have hUimg : U ∈ ι '' (S : Set (H →L[ℂ] H)) := hUmn.2
    rcases hUimg with ⟨A, hA, hA_eq⟩
    refine ⟨A, hA, λ i => ?_⟩
    have hU_V_i : ‖U (x i) - (ι T) (x i)‖ < ε := hUV i
    have h_inner : ‖A (x i) - T (x i)‖ = ‖(ι A) (x i) - (ι T) (x i)‖ := by
      simp [hι_apply]
    have h_eq : ‖T (x i) - A (x i)‖ = ‖U (x i) - (ι T) (x i)‖ := by
      rw [norm_sub_rev, h_inner, hA_eq]
    rw [h_eq]
    exact hU_V_i
  · intro h p hp
    rcases p with ⟨n, xε⟩
    rcases xε with ⟨x, ε⟩
    have hε_pos : 0 < ε := hp
    have h_ex : ∃ A ∈ S, ∀ i : Fin n, ‖T (x i) - A (x i)‖ < ε := h n x (ε := ε) hε_pos
    rcases h_ex with ⟨A, hA, h_approx⟩
    refine ⟨ι A, λ i => ?_, ⟨A, hA, rfl⟩⟩
    have h_eq : ‖(ι A) (x i) - (ι T) (x i)‖ = ‖T (x i) - A (x i)‖ := by
      simp [hι_apply, norm_sub_rev]
    rw [h_eq]
    exact h_approx i

/-- `lem:sot-closed-mem`: if the SOT image `ι_S '' S` is closed and `T` satisfies the
finite-family approximation property, then `T ∈ S`. -/
theorem sot_closed_mem (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (hclosed : IsClosed (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
      (S : Set (H →L[ℂ] H))))
    (T : H →L[ℂ] H)
    (happrox : ∀ (n : ℕ) (x : Fin n → H) {ε : ℝ}, 0 < ε →
      ∃ A ∈ S, ∀ i : Fin n, ‖T (x i) - A (x i)‖ < ε) :
    T ∈ S := by
  let f := ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
  have hmemsot : f T ∈ closure (f '' (S : Set (H →L[ℂ] H))) :=
    ((sot_closure_membership S T).mpr happrox)
  have hsubset : closure (f '' (S : Set (H →L[ℂ] H))) ⊆ f '' (S : Set (H →L[ℂ] H)) :=
    IsClosed.closure_subset hclosed
  rcases hsubset hmemsot with ⟨A, hA, h_eq⟩
  have h_inj : Function.Injective (f : (H →L[ℂ] H) → PointwiseConvergenceCLM (RingHom.id ℂ) H H) := by
    intro x y h
    apply (ContinuousLinearMap.toUniformConvergenceCLM (RingHom.id ℂ) H
      {s : Set H | Finite s}).injective
    exact h
  have hTA : T = A := h_inj h_eq.symm
  rw [hTA]
  exact hA

end Analysis
end LeanEval
