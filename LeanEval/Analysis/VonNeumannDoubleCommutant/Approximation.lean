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
  sorry

/-- `lem:double-commutant-approx`: for `T ∈ S''`, a finite family `x : Fin n → H`
and `ε > 0`, there exists `A ∈ S` with `‖T x_i - A x_i‖ < ε` for all `i`. This is
the key bridge from the single-vector approximation to finitely many vectors,
obtained by amplification. -/
theorem double_commutant_approx (S : StarSubalgebra ℂ (H →L[ℂ] H))
    {T : H →L[ℂ] H}
    (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (x : Fin n → H) {ε : ℝ} (hε : 0 < ε) :
    ∃ A ∈ S, ∀ i : Fin n, ‖T (x i) - A (x i)‖ < ε := by
  sorry

/-- `lem:sot-nhds-zero-basis`: in the SOT type copy `PointwiseConvergenceCLM`, the
neighbourhood filter of `0` has a basis given by the sets
`W_{x, ε} = {U | ∀ i, ‖U (x i)‖ < ε}`, indexed by finite families
`x : Fin n → H` and reals `ε > 0`. -/
theorem sot_hasBasis_nhds_zero :
    (nhds (0 : PointwiseConvergenceCLM (RingHom.id ℂ) H H)).HasBasis
      (fun p : Σ n : ℕ, (Fin n → H) × ℝ => 0 < p.2.2)
      (fun p : Σ n : ℕ, (Fin n → H) × ℝ =>
        {U : PointwiseConvergenceCLM (RingHom.id ℂ) H H | ∀ i, ‖U (p.2.1 i)‖ < p.2.2}) := by
  sorry

/-- `lem:sot-nhds-basis`: for `T₀` in the SOT type copy, the neighbourhood filter of
`T₀` has a basis given by the sets `V_{x, ε} = {U | ∀ i, ‖U (x i) - T₀ (x i)‖ < ε}`,
indexed by finite families `x : Fin n → H` and reals `ε > 0`. -/
theorem sot_hasBasis_nhds (T₀ : PointwiseConvergenceCLM (RingHom.id ℂ) H H) :
    (nhds T₀).HasBasis
      (fun p : Σ n : ℕ, (Fin n → H) × ℝ => 0 < p.2.2)
      (fun p : Σ n : ℕ, (Fin n → H) × ℝ =>
        {U : PointwiseConvergenceCLM (RingHom.id ℂ) H H |
          ∀ i, ‖U (p.2.1 i) - T₀ (p.2.1 i)‖ < p.2.2}) := by
  sorry

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
  sorry

/-- `lem:sot-closed-mem`: if the SOT image `ι_S '' S` is closed and `T` satisfies the
finite-family approximation property, then `T ∈ S`. -/
theorem sot_closed_mem (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (hclosed : IsClosed (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
      (S : Set (H →L[ℂ] H))))
    (T : H →L[ℂ] H)
    (happrox : ∀ (n : ℕ) (x : Fin n → H) {ε : ℝ}, 0 < ε →
      ∃ A ∈ S, ∀ i : Fin n, ‖T (x i) - A (x i)‖ < ε) :
    T ∈ S := by
  sorry

end Analysis
end LeanEval
