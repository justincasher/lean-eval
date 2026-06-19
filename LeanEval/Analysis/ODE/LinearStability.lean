import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import EvalTools.Markers

namespace LeanEval
namespace Analysis
namespace ODE

/-!
Linear stability of `x' = A x` when every eigenvalue of `A` has negative real part.

For `A : Matrix (Fin n) (Fin n) ℝ` such that every (complex) eigenvalue `μ` of the
complexification of `A` satisfies `μ.re < 0`, every solution of `x' = A x` decays to
zero in norm: `‖x t‖ → 0` as `t → ∞`.

Throughout, matrices `Matrix (Fin n) (Fin n) 𝕜` carry the `ℓ^∞`-operator-norm
instances activated by `open scoped Matrix.Norms.Operator`, so that the
spectral-radius / Gelfand machinery, the matrix exponential's norm, and
`Matrix.linfty_opNorm_mulVec` (`‖M *ᵥ v‖ ≤ ‖M‖ * ‖v‖`) all refer to the same norm.
Vectors `Fin n → 𝕜` carry the supremum (`ℓ^∞`) norm.
-/

open scoped Matrix Matrix.Norms.Operator ENNReal NNReal

/-- **Complexification of a real matrix.** `complexification A` applies the inclusion
`ℝ ↪ ℂ` (the algebra map) to every entry of `A`. -/
noncomputable def complexification {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  A.map (algebraMap ℝ ℂ)

/-! ### Spectral radius of the matrix exponential -/

/-- **Spectrum of an upper-triangular matrix.** For `T` block triangular with respect to
the identity ordering, `μ ∈ σ(T)` iff `μ` is a diagonal entry. -/
lemma spectrum_upperTriangular {n : ℕ} {T : Matrix (Fin n) (Fin n) ℂ}
    (hT : T.BlockTriangular id) (μ : ℂ) :
    μ ∈ spectrum ℂ T ↔ ∃ i, μ = T i i := by
  sorry

/-- **The exponential of an upper-triangular matrix is upper triangular.** Moreover its
diagonal entries are the exponentials of the diagonal entries of `T`. -/
lemma exp_upperTriangular {n : ℕ} {T : Matrix (Fin n) (Fin n) ℂ}
    (hT : T.BlockTriangular id) :
    (NormedSpace.exp T).BlockTriangular id ∧
      ∀ i, (NormedSpace.exp T) i i = NormedSpace.exp (T i i) := by
  sorry

/-- **Spectrum of the exponential of an upper-triangular matrix.** Every `z ∈ σ(e^T)`
equals `e^{T i i}` for some index `i`, with `T i i ∈ σ(T)`. -/
lemma spectrum_exp_triangular {n : ℕ} {T : Matrix (Fin n) (Fin n) ℂ}
    (hT : T.BlockTriangular id) {z : ℂ} (hz : z ∈ spectrum ℂ (NormedSpace.exp T)) :
    ∃ i, z = NormedSpace.exp (T i i) ∧ T i i ∈ spectrum ℂ T := by
  sorry

/-- **Schur conjugation preserves the spectra of `B` and `e^{B}`.** Every complex matrix
`B` is unitarily similar to an upper-triangular matrix `T = U T (star U)`, and unitary
conjugation leaves both `σ(B)` and `σ(e^{B})` unchanged.

(The pinned Mathlib lacks `Matrix.schurTriangulation`; this is the faithful existential
form of the blueprint statement, which fixes `T` to the Schur form.) -/
lemma spectrum_exp_eq_schur {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) :
    ∃ (T : Matrix (Fin n) (Fin n) ℂ) (U : Matrix.unitaryGroup (Fin n) ℂ),
      T.BlockTriangular id ∧
      B = (U : Matrix (Fin n) (Fin n) ℂ) * T * star (U : Matrix (Fin n) (Fin n) ℂ) ∧
      spectrum ℂ (NormedSpace.exp B) = spectrum ℂ (NormedSpace.exp T) ∧
      spectrum ℂ B = spectrum ℂ T := by
  sorry

/-- **Reverse spectral mapping for the exponential.** Every `z ∈ σ(e^{B})` is `e^{μ}`
for some `μ ∈ σ(B)`. -/
lemma spectrum_exp_subset {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) {z : ℂ}
    (hz : z ∈ spectrum ℂ (NormedSpace.exp B)) :
    ∃ μ ∈ spectrum ℂ B, z = NormedSpace.exp μ := by
  sorry

/-- **Spectral radius of the exponential is less than one.** If every `μ ∈ σ(B)` has
`Re μ < 0`, then the spectral radius of `e^{B}` is `< 1`. -/
lemma spectralRadius_exp_lt_one {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (hB : ∀ μ ∈ spectrum ℂ B, μ.re < 0) :
    spectralRadius ℂ (NormedSpace.exp B) < 1 := by
  sorry

/-! ### Decay of operator powers -/

/-- **From the `1/m`-th root bound to the power bound.** In `[0, ∞]`, if
`‖a^m‖^{1/m} < ρ` (with `m ≥ 1`) then `‖a^m‖ < ρ^m`. -/
lemma enorm_pow_lt_of_root_lt {𝒜 : Type*} [NormedRing 𝒜] (a : 𝒜) {ρ : ℝ≥0∞}
    (hρ : 0 < ρ) {m : ℕ} (hm : 1 ≤ m)
    (h : (‖a ^ m‖₊ : ℝ≥0∞) ^ (1 / m : ℝ) < ρ) :
    (‖a ^ m‖₊ : ℝ≥0∞) < ρ ^ m := by
  sorry

/-- **Gelfand bound on powers.** In a complex Banach algebra, if `r(a) < ρ` with
`ρ > 0`, then `‖a^m‖ ≤ ρ^m` for all sufficiently large `m`. -/
lemma gelfand_eventually_le {𝒜 : Type*} [NormedRing 𝒜] [NormedAlgebra ℂ 𝒜]
    [CompleteSpace 𝒜] (a : 𝒜) {ρ : ℝ} (hρ : 0 < ρ)
    (h : spectralRadius ℂ a < ENNReal.ofReal ρ) :
    ∀ᶠ m : ℕ in Filter.atTop, ‖a ^ m‖ ≤ ρ ^ m := by
  sorry

/-- **Spectral radius below one forces power decay.** In a complex Banach algebra, if
`r(a) < 1` then `‖a^m‖ → 0`. -/
lemma tendsto_pow_norm_lt_one {𝒜 : Type*} [NormedRing 𝒜] [NormedAlgebra ℂ 𝒜]
    [CompleteSpace 𝒜] (a : 𝒜) (h : spectralRadius ℂ a < 1) :
    Filter.Tendsto (fun m : ℕ => ‖a ^ m‖) Filter.atTop (nhds 0) := by
  sorry

/-! ### Continuous-time decay of the matrix exponential -/

/-- **Exponential of an integer multiple.** `e^{(m : ℝ) • B} = (e^{B})^m`. -/
lemma exp_smul_nat {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) :
    NormedSpace.exp ((m : ℝ) • B) = (NormedSpace.exp B) ^ m := by
  sorry

/-- **Splitting the exponential at the integer part.** For `t ≥ 0` and `m = ⌊t⌋`,
`e^{t • B} = (e^{B})^m · e^{(t - m) • B}`. -/
lemma exp_smul_split {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) {t : ℝ} (ht : 0 ≤ t) :
    NormedSpace.exp (t • B)
      = (NormedSpace.exp B) ^ (⌊t⌋₊) * NormedSpace.exp ((t - (⌊t⌋₊ : ℝ)) • B) := by
  sorry

/-- **Uniform bound on the exponential over the unit interval.** There is `M ≥ 0` with
`‖e^{s • B}‖ ≤ M` for all `s ∈ [0,1]`. -/
lemma bddAbove_exp_smul_unit {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖NormedSpace.exp (s • B)‖ ≤ M := by
  sorry

/-- **Bound on the exponential by its integer-power part.** There is `M ≥ 0` such that for
every `t ≥ 0`, with `m = ⌊t⌋`, `‖e^{t • B}‖ ≤ ‖(e^{B})^m‖ · M`. -/
lemma norm_exp_smul_le {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, 0 ≤ t →
      ‖NormedSpace.exp (t • B)‖ ≤ ‖(NormedSpace.exp B) ^ (⌊t⌋₊)‖ * M := by
  sorry

/-- **Continuous-time decay of the exponential.** If `r(e^{B}) < 1` then
`‖e^{t • B}‖ → 0` as `t → ∞`. -/
lemma norm_exp_smul_tendsto_zero {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (hB : spectralRadius ℂ (NormedSpace.exp B) < 1) :
    Filter.Tendsto (fun t : ℝ => ‖NormedSpace.exp (t • B)‖) Filter.atTop (nhds 0) := by
  sorry

/-! ### Solution representation by the matrix exponential -/

/-- **Multiplying a matrix by a fixed vector is continuous linear.** For `v : Fin n → ℝ`
the map `M ↦ M *ᵥ v` is a continuous linear map. -/
lemma mulVec_right_clm {n : ℕ} (v : Fin n → ℝ) :
    ∃ L : Matrix (Fin n) (Fin n) ℝ →L[ℝ] (Fin n → ℝ), ⇑L = fun M => M.mulVec v := by
  sorry

/-- **Derivative of `τ ↦ e^{(τ - t₁) • A}`.** Its derivative at `t` is `A · e^{(t-t₁) • A}`. -/
lemma exp_smul_hasDerivAt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (t₁ t : ℝ) :
    HasDerivAt (fun τ : ℝ => NormedSpace.exp ((τ - t₁) • A))
      (A * NormedSpace.exp ((t - t₁) • A)) t := by
  sorry

/-- **Derivative of `τ ↦ e^{(τ - t₁) • A} v`.** Its derivative at `t` is
`A · (e^{(t-t₁) • A} v)`. -/
lemma exp_smul_mulVec_hasDerivAt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) (t₁ t : ℝ) :
    HasDerivAt (fun τ : ℝ => (NormedSpace.exp ((τ - t₁) • A)).mulVec v)
      (A.mulVec ((NormedSpace.exp ((t - t₁) • A)).mulVec v)) t := by
  sorry

/-- **The linear vector field is Lipschitz.** The map `z ↦ A *ᵥ z` is `K`-Lipschitz for
some constant `K`. -/
lemma vectorField_lipschitz {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ K : ℝ≥0, LipschitzWith K (fun z : Fin n → ℝ => A.mulVec z) := by
  sorry

/-- **The exponential propagator is a solution.** With `y τ = e^{(τ - t₁) • A} w`, for
every `τ` we have `HasDerivAt y (A · y τ) τ` and `y τ ∈ univ`, and `y t₁ = w`. -/
lemma exp_smul_isSolution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ)
    (t₁ : ℝ) :
    (∀ τ : ℝ,
        HasDerivAt (fun s : ℝ => (NormedSpace.exp ((s - t₁) • A)).mulVec w)
          (A.mulVec ((NormedSpace.exp ((τ - t₁) • A)).mulVec w)) τ ∧
        (NormedSpace.exp ((τ - t₁) • A)).mulVec w ∈ (Set.univ : Set (Fin n → ℝ))) ∧
      (NormedSpace.exp ((t₁ - t₁) • A)).mulVec w = w := by
  sorry

/-- **Uniqueness of linear ODE solutions on an open interval.** Two functions solving
`f' = A f` on `(a, b)` that agree at one interior point agree on `(a, b)`. -/
lemma ODE_solution_unique_univ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {a b : ℝ}
    {f g : ℝ → (Fin n → ℝ)} {t₀ : ℝ}
    (hf : ∀ τ ∈ Set.Ioo a b, HasDerivAt f (A.mulVec (f τ)) τ)
    (hg : ∀ τ ∈ Set.Ioo a b, HasDerivAt g (A.mulVec (g τ)) τ)
    (ht₀ : t₀ ∈ Set.Ioo a b) (heq : f t₀ = g t₀) :
    Set.EqOn f g (Set.Ioo a b) := by
  sorry

/-- **Agreement of a solution and the propagator on `(0, b)`.** A solution of `x' = A x`
on `(0, b)` agrees there with `τ ↦ e^{(τ - t₁) • A} x(t₁)` for any base point `t₁`. -/
lemma solution_eqOn_exp_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {b : ℝ}
    {x : ℝ → (Fin n → ℝ)}
    (hx : ∀ τ ∈ Set.Ioo (0 : ℝ) b, HasDerivAt x (A.mulVec (x τ)) τ)
    {t₁ : ℝ} (ht₁ : t₁ ∈ Set.Ioo (0 : ℝ) b) :
    Set.EqOn x (fun τ => (NormedSpace.exp ((τ - t₁) • A)).mulVec (x t₁))
      (Set.Ioo (0 : ℝ) b) := by
  sorry

/-- **Solutions are matrix exponentials of the initial value.** A solution of `x' = A x`
on `(0, ∞)` satisfies `x t = e^{(t - t₁) • A} x(t₁)` for all `t, t₁ > 0`. -/
lemma solution_eq_exp_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {x : ℝ → (Fin n → ℝ)}
    (hx : ∀ t : ℝ, 0 < t → HasDerivAt x (A.mulVec (x t)) t)
    {t₁ : ℝ} (ht₁ : 0 < t₁) {t : ℝ} (ht : 0 < t) :
    x t = (NormedSpace.exp ((t - t₁) • A)).mulVec (x t₁) := by
  sorry

/-! ### Complexification and the main theorem -/

/-- **Eigenvalue hypothesis as a spectral condition.** If every eigenvalue of `toLin' B`
has negative real part, then every `μ ∈ σ(B)` has negative real part, where
`B = A.map (algebraMap ℝ ℂ)`. -/
lemma eigenvalue_re_neg_spectrum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ μ : ℂ,
        Module.End.HasEigenvalue (Matrix.toLin' (A.map (algebraMap ℝ ℂ))) μ → μ.re < 0)
    {μ : ℂ} (hμ : μ ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ))) :
    μ.re < 0 := by
  sorry

/-- **Complexification is norm-preserving on vectors.** `‖(i ↦ (w i : ℂ))‖ = ‖w‖`. -/
lemma norm_complexify_vec {n : ℕ} (w : Fin n → ℝ) :
    ‖fun i => (w i : ℂ)‖ = ‖w‖ := by
  sorry

/-- **Matrix exponential commutes with entrywise complexification.**
`(e^{M}).map (algebraMap ℝ ℂ) = e^{M.map (algebraMap ℝ ℂ)}`. -/
lemma exp_map_complexify {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    (NormedSpace.exp M).map (algebraMap ℝ ℂ)
      = NormedSpace.exp (M.map (algebraMap ℝ ℂ)) := by
  sorry

/-- **Complexification commutes with `e^{sA} w`.** With `B = A.map (algebraMap ℝ ℂ)`,
`(e^{s • A} w)_ℂ = e^{s • B} w_ℂ`. -/
lemma complexify_exp_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ)
    (s : ℝ) :
    (fun i => (((NormedSpace.exp (s • A)).mulVec w) i : ℂ))
      = (NormedSpace.exp (s • A.map (algebraMap ℝ ℂ))).mulVec (fun i => (w i : ℂ)) := by
  sorry

/-- **Pointwise bound on the solution.** With `B = A.map (algebraMap ℝ ℂ)`, a solution of
`x' = A x` on `(0, ∞)` satisfies `‖x t‖ ≤ ‖e^{(t-1) • B}‖ · ‖x 1‖` for all `t > 0`. -/
lemma norm_solution_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {x : ℝ → (Fin n → ℝ)}
    (hx : ∀ t : ℝ, 0 < t → HasDerivAt x (A.mulVec (x t)) t)
    {t : ℝ} (ht : 0 < t) :
    ‖x t‖ ≤ ‖NormedSpace.exp ((t - 1) • A.map (algebraMap ℝ ℂ))‖ * ‖x 1‖ := by
  sorry

/-- **Asymptotic stability of a linear ODE with eigenvalues in the open left half-plane.**

Let `A : Matrix (Fin n) (Fin n) ℝ`. Suppose every (complex) eigenvalue of the
complexification of `A` has strictly negative real part. Then every solution of the
linear ODE `x'(t) = A · x(t)` tends to `0` in norm as `t → ∞`. -/
@[eval_problem]
theorem linear_ode_asymptotic_stability
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ μ : ℂ,
        Module.End.HasEigenvalue
          (Matrix.toLin' (A.map (algebraMap ℝ ℂ))) μ → μ.re < 0)
    (x : ℝ → (Fin n → ℝ))
    (hx : ∀ t : ℝ, 0 < t → HasDerivAt x (A.mulVec (x t)) t) :
    Filter.Tendsto (fun t : ℝ => ‖x t‖) Filter.atTop (nhds 0) := by
  sorry

end ODE
end Analysis
end LeanEval
