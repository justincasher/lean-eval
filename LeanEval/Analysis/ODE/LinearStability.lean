import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
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
import LeanEval.Analysis.ODE.LinearStability.SchurTriangulation
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
  have hcharpoly : T.charpoly = ∏ i : Fin n, (Polynomial.X - Polynomial.C (T i i)) :=
    Matrix.charpoly_of_upperTriangular T hT
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, hcharpoly, Polynomial.IsRoot, Polynomial.eval_prod]
  simp [Finset.prod_eq_zero_iff, sub_eq_zero]

/-- **The exponential of an upper-triangular matrix is upper triangular.** Moreover its
diagonal entries are the exponentials of the diagonal entries of `T`. -/
lemma exp_upperTriangular {n : ℕ} {T : Matrix (Fin n) (Fin n) ℂ}
    (hT : T.BlockTriangular id) :
    (NormedSpace.exp T).BlockTriangular id ∧
      ∀ i, (NormedSpace.exp T) i i = NormedSpace.exp (T i i) := by
  -- Powers of a triangular matrix are triangular.
  have hBT_pow : ∀ k : ℕ, (T ^ k).BlockTriangular id := by
    intro k
    induction k with
    | zero => rw [pow_zero]; exact Matrix.blockTriangular_one
    | succ k ih => rw [pow_succ]; exact Matrix.BlockTriangular.mul ih hT
  -- The exponential series for `T`.
  have hsumT : HasSum (fun k : ℕ => ((k.factorial : ℂ)⁻¹) • T ^ k) (NormedSpace.exp T) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) T
  -- Evaluation at any fixed entry `(p, q)` is a continuous linear map; push it through the series.
  have eval : ∀ p q : Fin n,
      HasSum (fun k : ℕ => ((k.factorial : ℂ)⁻¹) • (T ^ k) p q) ((NormedSpace.exp T) p q) := by
    intro p q
    let φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ :=
      { toFun := fun M => M p q
        map_add' := fun M N => rfl
        map_smul' := fun c M => rfl }
    have hcont : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ => M p q) :=
      φ.continuous_of_finiteDimensional
    let φL : Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ := ⟨φ, hcont⟩
    have hmap := hsumT.mapL φL
    have hfun : (fun k : ℕ => φL ((( k.factorial : ℂ)⁻¹) • T ^ k))
        = (fun k : ℕ => ((k.factorial : ℂ)⁻¹) • (T ^ k) p q) := by
      funext k
      show (((k.factorial : ℂ)⁻¹) • T ^ k) p q = ((k.factorial : ℂ)⁻¹) • (T ^ k) p q
      rw [Matrix.smul_apply]
    rw [hfun] at hmap
    exact hmap
  refine ⟨?_, ?_⟩
  · -- `exp T` is triangular: each strictly-lower entry is a sum of zeros.
    intro i j hij
    have e := eval i j
    have hz : (fun k : ℕ => ((k.factorial : ℂ)⁻¹) • (T ^ k) i j) = (fun _ : ℕ => (0 : ℂ)) := by
      funext k
      rw [(hBT_pow k) hij, smul_zero]
    rw [hz] at e
    exact e.unique hasSum_zero
  · -- The diagonal entries: `(exp T) i i = exp (T i i)`.
    intro i
    have hpow : ∀ k : ℕ, (T ^ k) i i = (T i i) ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          rw [pow_succ, pow_succ, Matrix.mul_apply, Finset.sum_eq_single i]
          · rw [ih]
          · intro j _ hji
            rcases lt_or_gt_of_ne hji with h | h
            · rw [(hBT_pow k) h, zero_mul]
            · rw [hT h, mul_zero]
          · intro hi
            exact absurd (Finset.mem_univ i) hi
    have e := eval i i
    have hfun2 : (fun k : ℕ => ((k.factorial : ℂ)⁻¹) • (T ^ k) i i)
        = (fun k : ℕ => ((k.factorial : ℂ)⁻¹) • (T i i) ^ k) := by
      funext k; rw [hpow k]
    rw [hfun2] at e
    exact e.unique (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (T i i))

/-- **Spectrum of the exponential of an upper-triangular matrix.** Every `z ∈ σ(e^T)`
equals `e^{T i i}` for some index `i`, with `T i i ∈ σ(T)`. -/
lemma spectrum_exp_triangular {n : ℕ} {T : Matrix (Fin n) (Fin n) ℂ}
    (hT : T.BlockTriangular id) {z : ℂ} (hz : z ∈ spectrum ℂ (NormedSpace.exp T)) :
    ∃ i, z = NormedSpace.exp (T i i) ∧ T i i ∈ spectrum ℂ T := by
  rcases exp_upperTriangular hT with ⟨hT_exp, h_diag⟩
  rcases (spectrum_upperTriangular hT_exp z).mp hz with ⟨i, hi⟩
  refine ⟨i, ?_, ?_⟩
  · rw [hi, h_diag i]
  · exact (spectrum_upperTriangular hT (T i i)).mpr ⟨i, rfl⟩

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
  set U := Matrix.schurTriangulationUnitary B with hUdef
  set T : Matrix (Fin n) (Fin n) ℂ := (Matrix.schurTriangulation B).val with hTdef
  have hB : B = (U : Matrix (Fin n) (Fin n) ℂ) * T * star (U : Matrix (Fin n) (Fin n) ℂ) :=
    Matrix.schur_triangulation B
  -- Conjugation by the unitary `U` commutes with the matrix exponential.
  have hconj : ∀ X : Matrix (Fin n) (Fin n) ℂ,
      NormedSpace.exp ((U : Matrix (Fin n) (Fin n) ℂ) * X * star (U : Matrix (Fin n) (Fin n) ℂ))
        = (U : Matrix (Fin n) (Fin n) ℂ) * NormedSpace.exp X
            * star (U : Matrix (Fin n) (Fin n) ℂ) := by
    intro X
    have h := Matrix.exp_units_conj (Unitary.toUnits U) X
    simpa using h
  refine ⟨T, U, (Matrix.schurTriangulation B).property, hB, ?_, ?_⟩
  · -- `σ(exp B) = σ(exp T)`
    have hexp : NormedSpace.exp B
        = (U : Matrix (Fin n) (Fin n) ℂ) * NormedSpace.exp T
            * star (U : Matrix (Fin n) (Fin n) ℂ) := by
      rw [hB, hconj]
    rw [hexp]
    exact Unitary.spectrum_star_right_conjugate
  · -- `σ(B) = σ(T)`
    rw [hB]
    exact Unitary.spectrum_star_right_conjugate

/-- **Reverse spectral mapping for the exponential.** Every `z ∈ σ(e^{B})` is `e^{μ}`
for some `μ ∈ σ(B)`. -/
lemma spectrum_exp_subset {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) {z : ℂ}
    (hz : z ∈ spectrum ℂ (NormedSpace.exp B)) :
    ∃ μ ∈ spectrum ℂ B, z = NormedSpace.exp μ := by
  obtain ⟨T, U, hT, hB, hspec_exp, hspec_B⟩ := spectrum_exp_eq_schur B
  have hzT : z ∈ spectrum ℂ (NormedSpace.exp T) := by
    rw [hspec_exp] at hz
    exact hz
  obtain ⟨i, hz_eq, hi_mem_T⟩ := spectrum_exp_triangular hT hzT
  refine ⟨T i i, ?_, hz_eq⟩
  rw [hspec_B]
  exact hi_mem_T

/-- **Spectral radius of the exponential is less than one.** If every `μ ∈ σ(B)` has
`Re μ < 0`, then the spectral radius of `e^{B}` is `< 1`. -/
lemma spectralRadius_exp_lt_one {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (hB : ∀ μ ∈ spectrum ℂ B, μ.re < 0) :
    spectralRadius ℂ (NormedSpace.exp B) < 1 := by
  by_cases hn : n = 0
  · subst hn
    haveI : Subsingleton (Matrix (Fin 0) (Fin 0) ℂ) := by infer_instance
    simp
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn
    subst hk
    haveI : Nonempty (Fin (k + 1)) := inferInstance
    haveI : Nontrivial (Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) := Matrix.nonempty
    apply spectrum.spectralRadius_lt_of_forall_lt (NormedSpace.exp B) (r := (1 : ℝ≥0))
    intro z hz
    rcases spectrum_exp_subset B hz with ⟨μ, hμ, hz_eq⟩
    subst hz_eq
    have hnorm : ‖NormedSpace.exp μ‖ = Real.exp μ.re := by
      simpa [Complex.exp_eq_exp_ℂ] using Complex.norm_exp μ
    have hre : μ.re < 0 := hB μ hμ
    have hexp_lt_one : Real.exp μ.re < 1 := by
      rwa [Real.exp_lt_one_iff]
    have h' : (‖NormedSpace.exp μ‖₊ : ℝ) < (1 : ℝ) := by
      simpa [hnorm] using hexp_lt_one
    exact_mod_cast h'

/-! ### Decay of operator powers -/

/-- **From the `1/m`-th root bound to the power bound.** In `[0, ∞]`, if
`‖a^m‖^{1/m} < ρ` (with `m ≥ 1`) then `‖a^m‖ < ρ^m`. -/
lemma enorm_pow_lt_of_root_lt {𝒜 : Type*} [NormedRing 𝒜] (a : 𝒜) {ρ : ℝ≥0∞}
    (_hρ : 0 < ρ) {m : ℕ} (hm : 1 ≤ m)
    (h : (‖a ^ m‖₊ : ℝ≥0∞) ^ (1 / m : ℝ) < ρ) :
    (‖a ^ m‖₊ : ℝ≥0∞) < ρ ^ m := by
  set X := (‖a ^ m‖₊ : ℝ≥0∞) with hX
  have hm_pos : 0 < m := by omega
  have hmRpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
  have hXrpow : (X ^ (1 / m : ℝ)) ^ (m : ℝ) = X := by
    calc
      (X ^ (1 / m : ℝ)) ^ (m : ℝ) = X ^ ((1 / (m : ℝ)) * (m : ℝ)) := by
        rw [ENNReal.rpow_mul X (1 / (m : ℝ)) (m : ℝ)]
      _ = X ^ (1 : ℝ) := by
        field_simp [hmRpos.ne.symm]
      _ = X := by simp
  have h_lt : (X ^ (1 / m : ℝ)) ^ (m : ℝ) < ρ ^ (m : ℝ) :=
    ENNReal.rpow_lt_rpow h hmRpos
  have h_goal : X < ρ ^ (m : ℝ) := by
    rw [hXrpow] at h_lt
    exact h_lt
  simpa [ENNReal.rpow_natCast] using h_goal

/-- **Gelfand bound on powers.** In a complex Banach algebra, if `r(a) < ρ` with
`ρ > 0`, then `‖a^m‖ ≤ ρ^m` for all sufficiently large `m`. -/
lemma gelfand_eventually_le {𝒜 : Type*} [NormedRing 𝒜] [NormedAlgebra ℂ 𝒜]
    [CompleteSpace 𝒜] (a : 𝒜) {ρ : ℝ} (hρ : 0 < ρ)
    (h : spectralRadius ℂ a < ENNReal.ofReal ρ) :
    ∀ᶠ m : ℕ in Filter.atTop, ‖a ^ m‖ ≤ ρ ^ m := by
  have hρ_nonneg : 0 ≤ ρ := by linarith
  have h_tendsto := spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius a
  have h_const : Filter.Tendsto (fun _ : ℕ => (ENNReal.ofReal ρ : ℝ≥0∞)) Filter.atTop (nhds (ENNReal.ofReal ρ)) :=
    tendsto_const_nhds
  have h_event_lt : ∀ᶠ m : ℕ in Filter.atTop, ((‖a ^ m‖₊ : ℝ≥0∞) ^ (1 / m : ℝ)) < (ENNReal.ofReal ρ : ℝ≥0∞) :=
    h_tendsto.eventually_lt h_const h
  have hm_one : ∀ᶠ m : ℕ in Filter.atTop, 1 ≤ m := by
    refine Filter.eventually_atTop.mpr ?_
    exact ⟨1, fun m hm => hm⟩
  have h_event_pow : ∀ᶠ m : ℕ in Filter.atTop, (‖a ^ m‖₊ : ℝ≥0∞) < (ENNReal.ofReal ρ : ℝ≥0∞) ^ m := by
    filter_upwards [h_event_lt, hm_one] with m hm hm1
    have hρ_ennpos : 0 < (ENNReal.ofReal ρ : ℝ≥0∞) := by
      rw [ENNReal.ofReal_pos]
      exact hρ
    exact enorm_pow_lt_of_root_lt a hρ_ennpos hm1 hm
  refine h_event_pow.mono fun m hm => ?_
  have h_lt_real : ‖a ^ m‖ < ρ ^ m := by
    have h_finite : (‖a ^ m‖₊ : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
    have h_finite' : (ENNReal.ofReal ρ : ℝ≥0∞) ^ m ≠ ∞ := ENNReal.pow_ne_top (ENNReal.ofReal_ne_top)
    have h_toReal := (ENNReal.toReal_lt_toReal h_finite h_finite').mpr hm
    simpa [toReal_coe_nnnorm', ENNReal.toReal_pow, ENNReal.toReal_ofReal hρ_nonneg] using h_toReal
  exact le_of_lt h_lt_real

/-- **Spectral radius below one forces power decay.** In a complex Banach algebra, if
`r(a) < 1` then `‖a^m‖ → 0`. -/
lemma tendsto_pow_norm_lt_one {𝒜 : Type*} [NormedRing 𝒜] [NormedAlgebra ℂ 𝒜]
    [CompleteSpace 𝒜] (a : 𝒜) (h : spectralRadius ℂ a < 1) :
    Filter.Tendsto (fun m : ℕ => ‖a ^ m‖) Filter.atTop (nhds 0) := by
  -- spectralRadius ℂ a is finite because it is < 1 < ⊤
  have hfinite_top : spectralRadius ℂ a < ⊤ := h.trans (by simp : (1 : ℝ≥0∞) < ⊤)
  have hfinite : spectralRadius ℂ a ≠ ⊤ := ne_of_lt hfinite_top
  -- Convert the ENNReal inequality to a real inequality
  have h_one_ne_top : (1 : ℝ≥0∞) ≠ ⊤ := by simp
  have h_toReal_lt_one : (spectralRadius ℂ a).toReal < 1 := by
    have := (ENNReal.toReal_lt_toReal hfinite h_one_ne_top).mpr h
    simpa using this
  -- Pick ρ with (spectralRadius ℂ a).toReal < ρ < 1
  rcases exists_between h_toReal_lt_one with ⟨ρ, hρ1, hρ2⟩
  -- Then ρ ≥ 0 because (spectralRadius ℂ a).toReal ≥ 0
  have hρ_nonneg : 0 ≤ ρ := by
    have h_nonneg : 0 ≤ (spectralRadius ℂ a).toReal := ENNReal.toReal_nonneg
    linarith
  have hρ_pos : 0 < ρ := by
    have h_nonneg : 0 ≤ (spectralRadius ℂ a).toReal := ENNReal.toReal_nonneg
    linarith
  have hρ_lt_one : ρ < 1 := hρ2
  -- From (spectralRadius ℂ a).toReal < ρ, get spectralRadius ℂ a < ENNReal.ofReal ρ
  have h_lt_ofReal : spectralRadius ℂ a < ENNReal.ofReal ρ := by
    calc
      spectralRadius ℂ a = ENNReal.ofReal ((spectralRadius ℂ a).toReal) := by
        simpa using (ENNReal.ofReal_toReal hfinite).symm
      _ < ENNReal.ofReal ρ :=
        (ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨hρ1, hρ_pos⟩)
  -- Apply Gelfand's lemma to get the eventual bound
  have hgelfand : ∀ᶠ m : ℕ in Filter.atTop, ‖a ^ m‖ ≤ ρ ^ m :=
    gelfand_eventually_le a hρ_pos h_lt_ofReal
  -- ρ^m → 0 because 0 ≤ ρ < 1
  have hpow_tendsto : Filter.Tendsto (fun m : ℕ => ρ ^ m) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hρ_nonneg hρ_lt_one
  -- norm is always nonnegative
  have h_norm_nonneg : ∀ m : ℕ, 0 ≤ ‖a ^ m‖ := fun m => norm_nonneg _
  -- Squeeze theorem
  apply squeeze_zero' (Filter.Eventually.of_forall h_norm_nonneg) hgelfand hpow_tendsto

/-! ### Continuous-time decay of the matrix exponential -/

/-- **Exponential of an integer multiple.** `e^{(m : ℝ) • B} = (e^{B})^m`. -/
lemma exp_smul_nat {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) :
    NormedSpace.exp ((m : ℝ) • B) = (NormedSpace.exp B) ^ m := by
  have h : (m : ℝ) • B = (m : ℕ) • B := by
    simpa using Nat.cast_smul_eq_nsmul (R := ℝ) (M := Matrix (Fin n) (Fin n) ℂ) m B
  rw [h]
  exact NormedSpace.exp_nsmul m B

/-- **Splitting the exponential at the integer part.** For `t ≥ 0` and `m = ⌊t⌋`,
`e^{t • B} = (e^{B})^m · e^{(t - m) • B}`. -/
lemma exp_smul_split {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) {t : ℝ} (_ht : 0 ≤ t) :
    NormedSpace.exp (t • B)
      = (NormedSpace.exp B) ^ (⌊t⌋₊) * NormedSpace.exp ((t - (⌊t⌋₊ : ℝ)) • B) := by
  set m := ⌊t⌋₊ with hm
  have ht_eq : t = (m : ℝ) + (t - (m : ℝ)) := by ring
  have h_comm : Commute ((m : ℝ) • B) ((t - (m : ℝ)) • B) := by
    have hB : Commute B B := Commute.refl B
    have h1 : Commute ((m : ℝ) • B) B := hB.smul_left (m : ℝ)
    exact h1.smul_right (t - (m : ℝ))
  have h_add : t • B = ((m : ℝ) • B) + ((t - (m : ℝ)) • B) := by
    calc
      t • B = ((m : ℝ) + (t - (m : ℝ))) • B := by
        rw [ht_eq]
        congr 1
        ring
      _ = (m : ℝ) • B + (t - (m : ℝ)) • B := by exact add_smul (m : ℝ) (t - (m : ℝ)) B
  calc
    NormedSpace.exp (t • B) = NormedSpace.exp (((m : ℝ) • B) + ((t - (m : ℝ)) • B)) := by rw [h_add]
    _ = NormedSpace.exp ((m : ℝ) • B) * NormedSpace.exp ((t - (m : ℝ)) • B) := by
      exact NormedSpace.exp_add_of_commute h_comm
    _ = (NormedSpace.exp B) ^ m * NormedSpace.exp ((t - (m : ℝ)) • B) := by rw [exp_smul_nat B m]
    _ = (NormedSpace.exp B) ^ (⌊t⌋₊) * NormedSpace.exp ((t - (⌊t⌋₊ : ℝ)) • B) := by rfl

/-- **Uniform bound on the exponential over the unit interval.** There is `M ≥ 0` with
`‖e^{s • B}‖ ≤ M` for all `s ∈ [0,1]`. -/
lemma bddAbove_exp_smul_unit {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖NormedSpace.exp (s • B)‖ ≤ M := by
  have h_norm_cont : ContinuousOn (fun (s : ℝ) => ‖NormedSpace.exp (s • B)‖) (Set.Icc (0 : ℝ) 1) := by
    have h_exp_cont : Continuous (fun (s : ℝ) => NormedSpace.exp (s • B)) := by
      have h_smul_cont : Continuous (fun (s : ℝ) => s • B) :=
        (Continuous.smul Complex.continuous_ofReal continuous_const : Continuous (fun s : ℝ => (s : ℂ) • B))
      exact NormedSpace.exp_continuous.comp h_smul_cont
    exact (h_exp_cont.norm).continuousOn
  have h_compact : IsCompact (Set.Icc (0 : ℝ) 1) := isCompact_Icc
  rcases h_compact.exists_bound_of_continuousOn h_norm_cont with ⟨M, hM⟩
  have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨by norm_num, by norm_num⟩
  have hM_zero_norm : ‖NormedSpace.exp ((0 : ℝ) • B)‖ ≤ M := by
    have htemp := hM 0 hzero
    simpa using htemp
  have hM_nonneg : 0 ≤ M := by
    have hzero_norm_nonneg : 0 ≤ ‖NormedSpace.exp ((0 : ℝ) • B)‖ := norm_nonneg _
    linarith
  refine ⟨M, hM_nonneg, ?_⟩
  intro s hs
  have htemp := hM s hs
  simpa using htemp

/-- **Bound on the exponential by its integer-power part.** There is `M ≥ 0` such that for
every `t ≥ 0`, with `m = ⌊t⌋`, `‖e^{t • B}‖ ≤ ‖(e^{B})^m‖ · M`. -/
lemma norm_exp_smul_le {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, 0 ≤ t →
      ‖NormedSpace.exp (t • B)‖ ≤ ‖(NormedSpace.exp B) ^ (⌊t⌋₊)‖ * M := by
  obtain ⟨M, hM_nonneg, hM⟩ := bddAbove_exp_smul_unit B
  refine ⟨M, hM_nonneg, ?_⟩
  intro t ht
  have hfrac_mem : (t - (⌊t⌋₊ : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · have := Nat.floor_le ht
      linarith
    · have := Nat.lt_floor_add_one t
      linarith
  rw [exp_smul_split B ht]
  calc
    ‖(NormedSpace.exp B) ^ (⌊t⌋₊) * NormedSpace.exp ((t - (⌊t⌋₊ : ℝ)) • B)‖
        ≤ ‖(NormedSpace.exp B) ^ (⌊t⌋₊)‖ * ‖NormedSpace.exp ((t - (⌊t⌋₊ : ℝ)) • B)‖ :=
          norm_mul_le _ _
    _ ≤ ‖(NormedSpace.exp B) ^ (⌊t⌋₊)‖ * M :=
          mul_le_mul_of_nonneg_left (hM _ hfrac_mem) (norm_nonneg _)

/-- **Continuous-time decay of the exponential.** If `r(e^{B}) < 1` then
`‖e^{t • B}‖ → 0` as `t → ∞`. -/
lemma norm_exp_smul_tendsto_zero {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (hB : spectralRadius ℂ (NormedSpace.exp B) < 1) :
    Filter.Tendsto (fun t : ℝ => ‖NormedSpace.exp (t • B)‖) Filter.atTop (nhds 0) := by
  rcases norm_exp_smul_le B with ⟨M, hM_nonneg, hM⟩
  have h_pow_tendsto : Filter.Tendsto (fun m : ℕ => ‖(NormedSpace.exp B) ^ m‖) Filter.atTop (nhds 0) :=
    tendsto_pow_norm_lt_one (NormedSpace.exp B) hB
  have h_floor_tendsto : Filter.Tendsto (fun t : ℝ => (⌊t⌋₊ : ℕ)) Filter.atTop Filter.atTop :=
    tendsto_nat_floor_atTop
  have h_bound_tendsto : Filter.Tendsto (fun t : ℝ => ‖(NormedSpace.exp B) ^ (⌊t⌋₊)‖) Filter.atTop (nhds 0) :=
    h_pow_tendsto.comp h_floor_tendsto
  have h_bound_mul_tendsto : Filter.Tendsto (fun t : ℝ => ‖(NormedSpace.exp B) ^ (⌊t⌋₊)‖ * M) Filter.atTop (nhds 0) := by
    simpa [mul_zero] using h_bound_tendsto.mul_const M
  have h_nonneg : ∀ᶠ t : ℝ in Filter.atTop, 0 ≤ ‖NormedSpace.exp (t • B)‖ :=
    Filter.eventually_atTop.mpr ⟨0, fun t ht => norm_nonneg _⟩
  have h_ineq : ∀ᶠ t : ℝ in Filter.atTop, ‖NormedSpace.exp (t • B)‖ ≤ ‖(NormedSpace.exp B) ^ (⌊t⌋₊)‖ * M := by
    refine Filter.eventually_atTop.mpr ⟨0, fun t ht => hM t ht⟩
  exact squeeze_zero' h_nonneg h_ineq h_bound_mul_tendsto

/-! ### Solution representation by the matrix exponential -/

/-- **Multiplying a matrix by a fixed vector is continuous linear.** For `v : Fin n → ℝ`
the map `M ↦ M *ᵥ v` is a continuous linear map. -/
lemma mulVec_right_clm {n : ℕ} (v : Fin n → ℝ) :
    ∃ L : Matrix (Fin n) (Fin n) ℝ →L[ℝ] (Fin n → ℝ), ⇑L = fun M => M.mulVec v := by
  let L : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun M => M.mulVec v
      map_add' := fun x y => by simp [Matrix.add_mulVec]
      map_smul' := fun r x => by simp [Matrix.smul_mulVec] }
  refine ⟨LinearMap.toContinuousLinearMap L, ?_⟩
  rfl

/-- **Derivative of `τ ↦ e^{(τ - t₁) • A}`.** Its derivative at `t` is `A · e^{(t-t₁) • A}`. -/
lemma exp_smul_hasDerivAt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (t₁ t : ℝ) :
    HasDerivAt (fun τ : ℝ => NormedSpace.exp ((τ - t₁) • A))
      (A * NormedSpace.exp ((t - t₁) • A)) t := by
  have h_inner : HasDerivAt (fun τ : ℝ => τ - t₁) (1 : ℝ) t :=
    (hasDerivAt_id t).sub_const t₁
  have h_outer : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • A))
      (A * NormedSpace.exp (((t - t₁) : ℝ) • A)) (t - t₁) :=
    hasDerivAt_exp_smul_const' A (t - t₁)
  have h_comp := h_outer.scomp t h_inner
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  let φ : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun M => M i j
      map_add' := fun M N => rfl
      map_smul' := fun c M => rfl }
  have hφ_cont : Continuous (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) :=
    φ.continuous_of_finiteDimensional
  let φL : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ := ⟨φ, hφ_cont⟩
  have h_coord := h_comp.comp_semilinear (RingHom.id ℝ) φL
  have hφL_apply (M : Matrix (Fin n) (Fin n) ℝ) : φL M = M i j := rfl
  have h_coord_fun :
      (⇑φL ∘ ((fun u : ℝ => NormedSpace.exp (u • A)) ∘ fun τ : ℝ => τ - t₁) ∘
          ⇑(RingHom.id ℝ)) =
        (fun x => NormedSpace.exp ((x - t₁) • A) i j) := by
    funext x
    change φL (NormedSpace.exp ((x - t₁) • A)) = NormedSpace.exp ((x - t₁) • A) i j
    exact hφL_apply _
  have h_coord_deriv : φL ((1 : ℝ) • (A * NormedSpace.exp ((t - t₁) • A))) =
      (A * NormedSpace.exp ((t - t₁) • A)) i j := by
    rw [one_smul]
    exact hφL_apply _
  have h_coord' := h_coord.congr_deriv h_coord_deriv
  refine h_coord'.congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall fun x => (congrFun h_coord_fun x).symm

/-- **Derivative of `τ ↦ e^{(τ - t₁) • A} v`.** Its derivative at `t` is
`A · (e^{(t-t₁) • A} v)`. -/
lemma exp_smul_mulVec_hasDerivAt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) (t₁ t : ℝ) :
    HasDerivAt (fun τ : ℝ => (NormedSpace.exp ((τ - t₁) • A)).mulVec v)
      (A.mulVec ((NormedSpace.exp ((t - t₁) • A)).mulVec v)) t := by
  -- By exp_smul_hasDerivAt, τ ↦ e^{(τ - t₁) • A} has derivative A·e^{(t-t₁)•A} at t.
  have h_exp : HasDerivAt (fun τ : ℝ => NormedSpace.exp ((τ - t₁) • A))
      (A * NormedSpace.exp ((t - t₁) • A)) t :=
    exp_smul_hasDerivAt A t₁ t
  -- By mulVec_right_clm, M ↦ M.mulVec v is a continuous linear map.
  rcases mulVec_right_clm v with ⟨L, hL⟩
  -- L is a ContinuousLinearMap, so by HasDerivAt.comp_semilinear, composition preserves
  -- the derivative: (L ∘ f) has derivative L(f') at t.
  have h_comp : HasDerivAt (L ∘ (fun τ : ℝ => NormedSpace.exp ((τ - t₁) • A)))
      (L (A * NormedSpace.exp ((t - t₁) • A))) t :=
    h_exp.comp_semilinear (RingHom.id ℝ) L
  -- Unfold L ∘ f to the actual function we want.
  have hL_apply : (L ∘ (fun τ : ℝ => NormedSpace.exp ((τ - t₁) • A))) =
      (fun τ : ℝ => (NormedSpace.exp ((τ - t₁) • A)).mulVec v) := by
    ext τ
    simp [hL]
  rw [hL_apply] at h_comp
  -- Finally, rewrite the derivative using associativity of matrix-vector multiplication.
  have h_mulVec : L (A * NormedSpace.exp ((t - t₁) • A)) =
      A.mulVec ((NormedSpace.exp ((t - t₁) • A)).mulVec v) := by
    calc
      L (A * NormedSpace.exp ((t - t₁) • A)) = ((A * NormedSpace.exp ((t - t₁) • A)).mulVec v) := by
        simp [hL]
      _ = A.mulVec ((NormedSpace.exp ((t - t₁) • A)).mulVec v) := by
        -- using Matrix.mulVec_mulVec: (A * B).mulVec v = A.mulVec (B.mulVec v)
        simp [Matrix.mulVec_mulVec]
  rw [h_mulVec] at h_comp
  exact h_comp

/-- **The linear vector field is Lipschitz.** The map `z ↦ A *ᵥ z` is `K`-Lipschitz for
some constant `K`. -/
lemma vectorField_lipschitz {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ K : ℝ≥0, LipschitzWith K (fun z : Fin n → ℝ => A.mulVec z) := by
  let L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) := Matrix.mulVecLin A
  let Lc : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := LinearMap.toContinuousLinearMap L
  refine ⟨‖Lc‖₊, ?_⟩
  have hLipschitz : LipschitzWith ‖Lc‖₊ Lc := Lc.lipschitz
  have hLc_eq : (Lc : (Fin n → ℝ) → (Fin n → ℝ)) = fun z => A.mulVec z := by
    ext z
    simp [L, Lc, Matrix.mulVecLin]
  simpa [hLc_eq] using hLipschitz

/-- **The exponential propagator is a solution.** With `y τ = e^{(τ - t₁) • A} w`, for
every `τ` we have `HasDerivAt y (A · y τ) τ` and `y τ ∈ univ`, and `y t₁ = w`. -/
lemma exp_smul_isSolution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ)
    (t₁ : ℝ) :
    (∀ τ : ℝ,
        HasDerivAt (fun s : ℝ => (NormedSpace.exp ((s - t₁) • A)).mulVec w)
          (A.mulVec ((NormedSpace.exp ((τ - t₁) • A)).mulVec w)) τ ∧
        (NormedSpace.exp ((τ - t₁) • A)).mulVec w ∈ (Set.univ : Set (Fin n → ℝ))) ∧
      (NormedSpace.exp ((t₁ - t₁) • A)).mulVec w = w := by
  constructor
  · intro τ
    constructor
    · exact exp_smul_mulVec_hasDerivAt A w t₁ τ
    · exact Set.mem_univ _
  · simp

/-- **Uniqueness of linear ODE solutions on an open interval.** Two functions solving
`f' = A f` on `(a, b)` that agree at one interior point agree on `(a, b)`. -/
lemma ODE_solution_unique_univ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {a b : ℝ}
    {f g : ℝ → (Fin n → ℝ)} {t₀ : ℝ}
    (hf : ∀ τ ∈ Set.Ioo a b, HasDerivAt f (A.mulVec (f τ)) τ)
    (hg : ∀ τ ∈ Set.Ioo a b, HasDerivAt g (A.mulVec (g τ)) τ)
    (ht₀ : t₀ ∈ Set.Ioo a b) (heq : f t₀ = g t₀) :
    Set.EqOn f g (Set.Ioo a b) := by
  rcases vectorField_lipschitz A with ⟨K, hK⟩
  intro τ hτ
  rcases le_total t₀ τ with hforward | hbackward
  · have hsubset : Set.Icc t₀ τ ⊆ Set.Ioo a b := by
      intro s hs
      exact ⟨lt_of_lt_of_le ht₀.1 hs.1, lt_of_le_of_lt hs.2 hτ.2⟩
    have hf_cont : ContinuousOn f (Set.Icc t₀ τ) :=
      HasDerivAt.continuousOn fun s hs => hf s (hsubset hs)
    have hg_cont : ContinuousOn g (Set.Icc t₀ τ) :=
      HasDerivAt.continuousOn fun s hs => hg s (hsubset hs)
    have hf_within : ∀ s ∈ Set.Ico t₀ τ,
        HasDerivWithinAt f (A.mulVec (f s)) (Set.Ici s) s := by
      intro s hs
      exact (hf s (hsubset (Set.Ico_subset_Icc_self hs))).hasDerivWithinAt
    have hg_within : ∀ s ∈ Set.Ico t₀ τ,
        HasDerivWithinAt g (A.mulVec (g s)) (Set.Ici s) s := by
      intro s hs
      exact (hg s (hsubset (Set.Ico_subset_Icc_self hs))).hasDerivWithinAt
    have hdist := dist_le_of_trajectories_ODE
      (v := fun _ z => A.mulVec z) (K := K) (a := t₀) (b := τ) (δ := 0)
      (fun _ => hK) hf_cont hf_within hg_cont hg_within
      (by simp [heq]) τ ⟨hforward, le_rfl⟩
    apply dist_eq_zero.mp
    exact le_antisymm (by simpa using hdist) dist_nonneg
  · let T := t₀ - τ
    let fr : ℝ → (Fin n → ℝ) := fun s => f (t₀ - s)
    let gr : ℝ → (Fin n → ℝ) := fun s => g (t₀ - s)
    have hT : 0 ≤ T := by
      dsimp [T]
      linarith
    have horig : ∀ s ∈ Set.Icc (0 : ℝ) T, t₀ - s ∈ Set.Ioo a b := by
      intro s hs
      dsimp [T] at hs
      constructor
      · have hle : τ ≤ t₀ - s := by linarith [hs.2]
        exact lt_of_lt_of_le hτ.1 hle
      · have hle : t₀ - s ≤ t₀ := by linarith [hs.1]
        exact lt_of_le_of_lt hle ht₀.2
    have hfr_deriv : ∀ s ∈ Set.Icc (0 : ℝ) T,
        HasDerivAt fr (-(A.mulVec (fr s))) s := by
      intro s hs
      have h_inner_raw := (hasDerivAt_const s t₀).sub (hasDerivAt_id s)
      have h_inner_fun : ((fun _ : ℝ => t₀) - id) = (fun q : ℝ => t₀ - q) := by
        ext q
        rfl
      have h_inner : HasDerivAt (fun q : ℝ => t₀ - q) (-1) s := by
        rw [← h_inner_fun]
        simpa using h_inner_raw
      have h_comp := (hf (t₀ - s) (horig s hs)).scomp s h_inner
      simpa [fr, Function.comp_def] using h_comp
    have hgr_deriv : ∀ s ∈ Set.Icc (0 : ℝ) T,
        HasDerivAt gr (-(A.mulVec (gr s))) s := by
      intro s hs
      have h_inner_raw := (hasDerivAt_const s t₀).sub (hasDerivAt_id s)
      have h_inner_fun : ((fun _ : ℝ => t₀) - id) = (fun q : ℝ => t₀ - q) := by
        ext q
        rfl
      have h_inner : HasDerivAt (fun q : ℝ => t₀ - q) (-1) s := by
        rw [← h_inner_fun]
        simpa using h_inner_raw
      have h_comp := (hg (t₀ - s) (horig s hs)).scomp s h_inner
      simpa [gr, Function.comp_def] using h_comp
    have hK_neg_raw : LipschitzWith K (-(fun z : Fin n → ℝ => A.mulVec z)) := hK.neg
    have hneg_fun : -(fun z : Fin n → ℝ => A.mulVec z) =
        (fun z : Fin n → ℝ => -(A.mulVec z)) := by
      ext z i
      rfl
    have hK_neg : LipschitzWith K (fun z : Fin n → ℝ => -(A.mulVec z)) := by
      rw [← hneg_fun]
      exact hK_neg_raw
    have hfr_cont : ContinuousOn fr (Set.Icc (0 : ℝ) T) :=
      HasDerivAt.continuousOn hfr_deriv
    have hgr_cont : ContinuousOn gr (Set.Icc (0 : ℝ) T) :=
      HasDerivAt.continuousOn hgr_deriv
    have hfr_within : ∀ s ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt fr (-(A.mulVec (fr s))) (Set.Ici s) s := by
      intro s hs
      exact (hfr_deriv s (Set.Ico_subset_Icc_self hs)).hasDerivWithinAt
    have hgr_within : ∀ s ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt gr (-(A.mulVec (gr s))) (Set.Ici s) s := by
      intro s hs
      exact (hgr_deriv s (Set.Ico_subset_Icc_self hs)).hasDerivWithinAt
    have hdist := dist_le_of_trajectories_ODE
      (v := fun _ z => -(A.mulVec z)) (K := K) (a := 0) (b := T) (δ := 0)
      (fun _ => hK_neg) hfr_cont hfr_within hgr_cont hgr_within
      (by simp [fr, gr, heq]) T ⟨hT, le_rfl⟩
    have hzero : dist (fr T) (gr T) = 0 :=
      le_antisymm (by simpa using hdist) dist_nonneg
    simpa [fr, gr, T] using dist_eq_zero.mp hzero

/-- **Agreement of a solution and the propagator on `(0, b)`.** A solution of `x' = A x`
on `(0, b)` agrees there with `τ ↦ e^{(τ - t₁) • A} x(t₁)` for any base point `t₁`. -/
lemma solution_eqOn_exp_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {b : ℝ}
    {x : ℝ → (Fin n → ℝ)}
    (hx : ∀ τ ∈ Set.Ioo (0 : ℝ) b, HasDerivAt x (A.mulVec (x τ)) τ)
    {t₁ : ℝ} (ht₁ : t₁ ∈ Set.Ioo (0 : ℝ) b) :
    Set.EqOn x (fun τ => (NormedSpace.exp ((τ - t₁) • A)).mulVec (x t₁))
      (Set.Ioo (0 : ℝ) b) := by
  set y := fun τ : ℝ => (NormedSpace.exp ((τ - t₁) • A)).mulVec (x t₁) with hy
  have hsol := exp_smul_isSolution A (x t₁) t₁
  have hy_deriv : ∀ τ ∈ Set.Ioo (0 : ℝ) b, HasDerivAt y (A.mulVec (y τ)) τ := by
    intro τ hτ
    have h_all : HasDerivAt y (A.mulVec (y τ)) τ := (hsol.1 τ).1
    exact h_all
  have hy_t₁ : y t₁ = x t₁ := hsol.2
  exact ODE_solution_unique_univ A hx hy_deriv ht₁ hy_t₁.symm

/-- **Solutions are matrix exponentials of the initial value.** A solution of `x' = A x`
on `(0, ∞)` satisfies `x t = e^{(t - t₁) • A} x(t₁)` for all `t, t₁ > 0`. -/
lemma solution_eq_exp_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {x : ℝ → (Fin n → ℝ)}
    (hx : ∀ t : ℝ, 0 < t → HasDerivAt x (A.mulVec (x t)) t)
    {t₁ : ℝ} (ht₁ : 0 < t₁) {t : ℝ} (ht : 0 < t) :
    x t = (NormedSpace.exp ((t - t₁) • A)).mulVec (x t₁) := by
  set b := max t t₁ + 1 with hb_def
  have hb_pos : 0 < b := by
    have hpos : 0 < max t t₁ := lt_max_iff.mpr (Or.inl ht)
    nlinarith
  have hx' : ∀ τ ∈ Set.Ioo (0 : ℝ) b, HasDerivAt x (A.mulVec (x τ)) τ := by
    intro τ hτ
    rcases Set.mem_Ioo.mp hτ with ⟨hτ_left, hτ_right⟩
    exact hx τ hτ_left
  have ht₁_mem : t₁ ∈ Set.Ioo (0 : ℝ) b := by
    refine Set.mem_Ioo.mpr ⟨ht₁, ?_⟩
    calc
      t₁ ≤ max t t₁ := le_max_right t t₁
      _ < max t t₁ + 1 := by nlinarith
      _ = b := rfl
  have ht_mem : t ∈ Set.Ioo (0 : ℝ) b := by
    refine Set.mem_Ioo.mpr ⟨ht, ?_⟩
    calc
      t ≤ max t t₁ := le_max_left t t₁
      _ < max t t₁ + 1 := by nlinarith
      _ = b := rfl
  have h_eq_on := solution_eqOn_exp_smul A hx' ht₁_mem
  have h_eq := h_eq_on ht_mem
  exact h_eq

/-! ### Complexification and the main theorem -/

/-- **Eigenvalue hypothesis as a spectral condition.** If every eigenvalue of `toLin' B`
has negative real part, then every `μ ∈ σ(B)` has negative real part, where
`B = A.map (algebraMap ℝ ℂ)`. -/
lemma eigenvalue_re_neg_spectrum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ μ : ℂ,
        Module.End.HasEigenvalue (Matrix.toLin' (A.map (algebraMap ℝ ℂ))) μ → μ.re < 0)
    {μ : ℂ} (hμ : μ ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ))) :
    μ.re < 0 := by
  set B := A.map (algebraMap ℝ ℂ) with hB
  -- Fin n → ℂ is a finite-dimensional ℂ-vector space
  haveI : FiniteDimensional ℂ (Fin n → ℂ) := inferInstance
  -- Matrix.toLinAlgEquiv' is an algebra isomorphism from matrices to endomorphisms
  let φ : Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] ((Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) :=
    Matrix.toLinAlgEquiv' (R := ℂ)
  -- Algebra isomorphisms preserve the spectrum: spectrum ℂ (φ B) = spectrum ℂ B
  have hspec_eq : spectrum ℂ (φ B) = spectrum ℂ B :=
    AlgEquiv.spectrum_eq φ B
  -- Since μ ∈ spectrum ℂ B, we get μ ∈ spectrum ℂ (φ B)
  have hμ' : μ ∈ spectrum ℂ (φ B) := by
    rw [hspec_eq]
    exact hμ
  -- In finite dimensions, μ ∈ spectrum ℂ (φ B) iff μ is an eigenvalue of φ B
  have heig : Module.End.HasEigenvalue (φ B) μ := by
    rw [Module.End.hasEigenvalue_iff_mem_spectrum]
    exact hμ'
  -- φ B = Matrix.toLin' B as endomorphisms
  have hφ_eq : (φ B : Module.End ℂ (Fin n → ℂ)) = Matrix.toLin' B := by
    apply LinearMap.ext; intro v
    calc
      (φ B) v = B *ᵥ v := by simp [φ, Matrix.toLinAlgEquiv'_apply]
      _ = Matrix.toLin' B v := by simp [Matrix.toLin'_apply]
  -- Relabel using the equality
  have heig' : Module.End.HasEigenvalue (Matrix.toLin' B) μ := by
    simpa [hφ_eq] using heig
  -- Apply the hypothesis hA
  exact hA μ heig'

/-- **Complexification is norm-preserving on vectors.** `‖(i ↦ (w i : ℂ))‖ = ‖w‖`. -/
lemma norm_complexify_vec {n : ℕ} (w : Fin n → ℝ) :
    ‖fun i => (w i : ℂ)‖ = ‖w‖ := by
  rw [Pi.norm_def (f := fun i : Fin n => (w i : ℂ))]
  rw [Pi.norm_def (f := w)]
  simp [Complex.nnnorm_real]

/-- **Matrix exponential commutes with entrywise complexification.**
`(e^{M}).map (algebraMap ℝ ℂ) = e^{M.map (algebraMap ℝ ℂ)}`. -/
lemma exp_map_complexify {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    (NormedSpace.exp M).map (algebraMap ℝ ℂ)
      = NormedSpace.exp (M.map (algebraMap ℝ ℂ)) := by
  let f : Matrix (Fin n) (Fin n) ℝ →+* Matrix (Fin n) (Fin n) ℂ :=
    (algebraMap ℝ ℂ).mapMatrix
  have hf_cont : Continuous (f : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℂ) := by
    apply continuous_matrix
    intro i j
    have h_proj : Continuous (fun (M : Matrix (Fin n) (Fin n) ℝ) => M i j) :=
      (continuous_apply j).comp (continuous_apply i)
    have h_entry : (fun a : Matrix (Fin n) (Fin n) ℝ => f a i j) =
        Complex.ofReal ∘ fun a : Matrix (Fin n) (Fin n) ℝ => a i j := by
      funext a
      simp [f, RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [h_entry]
    exact Complex.continuous_ofReal.comp h_proj
  calc
    (NormedSpace.exp M).map (algebraMap ℝ ℂ) = f (NormedSpace.exp M) := by
      simp [f, RingHom.mapMatrix_apply]
    _ = NormedSpace.exp (f M) := by
      exact NormedSpace.map_exp f hf_cont M
    _ = NormedSpace.exp (M.map (algebraMap ℝ ℂ)) := by
      simp [f, RingHom.mapMatrix_apply]

/-- **Complexification commutes with `e^{sA} w`.** With `B = A.map (algebraMap ℝ ℂ)`,
`(e^{s • A} w)_ℂ = e^{s • B} w_ℂ`. -/
lemma complexify_exp_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ)
    (s : ℝ) :
    (fun i => (((NormedSpace.exp (s • A)).mulVec w) i : ℂ))
      = (NormedSpace.exp (s • A.map (algebraMap ℝ ℂ))).mulVec (fun i => (w i : ℂ)) := by
  ext i
  calc
    (fun i => (((NormedSpace.exp (s • A)).mulVec w) i : ℂ)) i
        = (algebraMap ℝ ℂ) (((NormedSpace.exp (s • A)).mulVec w) i) := rfl
    _ = ((NormedSpace.exp (s • A)).map (algebraMap ℝ ℂ) *ᵥ (algebraMap ℝ ℂ ∘ w)) i := by
      rw [RingHom.map_mulVec (algebraMap ℝ ℂ) (NormedSpace.exp (s • A)) w i]
    _ = ((NormedSpace.exp (s • A)).map (algebraMap ℝ ℂ)).mulVec (fun i => (w i : ℂ)) i := by
      simp [Function.comp_def]
    _ = (NormedSpace.exp ((s • A).map (algebraMap ℝ ℂ))).mulVec (fun i => (w i : ℂ)) i := by
      rw [exp_map_complexify (s • A)]
    _ = (NormedSpace.exp (s • A.map (algebraMap ℝ ℂ))).mulVec (fun i => (w i : ℂ)) i := by
      rw [Matrix.map_smul (algebraMap ℝ ℂ) s (by intro a; simp) A]
    _ = (NormedSpace.exp (s • A.map (algebraMap ℝ ℂ))).mulVec (fun i => (w i : ℂ)) i := rfl

/-- **Pointwise bound on the solution.** With `B = A.map (algebraMap ℝ ℂ)`, a solution of
`x' = A x` on `(0, ∞)` satisfies `‖x t‖ ≤ ‖e^{(t-1) • B}‖ · ‖x 1‖` for all `t > 0`. -/
lemma norm_solution_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {x : ℝ → (Fin n → ℝ)}
    (hx : ∀ t : ℝ, 0 < t → HasDerivAt x (A.mulVec (x t)) t)
    {t : ℝ} (ht : 0 < t) :
    ‖x t‖ ≤ ‖NormedSpace.exp ((t - 1) • A.map (algebraMap ℝ ℂ))‖ * ‖x 1‖ := by
  have h1pos : (0 : ℝ) < 1 := by norm_num
  have hx_eq : x t = (NormedSpace.exp ((t - 1) • A)).mulVec (x 1) :=
    solution_eq_exp_smul A hx h1pos ht
  set s := t - 1 with hs
  set B := A.map (algebraMap ℝ ℂ) with hB
  have h_cx_eq : (fun i : Fin n => (x t i : ℂ)) =
      (NormedSpace.exp (s • B)).mulVec (fun i : Fin n => (x 1 i : ℂ)) := by
    calc
      (fun i : Fin n => (x t i : ℂ)) =
          (fun i : Fin n => (((NormedSpace.exp ((t - 1) • A)).mulVec (x 1)) i : ℂ)) := by
        rw [hx_eq]
      _ = (fun i : Fin n => (((NormedSpace.exp (s • A)).mulVec (x 1)) i : ℂ)) := by simp [hs]
      _ = (NormedSpace.exp (s • A.map (algebraMap ℝ ℂ))).mulVec (fun i : Fin n => (x 1 i : ℂ)) := by
        rw [complexify_exp_mulVec A (x 1) s]
      _ = (NormedSpace.exp (s • B)).mulVec (fun i : Fin n => (x 1 i : ℂ)) := by simp [hB]
  calc
    ‖x t‖ = ‖(fun i : Fin n => (x t i : ℂ))‖ := by
      symm; exact norm_complexify_vec (x t)
    _ = ‖(NormedSpace.exp (s • B)).mulVec (fun i : Fin n => (x 1 i : ℂ))‖ := by rw [h_cx_eq]
    _ ≤ ‖NormedSpace.exp (s • B)‖ * ‖(fun i : Fin n => (x 1 i : ℂ))‖ :=
      Matrix.linfty_opNorm_mulVec (NormedSpace.exp (s • B)) (fun i : Fin n => (x 1 i : ℂ))
    _ = ‖NormedSpace.exp (s • B)‖ * ‖x 1‖ := by rw [norm_complexify_vec (x 1)]
    _ = ‖NormedSpace.exp ((t - 1) • A.map (algebraMap ℝ ℂ))‖ * ‖x 1‖ := by simp [hs, hB]

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
  set B := A.map (algebraMap ℝ ℂ) with hB
  have hB_spectrum : ∀ μ ∈ spectrum ℂ B, μ.re < 0 := by
    intro μ hμ
    exact eigenvalue_re_neg_spectrum A hA hμ
  have h_rad_lt_one : spectralRadius ℂ (NormedSpace.exp B) < 1 :=
    spectralRadius_exp_lt_one B hB_spectrum
  have h_exp_tendsto : Filter.Tendsto (fun s : ℝ => ‖NormedSpace.exp (s • B)‖) Filter.atTop (nhds 0) :=
    norm_exp_smul_tendsto_zero B h_rad_lt_one
  have h_norm_bound : ∀ t : ℝ, 0 < t → ‖x t‖ ≤ ‖NormedSpace.exp ((t - 1) • B)‖ * ‖x 1‖ := by
    intro t ht
    exact norm_solution_le A hx ht
  have h_nonneg : ∀ t : ℝ, 0 ≤ ‖x t‖ := fun t => norm_nonneg _
  have h_shift : Filter.Tendsto (fun t : ℝ => t - 1) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_atTop.mpr ?_
    intro b
    refine ⟨b + 1, fun t ht => ?_⟩
    linarith
  have h_comp_tendsto : Filter.Tendsto (fun t : ℝ => ‖NormedSpace.exp ((t - 1) • B)‖) Filter.atTop (nhds 0) :=
    h_exp_tendsto.comp h_shift
  have h_mul_tendsto : Filter.Tendsto (fun t : ℝ => ‖NormedSpace.exp ((t - 1) • B)‖ * ‖x 1‖) Filter.atTop (nhds 0) := by
    simpa [mul_zero] using h_comp_tendsto.mul_const (‖x 1‖)
  have h_event_bound : ∀ᶠ t : ℝ in Filter.atTop, ‖x t‖ ≤ ‖NormedSpace.exp ((t - 1) • B)‖ * ‖x 1‖ := by
    refine Filter.eventually_atTop.mpr ⟨1, fun t ht => h_norm_bound t ?_⟩
    linarith
  have h_nonneg_event : ∀ᶠ t : ℝ in Filter.atTop, 0 ≤ ‖x t‖ := by
    refine Filter.eventually_atTop.mpr ⟨0, fun t ht => h_nonneg t⟩
  refine squeeze_zero' h_nonneg_event h_event_bound h_mul_tendsto

end ODE
end Analysis
end LeanEval
