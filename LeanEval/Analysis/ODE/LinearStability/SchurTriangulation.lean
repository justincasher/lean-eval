import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Logic.Equiv.Sum
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Schur triangulation

This file is ported from the `Physlib` project (module `Physlib.Mathematics.SchurTriangulation`),
because the pinned Mathlib in this repository does not yet contain Schur triangulation.

It proves that any matrix over an algebraically closed field (in particular any complex matrix)
is unitarily similar to an upper triangular matrix: `Matrix.schur_triangulation`.
-/

open scoped Matrix InnerProductSpace

section FinHelpers

variable {m n : ℕ}

/-- `subNat' i h` subtracts `m` from `i`. This is an alternative form of `Fin.subNat`. -/
@[inline] def Fin.subNat' (i : Fin (m + n)) (h : ¬ i < m) : Fin n :=
  Fin.subNat m (Fin.cast (m.add_comm n) i) (Nat.ge_of_not_lt h)

namespace Equiv

/-- An alternative form of `Equiv.sumEquivSigmaBool` where `Bool.casesOn` is replaced by `cond`. -/
def sumEquivSigmalCond : Fin m ⊕ Fin n ≃ Σ b, cond b (Fin m) (Fin n) :=
  calc Fin m ⊕ Fin n
    _ ≃ Fin n ⊕ Fin m := sumComm ..
    _ ≃ Σ b, bif b then (Fin m) else (Fin n) := sumEquivSigmaBool ..
    _ ≃ Σ b, cond b (Fin m) (Fin n) := sigmaCongrRight (fun | true | false => Equiv.refl _)

/-- The composition of `finSumFinEquiv` and `Equiv.sumEquivSigmalCond` used by
`LinearMap.SchurTriangulationAux.of`. -/
def finAddEquivSigmaCond : Fin (m + n) ≃ Σ b, cond b (Fin m) (Fin n) :=
  finSumFinEquiv.symm.trans sumEquivSigmalCond

variable {i : Fin (m + n)}

lemma finAddEquivSigmaCond_true (h : i < m) : finAddEquivSigmaCond i = ⟨true, i, h⟩ :=
  congrArg sumEquivSigmalCond <| finSumFinEquiv_symm_apply_castAdd ⟨i, h⟩

lemma finAddEquivSigmaCond_false (h : ¬ i < m) : finAddEquivSigmaCond i = ⟨false, i.subNat' h⟩ :=
  let j : Fin n := i.subNat' h
  calc finAddEquivSigmaCond i
    _ = finAddEquivSigmaCond (Fin.natAdd m j) :=
      suffices m + (i - m) = i from congrArg _ (Fin.ext this.symm)
      Nat.add_sub_of_le (Nat.le_of_not_gt h)
    _ = ⟨false, i.subNat' h⟩ := congrArg sumEquivSigmalCond <| finSumFinEquiv_symm_apply_natAdd j

end Equiv

end FinHelpers

section CondInstances

universe u
variable {m n : Type u}

/-- The type family parameterized by `Bool` is finite if each type variant is finite. -/
instance instFintypeCondPhys [M : Fintype m] [N : Fintype n] (b : Bool) : Fintype (cond b m n) :=
  b.rec N M

/-- Each `Bool`-indexed variant has decidable equality. -/
instance instDecidableEqCondPhys [DecidableEq m] [DecidableEq n] (b : Bool) :
    DecidableEq (cond b m n) := b.rec ‹_› ‹_›

/-- The type family parameterized by `Bool` has decidable equality if each type variant is
decidable. -/
instance instDecidableEqSigmaCondPhys [DecidableEq m] [DecidableEq n] :
    DecidableEq (Σ b, cond b m n) := inferInstance

end CondInstances

namespace Matrix

variable {n R : Type*} [LT n] [CommRing R]

/-- The property of a matrix being upper triangular. See also `Matrix.det_of_upperTriangular`. -/
abbrev IsUpperTriangular (A : Matrix n n R) := A.BlockTriangular id

/-- The subtype of upper triangular matrices. -/
abbrev UpperTriangular (n R) [LT n] [CommRing R] := { A : Matrix n n R // A.IsUpperTriangular }

end Matrix

namespace LinearMap

variable {𝕜 : Type*} [RCLike 𝕜] [IsAlgClosed 𝕜]

/-- **Don't use this definition directly.** Instead, use `Matrix.schurTriangulationBasis`,
`Matrix.schurTriangulationUnitary`, and `Matrix.schurTriangulation`. See also
`LinearMap.SchurTriangulationAux.of` and `Matrix.schurTriangulationAux`. -/
structure SchurTriangulationAux {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (f : Module.End 𝕜 E) where
  /-- The dimension of the inner product space `E`. -/
  dim : ℕ
  hdim : Module.finrank 𝕜 E = dim
  /-- An orthonormal basis of `E` that induces an upper triangular form for `f`. -/
  basis : OrthonormalBasis (Fin dim) 𝕜 E
  upperTriangular : (toMatrix basis.toBasis basis.toBasis f).IsUpperTriangular

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
/-- **Don't use this definition directly.** This is the key algorithm behind
`Matrix.schur_triangulation`. -/
protected noncomputable def SchurTriangulationAux.of {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] (f : Module.End 𝕜 E) :
    SchurTriangulationAux f :=
  haveI : Decidable (Nontrivial E) := Classical.propDecidable _
  if hE : Nontrivial E then
    let μ : f.Eigenvalues := default
    let V : Submodule 𝕜 E := f.eigenspace μ
    let W : Submodule 𝕜 E := Vᗮ
    let m := Module.finrank 𝕜 V
    have hdim : m + Module.finrank 𝕜 W = Module.finrank 𝕜 E := V.finrank_add_finrank_orthogonal
    let g : Module.End 𝕜 W := Submodule.orthogonalProjectionOnto W ∘ₗ f.domRestrict W
    let ⟨n, hn, bW, hg⟩ := SchurTriangulationAux.of g

    have bV : OrthonormalBasis (Fin m) 𝕜 V := stdOrthonormalBasis 𝕜 V
    have hV := V.orthogonalFamily_self
    have int : DirectSum.IsInternal (cond · V W) :=
      suffices ⨆ b, cond b V W = ⊤ from (hV.decomposition this).isInternal _
      (sup_eq_iSup V W).symm.trans Submodule.sup_orthogonal_of_hasOrthogonalProjection
    let B (b : Bool) : OrthonormalBasis (cond b (Fin m) (Fin n)) 𝕜 ↥(cond b V W) := b.rec bW bV
    let bE : OrthonormalBasis (Σ b, cond b (Fin m) (Fin n)) 𝕜 E :=
      int.collectedOrthonormalBasis hV B
    let e := Equiv.finAddEquivSigmaCond
    let basis := bE.reindex e.symm
    {
      basis
      dim := m + n
      hdim := hn ▸ hdim.symm
      upperTriangular := fun i j (hji : j < i) => show toMatrixOrthonormal basis f i j = 0 from
        have hB : ∀ s, bE s = B s.1 s.2
          | ⟨true, i⟩ => show bE ⟨true, i⟩ = bV i from
            show (int.collectedBasis fun b => (B b).toBasis).toOrthonormalBasis _ ⟨true, i⟩ = bV i
            by simp only [Module.Basis.coe_toOrthonormalBasis, DirectSum.IsInternal.collectedBasis_coe,
              cond_true, B, V, W]; rfl
          | ⟨false, j⟩ => show bE ⟨false, j⟩ = bW j from
            show (int.collectedBasis fun b => (B b).toBasis).toOrthonormalBasis _ ⟨false, j⟩ = bW j
            by simp only [Module.Basis.coe_toOrthonormalBasis, DirectSum.IsInternal.collectedBasis_coe,
              cond_false, B, V, W]; rfl
        have hf {bi i' bj j'} (hi : e i = ⟨bi, i'⟩) (hj : e j = ⟨bj, j'⟩) :=
          calc toMatrixOrthonormal basis f i j
            _ = toMatrixOrthonormal bE f (e i) (e j) := by
              rw [f.toMatrixOrthonormal_reindex]
              rfl
            _ = ⟪bE (e i), f (bE (e j))⟫_𝕜 := f.toMatrixOrthonormal_apply_apply ..
            _ = ⟪(B bi i' : E), f (B bj j')⟫_𝕜 := by rw [hB, hB, hi, hj]

        if hj : j < m then
          let j' : Fin m := ⟨j, hj⟩
          have hf' {bi i'} (hi : e i = ⟨bi, i'⟩) (h0 : ⟪(B bi i' : E), bV j'⟫_𝕜 = 0) :=
            calc toMatrixOrthonormal basis f i j
              _ = ⟪(B bi i' : E), f _⟫_𝕜 := hf hi (Equiv.finAddEquivSigmaCond_true hj)
              _ = ⟪_, f (bV j')⟫_𝕜 := rfl
              _ = 0 :=
                suffices f (bV j') = μ.val • bV j' by rw [this, inner_smul_right, h0, mul_zero]
                suffices f.HasEigenvector μ (bV j') from this.apply_eq_smul
                ⟨(bV j').property, fun h => bV.toBasis.ne_zero j' (Subtype.ext h)⟩

          if hi : i < m then
            let i' : Fin m := ⟨i, hi⟩
            suffices ⟪(bV i' : E), bV j'⟫_𝕜 = 0 from hf' (Equiv.finAddEquivSigmaCond_true hi) this
            bV.orthonormal.right (Fin.ne_of_gt hji)
          else
            let i' : Fin n := i.subNat' hi
            suffices ⟪(bW i' : E), bV j'⟫_𝕜 = 0 from hf' (Equiv.finAddEquivSigmaCond_false hi) this
            V.inner_left_of_mem_orthogonal (bV j').property (bW i').property
        else
          have hi (h : i < m) : False := hj (Nat.lt_trans hji h)
          let i' : Fin n := i.subNat' hi
          let j' : Fin n := j.subNat' hj
          calc toMatrixOrthonormal basis f i j
            _ = ⟪(bW i' : E), f (bW j')⟫_𝕜 :=
              hf (Equiv.finAddEquivSigmaCond_false hi) (Equiv.finAddEquivSigmaCond_false hj)
            _ = ⟪bW i', g (bW j')⟫_𝕜 := by
              rw [coe_comp, ContinuousLinearMap.coe_coe, Function.comp_apply, domRestrict_apply,
                Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
            _ = toMatrixOrthonormal bW g i' j' := (g.toMatrixOrthonormal_apply_apply ..).symm
            _ = 0 := hg (Nat.sub_lt_sub_right (Nat.le_of_not_lt hj) hji)
    }
  else
    haveI : Subsingleton E := not_nontrivial_iff_subsingleton.mp hE
    {
      dim := 0
      hdim := Module.finrank_zero_of_subsingleton
      basis := (Module.Basis.empty E).toOrthonormalBasis ⟨nofun, nofun⟩
      upperTriangular := nofun
    }
termination_by Module.finrank 𝕜 E
decreasing_by exact
  calc Module.finrank 𝕜 W
    _ < m + Module.finrank 𝕜 W :=
      suffices 0 < m from Nat.lt_add_of_pos_left this
      Submodule.one_le_finrank_iff.mpr μ.property
    _ = Module.finrank 𝕜 E := hdim

end LinearMap

namespace Matrix

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [LinearOrder n] [RCLike 𝕜] [IsAlgClosed 𝕜]
  (A : Matrix n n 𝕜)

/-- This is `LinearMap.SchurTriangulationAux` adapted for matrices in the
Euclidean space. -/
noncomputable def schurTriangulationAux :
    OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n) × UpperTriangular n 𝕜 :=
  let f := toEuclideanLin A
  let ⟨d, hd, b, hut⟩ := LinearMap.SchurTriangulationAux.of f
  let e : Fin d ≃o n := Fintype.orderIsoFinOfCardEq n (finrank_euclideanSpace.symm.trans hd)
  let b' := b.reindex e
  let B := LinearMap.toMatrixOrthonormal b' f
  suffices B.IsUpperTriangular from ⟨b', B, this⟩
  fun i j (hji : j < i) =>
    calc LinearMap.toMatrixOrthonormal b' f i j
      _ = LinearMap.toMatrixOrthonormal b f (e.symm i) (e.symm j) := by
        rw [f.toMatrixOrthonormal_reindex]
        rfl
      _ = 0 := hut (e.symm.lt_iff_lt.mpr hji)

/-- The change of basis that induces the upper triangular form `A.schurTriangulation` of a matrix
`A` over an algebraically closed field. -/
noncomputable def schurTriangulationBasis : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n) :=
  (schurTriangulationAux A).1

/-- The unitary matrix that induces the upper triangular form `A.schurTriangulation` to which a
matrix `A` over an algebraically closed field is unitarily similar. -/
noncomputable def schurTriangulationUnitary : unitaryGroup n 𝕜 where
  val := (EuclideanSpace.basisFun n 𝕜).toBasis.toMatrix (schurTriangulationBasis A)
  property := OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary ..

/-- The upper triangular form induced by `A.schurTriangulationUnitary` to which a matrix `A` over an
algebraically closed field is unitarily similar. -/
noncomputable def schurTriangulation : UpperTriangular n 𝕜 :=
  (schurTriangulationAux A).2

/-- **Schur triangulation**, **Schur decomposition** for matrices over an algebraically closed
field. In particular, a complex matrix can be converted to upper-triangular form by a change of
basis. In other words, any complex matrix is unitarily similar to an upper triangular matrix. -/
lemma schur_triangulation :
    A = schurTriangulationUnitary A * schurTriangulation A * star (schurTriangulationUnitary A) :=
  let U := schurTriangulationUnitary A
  have h : (U : Matrix n n 𝕜) * (schurTriangulation A).val = A * U :=
    let b := (schurTriangulationBasis A).toBasis
    let c := (EuclideanSpace.basisFun n 𝕜).toBasis
    calc c.toMatrix b * LinearMap.toMatrix b b (toEuclideanLin A)
      _ = LinearMap.toMatrix c c (toEuclideanLin A) * c.toMatrix b := by simp
      _ = LinearMap.toMatrix c c (toLin c c A) * U := rfl
      _ = A * U := by simp
  calc A
    _ = A * U * star (U : Matrix n n 𝕜) := by simp [mul_assoc]
    _ = U * schurTriangulation A * star (U : Matrix n n 𝕜) := by rw [← h]

end Matrix
