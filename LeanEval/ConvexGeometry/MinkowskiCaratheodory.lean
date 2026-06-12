import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Topology.Order.IntermediateValue
import EvalTools.Markers

namespace LeanEval
namespace ConvexGeometry

open Set

/-!
Minkowski-Carathéodory theorem in finite-dimensional real normed spaces.

This file formalizes the blueprint `minkowski-caratheodory-theorem`. The main result
(`mem_convexHull_finset_extremePoints_of_mem_compact_convex`) packages the theorem as a
finite extreme-point representation for each point of a compact convex set, with the
expected `finrank + 1` bound on the number of points used.

The proof combines a cardinality-bounded form of Carathéodory's theorem with Minkowski's
theorem (the finite-dimensional Krein–Milman theorem). The supporting lemmas are stated
faithfully to the blueprint; many of the "direction subspace" lemmas carry the explicit
shared context (a base point `p ∈ s`, the direction subspace `W = vectorSpan ℝ s`, and the
translated set `s' = {w ∈ W | w + p ∈ s}`).
-/

universe u

/-! ### Carathéodory with a dimension bound -/

/-- **Carathéodory representation lands in the convex hull of a finite image.**
From `x ∈ convexHull ℝ A` we obtain a finite affinely independent family `z` with strictly
positive weights summing to `1` representing `x`, whose image finset `t` lies in `A` and has
`x` in its convex hull. -/
theorem caratheodory_image_mem.{v} {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : Set E} {x : E} (hx : x ∈ convexHull ℝ A) :
    ∃ (ι : Type v) (_ : Fintype ι) (z : ι → E) (w : ι → ℝ) (t : Finset E),
      Set.range z ⊆ A ∧ AffineIndependent ℝ z ∧ (∀ i, 0 < w i) ∧
      ∑ i, w i = 1 ∧ ∑ i, w i • z i = x ∧
      (↑t : Set E) = Set.range z ∧ (↑t : Set E) ⊆ A ∧
      x ∈ convexHull ℝ (↑t : Set E) := by
  classical
    -- Apply the explicit Carathéodory representation lemma
    have hrep := eq_pos_convex_span_of_mem_convexHull hx
    rcases hrep with ⟨ι, hfι, z, w, hrange, haff, hpos, hsum, hx_eq⟩
    -- Construct t as the image finset of z
    let t : Finset E := Finset.image z (Finset.univ : Finset ι)
    -- The set underlying t equals the range of z
    have htrange : (t : Set E) = Set.range z := by
      ext y
      constructor
      · intro hy
        rcases Finset.mem_image.1 hy with ⟨i, _, rfl⟩
        exact ⟨i, rfl⟩
      · intro hy
        rcases hy with ⟨i, rfl⟩
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    -- Since range z ⊆ A, we also have (t : Set E) ⊆ A
    have htA : (t : Set E) ⊆ A := by
      rw [htrange]
      exact hrange
    -- Show x ∈ convexHull ℝ (Set.range z) using Finset.centerMass_mem_convexHull
    have hx_mem : x ∈ convexHull ℝ (Set.range z) := by
      have hpos' : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ w i :=
        λ i _ => le_of_lt (hpos i)
      have hsumpos : 0 < ∑ i ∈ (Finset.univ : Finset ι), w i := by
        rw [hsum]
        norm_num
      have hz_range : ∀ i ∈ (Finset.univ : Finset ι), z i ∈ Set.range z :=
        λ i _ => ⟨i, rfl⟩
      have hcm := Finset.centerMass_mem_convexHull (Finset.univ : Finset ι) hpos' hsumpos hz_range
      -- hcm : (Finset.univ : Finset ι).centerMass w z ∈ convexHull ℝ (Set.range z)
      -- But this centerMass equals x
      have hcenter_eq : (Finset.univ : Finset ι).centerMass w z = x := by
        calc
          (Finset.univ : Finset ι).centerMass w z
              = (∑ i ∈ (Finset.univ : Finset ι), w i)⁻¹ • ∑ i ∈ (Finset.univ : Finset ι), w i • z i := rfl
          _ = (∑ i, w i)⁻¹ • ∑ i, w i • z i := rfl
          _ = (1 : ℝ)⁻¹ • x := by rw [hsum, hx_eq]
          _ = x := by norm_num
      simpa [hcenter_eq] using hcm
    refine ⟨ι, hfι, z, w, t, hrange, haff, hpos, hsum, hx_eq, htrange, htA, ?_⟩
    rw [htrange]
    exact hx_mem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Carathéodory cardinality estimate.** With `z` affinely independent and `t` its image
finset, `#t ≤ #ι ≤ finrank ℝ E + 1`. -/
theorem caratheodory_card_bound [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] {z : ι → E}
    {t : Finset E} (hz : AffineIndependent ℝ z) (ht : (↑t : Set E) = Set.range z) :
    t.card ≤ Fintype.card ι ∧ Fintype.card ι ≤ Module.finrank ℝ E + 1 := by
  classical
    have ht_image : t = Finset.image z Finset.univ := by
      ext x
      constructor
      · intro hx
        have : x ∈ Set.range z := by
          rw [← ht]
          exact hx
        rcases this with ⟨i, hi⟩
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
      · intro hx
        rcases Finset.mem_image.mp hx with ⟨i, _, hi⟩
        have : x ∈ (t : Set E) := by
          rw [ht]
          exact ⟨i, hi⟩
        exact this
    have h_card_t : t.card ≤ Fintype.card ι := by
      calc
        t.card = (Finset.image z Finset.univ).card := by rw [ht_image]
        _ ≤ (Finset.univ : Finset ι).card := Finset.card_image_le
        _ = Fintype.card ι := by simp
    have h_card_ι : Fintype.card ι ≤ Module.finrank ℝ E + 1 := by
      have h_affine : Fintype.card ι ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range z)) + 1 :=
        hz.card_le_finrank_succ
      have h_finrank : Module.finrank ℝ (vectorSpan ℝ (Set.range z)) ≤ Module.finrank ℝ E :=
        Submodule.finrank_le (vectorSpan ℝ (Set.range z))
      linarith
    exact And.intro h_card_t h_card_ι

/-- **Carathéodory cardinality bound.** Every point of `convexHull ℝ A` lies in the convex
hull of a finite subset `t ⊆ A` with at most `finrank ℝ E + 1` points. -/
theorem caratheodory_card [FiniteDimensional ℝ E] {A : Set E} {x : E}
    (hx : x ∈ convexHull ℝ A) :
    ∃ t : Finset E, (↑t : Set E) ⊆ A ∧ t.card ≤ Module.finrank ℝ E + 1 ∧
      x ∈ convexHull ℝ (↑t : Set E) := by
  rcases caratheodory_image_mem hx with ⟨ι, hfi, z, w, t, _, hz, _, _, _, ht_range, ht_sub, hx_t⟩
  haveI : Fintype ι := hfi
  rcases caratheodory_card_bound hz ht_range with ⟨hcard1, hcard2⟩
  refine ⟨t, ht_sub, ?_, hx_t⟩
  exact le_trans hcard1 hcard2

/-! ### Building blocks for Minkowski's theorem -/

/-- **Maximal face of a linear functional.** The face of `s` on which the continuous linear
functional `ℓ` attains its maximum, i.e. the exposed subset determined by `ℓ`. -/
def exposedFace (ℓ : E →L[ℝ] ℝ) (s : Set E) : Set E := {y | y ∈ s ∧ ∀ z ∈ s, ℓ z ≤ ℓ y}

/-- **The maximal face is an extreme subset.** `exposedFace ℓ s` is compact and convex, and its
extreme points are extreme points of `s`. -/
theorem exposedFace_isExtreme {s : Set E} (hscomp : IsCompact s) (hsconv : Convex ℝ s)
    (ℓ : E →L[ℝ] ℝ) :
    IsCompact (exposedFace ℓ s) ∧ Convex ℝ (exposedFace ℓ s) ∧
      (exposedFace ℓ s).extremePoints ℝ ⊆ s.extremePoints ℝ := by
  have hExp : IsExposed ℝ s (exposedFace ℓ s) := by
    intro hne
    refine ⟨ℓ, ?_⟩
    ext x
    simp [exposedFace, Set.mem_setOf_eq]
  have hExtreme : IsExtreme ℝ s (exposedFace ℓ s) := hExp.isExtreme
  have hExtremePointsSubset : (exposedFace ℓ s).extremePoints ℝ ⊆ s.extremePoints ℝ :=
    hExtreme.extremePoints_subset_extremePoints
  have hCompact : IsCompact (exposedFace ℓ s) := hExp.isCompact hscomp
  have hConvex : Convex ℝ (exposedFace ℓ s) := hExp.convex hsconv
  exact ⟨hCompact, hConvex, hExtremePointsSubset⟩

/-- **The maximal face lies in the kernel of `ℓ`.** Every difference of two points of
`exposedFace ℓ s` is annihilated by `ℓ`. -/
theorem exposedFace_vectorSpan_le_ker {s : Set E} (ℓ : E →L[ℝ] ℝ) :
    vectorSpan ℝ (exposedFace ℓ s) ≤ LinearMap.ker (ℓ : E →ₗ[ℝ] ℝ) := by
  rw [vectorSpan, Submodule.span_le]
  intro v hv
  rcases Set.mem_vsub.mp hv with ⟨y, hy, y', hy', rfl⟩
  have hy_val_eq : ℓ y = ℓ y' := le_antisymm (hy'.2 y hy.1) (hy.2 y' hy'.1)
  have hy_ker : y - y' ∈ LinearMap.ker (ℓ : E →ₗ[ℝ] ℝ) := by
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
    simpa [ContinuousLinearMap.coe_coe] using hy_val_eq
  simpa [vsub_eq_sub] using hy_ker

/-- **The maximal face has smaller affine dimension.** If `ℓ` is non-constant on `s`, then the
affine dimension of `exposedFace ℓ s` is strictly smaller than that of `s`. -/
theorem exposedFace_finrank_lt [FiniteDimensional ℝ E] {s : Set E} (ℓ : E →L[ℝ] ℝ)
    {a b : E} (ha : a ∈ s) (hb : b ∈ s) (hab : ℓ a ≠ ℓ b) :
    Module.finrank ℝ (vectorSpan ℝ (exposedFace ℓ s)) <
      Module.finrank ℝ (vectorSpan ℝ s) := by
  set U := vectorSpan ℝ (exposedFace ℓ s) with hU
  set V := vectorSpan ℝ s with hV
  set K := LinearMap.ker (ℓ : E →ₗ[ℝ] ℝ) with hK
  have hsub : exposedFace ℓ s ⊆ s := by
    intro x hx
    exact hx.1
  have hUV : U ≤ V := vectorSpan_mono (k := ℝ) (s₁ := exposedFace ℓ s) (s₂ := s) hsub
  have hUK : U ≤ K := exposedFace_vectorSpan_le_ker ℓ
  have habV : a - b ∈ V := vsub_mem_vectorSpan (k := ℝ) (s := s) (p₁ := a) (p₂ := b) ha hb
  have hab_notU : a - b ∉ U := by
    intro h
    have : a - b ∈ K := hUK h
    have hℓab : ℓ (a - b) = 0 := this
    have h_eq : ℓ a = ℓ b := by
      calc
        ℓ a = ℓ (a - b + b) := by simp
        _ = ℓ (a - b) + ℓ b := by rw [map_add ℓ (a - b) b]
        _ = 0 + ℓ b := by rw [hℓab]
        _ = ℓ b := by simp
    exact hab h_eq
  have hU_lt_V : U < V := by
    refine lt_of_le_of_ne hUV ?_
    intro h_eq
    apply hab_notU
    rw [h_eq]
    exact habV
  exact Submodule.finrank_lt_finrank_of_lt hU_lt_V

/-- **The translated set is convex.** For a subspace `W` and a base point `p`, the translated
copy `{w ∈ W | w + p ∈ s}` of `s` inside `W` is convex. -/
theorem translatedSet_convex {s : Set E} (hsconv : Convex ℝ s) (W : Submodule ℝ E) (p : E) :
    Convex ℝ {w : W | (w : E) + p ∈ s} := by
  -- The map w ↦ (w : E) + p is affine; use Convex.affine_preimage
  let f : W →ᵃ[ℝ] E :=
    { toFun := fun w => (w : E) + p
      linear := (Submodule.subtype W : W →ₗ[ℝ] E)
      map_vadd' := by
        intro x v
        simp [add_assoc]
    }
  have h := hsconv.affine_preimage f
  simpa [Set.preimage, Set.mem_setOf_eq] using h

/-- **The translation recovers `s`.** For `p ∈ s` and `W = vectorSpan ℝ s`, the image of the
translated set `{w : W | (w : E) + p ∈ s}` under `w ↦ (w : E) + p` is `s` itself. -/
theorem image_translatedSet_eq {s : Set E} {p : E} (hp : p ∈ s) :
    (fun w : (vectorSpan ℝ s) => (w : E) + p) '' {w : (vectorSpan ℝ s) | (w : E) + p ∈ s} = s := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨w, hw, rfl⟩
    exact hw
  · intro hz
    have hzW : z - p ∈ vectorSpan ℝ s := by
      simpa [vsub_eq_sub] using vsub_mem_vectorSpan (k := ℝ) hz hp
    refine ⟨⟨z - p, hzW⟩, ?_, ?_⟩
    · simp [hz]
    · simp

/-- **The translated set spans its subspace.** For `p ∈ s`, the translated set
`{w : W | (w : E) + p ∈ s}` has full affine span in `W = vectorSpan ℝ s`. -/
theorem affineSpan_translatedSet_eq_top {s : Set E} {p : E} (hp : p ∈ s) :
    affineSpan ℝ {w : (vectorSpan ℝ s) | (w : E) + p ∈ s} = ⊤ := by
  set W := vectorSpan ℝ s with hW
  set s' : Set W := {w : W | (w : E) + p ∈ s} with hs'
  have h_nonempty : s'.Nonempty := by
    refine ⟨0, ?_⟩
    dsimp [s']
    simp [hp]
  have h_vec_eq_top : vectorSpan ℝ s' = ⊤ := by
    have h_inj : Function.Injective (Submodule.map (W.subtype : W →ₗ[ℝ] E)) :=
      Submodule.map_injective_of_injective (Submodule.subtype_injective W)
    apply h_inj
    calc
      Submodule.map W.subtype (vectorSpan ℝ s') = Submodule.map W.subtype (Submodule.span ℝ (s' -ᵥ s')) := by
        rw [vectorSpan]
      _ = Submodule.span ℝ (W.subtype '' (s' -ᵥ s' : Set W)) := by rw [Submodule.map_span]
      _ = Submodule.span ℝ (s -ᵥ s : Set E) := by
        apply congrArg (Submodule.span ℝ)
        ext x
        constructor
        · intro hx
          rw [Set.mem_image] at hx
          rcases hx with ⟨y, hy, rfl⟩
          rw [Set.mem_vsub] at hy
          rcases hy with ⟨w₁, hw₁, w₂, hw₂, hy_eq⟩
          have hw₁_s' : (w₁ : E) + p ∈ s := by simpa [s'] using hw₁
          have hw₂_s' : (w₂ : E) + p ∈ s := by simpa [s'] using hw₂
          have hy_val_eq : W.subtype y = ((w₁ : E) + p) - ((w₂ : E) + p) := by
            calc
              W.subtype y = W.subtype (w₁ -ᵥ w₂) := by rw [hy_eq]
              _ = (W.subtype (w₁ - w₂) : E) := by simp
              _ = (w₁ : E) - (w₂ : E) := rfl
              _ = ((w₁ : E) + p) - ((w₂ : E) + p) := by simp
          rw [hy_val_eq]
          exact vsub_mem_vsub hw₁_s' hw₂_s'
        · intro hx
          rw [Set.mem_vsub] at hx
          rcases hx with ⟨a, ha, b, hb, hx_eq⟩
          have h_image : (fun w : W => (w : E) + p) '' s' = s := image_translatedSet_eq hp
          have ha' : a ∈ (fun w : W => (w : E) + p) '' s' := by
            rw [h_image]
            exact ha
          have hb' : b ∈ (fun w : W => (w : E) + p) '' s' := by
            rw [h_image]
            exact hb
          rcases ha' with ⟨w₁, hw₁, ha_eq⟩
          rcases hb' with ⟨w₂, hw₂, hb_eq⟩
          have hz_mem : w₁ - w₂ ∈ (s' -ᵥ s' : Set W) := by
            rw [Set.mem_vsub]
            refine ⟨w₁, hw₁, w₂, hw₂, ?_⟩
            simp
          refine ⟨w₁ - w₂, hz_mem, ?_⟩
          calc
            W.subtype (w₁ - w₂) = (w₁ : E) - (w₂ : E) := rfl
            _ = ((w₁ : E) + p) - ((w₂ : E) + p) := by simp
            _ = a - b := by simp [ha_eq, hb_eq]
            _ = x := hx_eq
      _ = vectorSpan ℝ s := by rw [vectorSpan]
      _ = W := rfl
      _ = Submodule.map W.subtype (⊤ : Submodule ℝ W) := by rw [Submodule.map_subtype_top]
  exact (AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty (k := ℝ) (V := W) (P := W) h_nonempty).mpr h_vec_eq_top

/-- **Intrinsic interior equals interior under full affine span.** If a set `u` of a real normed
space has `affineSpan ℝ u = ⊤`, then its intrinsic interior is its topological interior. -/
theorem intrinsicInterior_eq_interior_of_affineSpan_eq_top {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {u : Set F} (hu : affineSpan ℝ u = ⊤) :
    intrinsicInterior ℝ u = interior u := by
  set A' : Set F := (affineSpan ℝ u : Set F) with hA'
  set π : A' → F := Subtype.val with hπ
  apply Set.Subset.antisymm
  · -- intrinsicInterior ℝ u ⊆ interior u
    intro x hx
    rcases (mem_intrinsicInterior (𝕜 := ℝ)).mp hx with ⟨y, hy, hyx⟩
    have hA_open : IsOpen ((affineSpan ℝ u : Set F)) := by
      have : (affineSpan ℝ u : Set F) = Set.univ := by
        simp [hu]
      rw [this]
      exact isOpen_univ
    have h_open_map : IsOpenMap π :=
      hA_open.isOpenMap_subtype_val
    have h_image_sub : π '' interior (π ⁻¹' u) ⊆ interior u := by
      calc
        π '' interior (π ⁻¹' u) ⊆ interior (π '' (π ⁻¹' u)) :=
          h_open_map.image_interior_subset (π ⁻¹' u)
        _ ⊆ interior u := interior_mono (Set.image_preimage_subset π u)
    have hx_image : x ∈ π '' interior (π ⁻¹' u) := by
      refine ⟨y, hy, hyx⟩
    exact h_image_sub hx_image
  · -- interior u ⊆ intrinsicInterior ℝ u
    exact interior_subset_intrinsicInterior

/-- **Intrinsic interior via the direction subspace.** With `W = vectorSpan ℝ s` and base point
`p ∈ s`, the intrinsic interior of `s` is the image of the topological interior of the
translated set under `w ↦ w + p`. -/
theorem intrinsicInterior_eq_image {s : Set E} {p : E} (hp : p ∈ s) :
    intrinsicInterior ℝ s =
      (fun w : (vectorSpan ℝ s) => (w : E) + p) ''
        interior {w : (vectorSpan ℝ s) | (w : E) + p ∈ s} := by
  set W := vectorSpan ℝ s with hW
  set s' : Set W := {w : W | (w : E) + p ∈ s} with hs'
  -- Build the affine isometry φ : W →ᵃⁱ[ℝ] E, φ w = (w : E) + p
  let φ : W →ᵃⁱ[ℝ] E :=
    (AffineIsometryEquiv.vaddConst ℝ p).toAffineIsometry.comp
      (W.subtypeₗᵢ).toAffineIsometry
  have hφ : ∀ w : W, φ w = (w : E) + p := by
    intro w
    calc
      φ w = ((AffineIsometryEquiv.vaddConst ℝ p).toAffineIsometry) (((W.subtypeₗᵢ).toAffineIsometry) w) := rfl
      _ = (AffineIsometryEquiv.vaddConst ℝ p) ((W.subtypeₗᵢ) w) := rfl
      _ = (AffineIsometryEquiv.vaddConst ℝ p) (w : E) := rfl
      _ = (w : E) +ᵥ p := by rw [AffineIsometryEquiv.coe_vaddConst]
      _ = (w : E) + p := rfl
  -- Step 1: φ '' s' = s  (via the pre-proved lemma)
  have h_image : φ '' s' = s := by
    calc
      φ '' s' = ((fun w : W => (w : E) + p) '' s') := by
        refine Set.image_congr ?_
        intro w hw
        rw [hφ w]
      _ = s := image_translatedSet_eq hp
  -- Step 2: intrinsicInterior ℝ s = φ '' intrinsicInterior ℝ s'
  have h_intrinsic_image : intrinsicInterior ℝ s = φ '' intrinsicInterior ℝ s' := by
    calc
      intrinsicInterior ℝ s = intrinsicInterior ℝ (φ '' s') := by rw [h_image]
      _ = φ '' intrinsicInterior ℝ s' := by rw [AffineIsometry.image_intrinsicInterior]
  -- Step 3: intrinsicInterior ℝ s' = interior s'
  have h_intrinsic_s' : intrinsicInterior ℝ s' = interior s' :=
    intrinsicInterior_eq_interior_of_affineSpan_eq_top (affineSpan_translatedSet_eq_top hp)
  -- Step 4: combine
  calc
    intrinsicInterior ℝ s = φ '' intrinsicInterior ℝ s' := h_intrinsic_image
    _ = φ '' interior s' := by rw [h_intrinsic_s']
    _ = ((fun w : W => (w : E) + p) '' interior s') := by
      refine Set.image_congr ?_
      intro w hw
      rw [hφ w]
    _ = (fun w : W => (w : E) + p) '' interior {w : W | (w : E) + p ∈ s} := rfl

/-- **The interior in the direction subspace is nonempty.** If `s` is nonempty (and convex),
the topological interior of the translated set in `W = vectorSpan ℝ s` is nonempty. -/
theorem interior_translatedSet_nonempty [FiniteDimensional ℝ E] {s : Set E} (hsconv : Convex ℝ s)
    (hne : s.Nonempty) {p : E} (hp : p ∈ s) :
    (interior {w : (vectorSpan ℝ s) | (w : E) + p ∈ s}).Nonempty := by
  have h_int_nonempty : (intrinsicInterior ℝ s).Nonempty :=
    (intrinsicInterior_nonempty hsconv).mpr hne
  have h_image_nonempty : ((fun w : (vectorSpan ℝ s) => (w : E) + p) ''
    interior {w : (vectorSpan ℝ s) | (w : E) + p ∈ s}).Nonempty := by
    rw [← intrinsicInterior_eq_image hp]
    exact h_int_nonempty
  exact Set.image_nonempty.mp h_image_nonempty

/-- **Separation in the direction subspace.** A relative boundary point `y` of `s` translates to
`y - p` which is not in the interior of the translated set, and is strictly separated from it by
a continuous linear functional `g` on `W = vectorSpan ℝ s`. -/
theorem separation_in_direction {s : Set E} (hsconv : Convex ℝ s) {p : E} (hp : p ∈ s)
    {y : E} (hy : y ∈ s) (hynotin : y ∉ intrinsicInterior ℝ s)
    (hyW : y - p ∈ vectorSpan ℝ s) :
    (⟨y - p, hyW⟩ : (vectorSpan ℝ s)) ∉ interior {w : (vectorSpan ℝ s) | (w : E) + p ∈ s} ∧
      ∃ g : (vectorSpan ℝ s) →L[ℝ] ℝ,
        ∀ w ∈ interior {w : (vectorSpan ℝ s) | (w : E) + p ∈ s}, g w < g ⟨y - p, hyW⟩ := by
  set W := vectorSpan ℝ s with hW
  set T := interior {w : W | (w : E) + p ∈ s} with hT
  have h_not_mem : (⟨y - p, hyW⟩ : W) ∉ T := by
    intro h_mem
    have h_y_image : y ∈ (fun w : W => (w : E) + p) '' T := by
      refine ⟨⟨y - p, hyW⟩, h_mem, ?_⟩
      simp
    have h_intrinsic : y ∈ intrinsicInterior ℝ s := by
      rw [intrinsicInterior_eq_image hp]
      exact h_y_image
    exact hynotin h_intrinsic
  have h_convex : Convex ℝ T := by
    have h_conv_set : Convex ℝ {w : W | (w : E) + p ∈ s} :=
      translatedSet_convex hsconv W p
    exact h_conv_set.interior
  have h_open : IsOpen T := isOpen_interior
  rcases geometric_hahn_banach_open_point h_convex h_open h_not_mem with ⟨g, hg⟩
  refine ⟨h_not_mem, g, ?_⟩
  intro w hw
  exact hg w hw

/-- **Extension of the separating functional to `E`.** The separating functional `g` on
`W = vectorSpan ℝ s` extends to a continuous linear functional `ℓ` on `E` restricting to `g`,
and every `z ∈ s` with `z - p` in the interior of the translated set satisfies `ℓ z < ℓ y`. -/
theorem extension_to_E {s : Set E} {p : E} {y : E} (hyW : y - p ∈ vectorSpan ℝ s)
    (g : (vectorSpan ℝ s) →L[ℝ] ℝ)
    (hsep : ∀ w ∈ interior {w : (vectorSpan ℝ s) | (w : E) + p ∈ s}, g w < g ⟨y - p, hyW⟩) :
    ∃ ℓ : E →L[ℝ] ℝ,
      (∀ w : (vectorSpan ℝ s), ℓ (w : E) = g w) ∧
      ∀ z ∈ s, ∀ hzW : z - p ∈ vectorSpan ℝ s,
        (⟨z - p, hzW⟩ : (vectorSpan ℝ s)) ∈ interior {w : (vectorSpan ℝ s) | (w : E) + p ∈ s} →
          ℓ z < ℓ y := by
  -- Use the Hahn-Banach theorem to extend g from W = vectorSpan ℝ s to all of E
  rcases Real.exists_extension_norm_eq (vectorSpan ℝ s) g with ⟨ℓ, hℓ⟩
  refine ⟨ℓ, ?_, ?_⟩
  · -- ℓ restricts to g on W
    exact hℓ.1
  · intro z hz hzW hint
    have hg_lt : g ⟨z - p, hzW⟩ < g ⟨y - p, hyW⟩ := hsep _ hint
    have hℓ_zp : ℓ (z - p) = g ⟨z - p, hzW⟩ := by
      rw [hℓ.1 ⟨z - p, hzW⟩]
    have hℓ_yp : ℓ (y - p) = g ⟨y - p, hyW⟩ := by
      rw [hℓ.1 ⟨y - p, hyW⟩]
    have h_lt : ℓ (z - p) < ℓ (y - p) := by
      rw [hℓ_zp, hℓ_yp]
      exact hg_lt
    calc
      ℓ z = ℓ ((z - p) + p) := by simp [sub_add_cancel]
      _ = ℓ (z - p) + ℓ p := by exact ℓ.map_add (z - p) p
      _ < ℓ (y - p) + ℓ p := by nlinarith
      _ = ℓ ((y - p) + p) := by simp [sub_add_cancel]
      _ = ℓ y := by simp [sub_add_cancel]

/-- **The bound passes to all of `s`.** If the strict bound `ℓ z < ℓ y` holds for all `z ∈ s`
with `z - p` in the interior of the translated set, then `ℓ z ≤ ℓ y` for all `z ∈ s`. -/
theorem bound_passes_to_closure [FiniteDimensional ℝ E] {s : Set E} (hsconv : Convex ℝ s)
    (hne : s.Nonempty) {p : E} (hp : p ∈ s) {y : E} (ℓ : E →L[ℝ] ℝ)
    (hstrict : ∀ z ∈ s, ∀ hzW : z - p ∈ vectorSpan ℝ s,
      (⟨z - p, hzW⟩ : (vectorSpan ℝ s)) ∈ interior {w : (vectorSpan ℝ s) | (w : E) + p ∈ s} →
        ℓ z < ℓ y) :
    ∀ z ∈ s, ℓ z ≤ ℓ y := by
  intro z hz
  set W := vectorSpan ℝ s with hW
  set s' : Set W := {w : W | (w : E) + p ∈ s} with hs'
  have hzW : z - p ∈ W := by
    simpa using vsub_mem_vectorSpan (k := ℝ) hz hp
  let w₀ : W := ⟨z - p, hzW⟩
  have hw₀_s' : w₀ ∈ s' := by
    dsimp [s', w₀]
    simp [hz]
  have hconv_s' : Convex ℝ s' := translatedSet_convex hsconv W p
  have h_nonempty_int : (interior s').Nonempty :=
    interior_translatedSet_nonempty hsconv hne hp
  have h_closure_eq : closure (interior s') = closure s' :=
    hconv_s'.closure_interior_eq_closure_of_nonempty_interior h_nonempty_int
  have hw₀_closure_int : w₀ ∈ closure (interior s') := by
    have hw₀_closure_s' : w₀ ∈ closure s' := subset_closure hw₀_s'
    rw [h_closure_eq]
    exact hw₀_closure_s'
  -- Define F : W → ℝ by F w = ℓ ((w : E) + p) - ℓ y
  let F : W → ℝ := fun w => ℓ ((w : E) + p) - ℓ y
  have hF_cont : ContinuousOn F (closure (interior s')) := by
    have hF_cont_global : Continuous F := by
      refine Continuous.sub ?_ (continuous_const : Continuous fun _ => ℓ y)
      refine ℓ.continuous.comp ?_
      refine Continuous.add ?_ continuous_const
      exact continuous_subtype_val
    exact hF_cont_global.continuousOn
  have h_nonpos_on_int : ∀ w ∈ interior s', F w ≤ 0 := by
    intro w hw
    have hw_s' : w ∈ s' := interior_subset hw
    have hz' : (w : E) + p ∈ s := hw_s'
    have hz'W : ((w : E) + p) - p ∈ W := by
      simpa [add_sub_cancel_right] using w.2
    have hw_interior : (⟨((w : E) + p) - p, hz'W⟩ : W) ∈ interior s' := by
      have h_eq : (⟨((w : E) + p) - p, hz'W⟩ : W) = w := Subtype.ext (by simp)
      simpa [h_eq] using hw
    have h_lt : ℓ ((w : E) + p) < ℓ y := hstrict ((w : E) + p) hz' hz'W hw_interior
    dsimp [F]
    linarith
  have h_nonpos_at_w₀ : F w₀ ≤ 0 :=
    le_on_closure h_nonpos_on_int hF_cont
      (by
        -- The constant zero function is continuous on any subset
        exact continuousOn_const)
      hw₀_closure_int
  -- From F w₀ ≤ 0 we deduce ℓ z ≤ ℓ y
  dsimp [F, w₀] at h_nonpos_at_w₀
  have : ℓ z - ℓ y ≤ 0 := by
    -- (w₀ : E) = z - p, so ℓ ((w₀ : E) + p) = ℓ ((z - p) + p) = ℓ z
    simpa [sub_add_cancel] using h_nonpos_at_w₀
  linarith

/-- **The separating functional is non-constant on `s`.** Under the strict separation bound, the
functional `ℓ` takes two distinct values on `s`. -/
theorem functional_non_constant [FiniteDimensional ℝ E] {s : Set E} (hsconv : Convex ℝ s)
    (hne : s.Nonempty) {p : E} (hp : p ∈ s) {y : E} (hy : y ∈ s) (ℓ : E →L[ℝ] ℝ)
    (hstrict : ∀ z ∈ s, ∀ hzW : z - p ∈ vectorSpan ℝ s,
      (⟨z - p, hzW⟩ : (vectorSpan ℝ s)) ∈ interior {w : (vectorSpan ℝ s) | (w : E) + p ∈ s} →
        ℓ z < ℓ y) :
    ∃ a ∈ s, ∃ b ∈ s, ℓ a ≠ ℓ b := by
  have h_int_nonempty : (interior {w : (vectorSpan ℝ s) | (w : E) + p ∈ s}).Nonempty :=
    interior_translatedSet_nonempty hsconv hne hp
  rcases h_int_nonempty with ⟨w, hw⟩
  have hw_mem_set : (w : E) + p ∈ s := by
    have hw_mem_closure : w ∈ interior {w : (vectorSpan ℝ s) | (w : E) + p ∈ s} := hw
    have hw_mem_set' : w ∈ {w : (vectorSpan ℝ s) | (w : E) + p ∈ s} := interior_subset hw_mem_closure
    simpa using hw_mem_set'
  have hazW : ((w : E) + p) - p ∈ vectorSpan ℝ s := by
    simp
  have hw_interior : (⟨((w : E) + p) - p, hazW⟩ : (vectorSpan ℝ s)) ∈
    interior {w : (vectorSpan ℝ s) | (w : E) + p ∈ s} := by
    simpa using hw
  have h_lt : ℓ ((w : E) + p) < ℓ y :=
    hstrict ((w : E) + p) hw_mem_set hazW hw_interior
  refine ⟨(w : E) + p, hw_mem_set, y, hy, ?_⟩
  linarith

/-- **Supporting functional at a relative boundary point.** A point `y ∈ s` not in the intrinsic
interior of `s` admits a non-constant supporting functional `ℓ` with `ℓ z ≤ ℓ y` for all `z ∈ s`
(equivalently `y ∈ exposedFace ℓ s`). -/
theorem supporting_functional [FiniteDimensional ℝ E] {s : Set E} (hsconv : Convex ℝ s)
    (hne : s.Nonempty) {y : E} (hy : y ∈ s) (hynotin : y ∉ intrinsicInterior ℝ s) :
    ∃ ℓ : E →L[ℝ] ℝ, (∃ a ∈ s, ∃ b ∈ s, ℓ a ≠ ℓ b) ∧ ∀ z ∈ s, ℓ z ≤ ℓ y := by
  rcases hne with ⟨p, hp⟩
  have hne' : s.Nonempty := ⟨p, hp⟩
  have hyW : y - p ∈ vectorSpan ℝ s := by
    have hvsub := vsub_mem_vectorSpan (k := ℝ) hy hp
    simpa [vsub_eq_sub] using hvsub
  rcases separation_in_direction hsconv hp hy hynotin hyW with ⟨h_notin, g, hsep⟩
  rcases extension_to_E hyW g hsep with ⟨ℓ, hℓ_restrict, hstrict⟩
  have hbound : ∀ z ∈ s, ℓ z ≤ ℓ y :=
    bound_passes_to_closure hsconv hne' hp ℓ hstrict
  have h_nonconst : ∃ a ∈ s, ∃ b ∈ s, ℓ a ≠ ℓ b :=
    functional_non_constant hsconv hne' hp hy ℓ hstrict
  exact ⟨ℓ, h_nonconst, hbound⟩

/-- **A nonzero direction exists.** If the affine dimension of `s` is at least `1`, then
`vectorSpan ℝ s` contains a nonzero vector. -/
theorem exists_direction_vector {s : Set E} (h : 1 ≤ Module.finrank ℝ (vectorSpan ℝ s)) :
    ∃ v ∈ vectorSpan ℝ s, v ≠ 0 := by
  have hpos : 0 < Module.finrank ℝ (vectorSpan ℝ s) := by
    linarith
  haveI : Module.Finite ℝ (vectorSpan ℝ s) := Module.finite_of_finrank_pos hpos
  have h_nontriv : Nontrivial (vectorSpan ℝ s) :=
    (Module.finrank_pos_iff.mp hpos)
  have h_ne : ∃ (v : vectorSpan ℝ s), v ≠ 0 := exists_ne _
  rcases h_ne with ⟨v, hv⟩
  refine ⟨v.val, v.property, ?_⟩
  intro hzero
  apply hv
  exact Subtype.ext hzero

/-- **The line section is compact and convex.** For `x ∈ s` and a nonzero direction `v`, the
section `{t | x + t • v ∈ s}` is compact and convex. -/
theorem lineSection_isCompact_convex {s : Set E} (hscomp : IsCompact s) (hsconv : Convex ℝ s)
    {x : E} (hx : x ∈ s) {v : E} (hv : v ≠ 0) :
    IsCompact {t : ℝ | x + t • v ∈ s} ∧ Convex ℝ {t : ℝ | x + t • v ∈ s} := by
  set T := {t : ℝ | x + t • v ∈ s} with hT
  haveI : T2Space E := by infer_instance
  -- 1. Convexity: T is convex as the affine preimage of a convex set
  have hT_convex : Convex ℝ T := by
    let f : ℝ →ᵃ[ℝ] E :=
      { toFun := fun t : ℝ => x + t • v
        linear :=
          { toFun := fun t : ℝ => t • v
            map_add' := by intro a b; simp [add_smul]
            map_smul' := by intro r a; simp [smul_smul]
          }
        map_vadd' := by
          intro t u
          simp [add_smul, add_comm, add_assoc]
      }
    simpa [hT, Set.preimage, Set.mem_setOf_eq] using hsconv.affine_preimage f
  -- 2. Compactness: T is closed and bounded in ℝ, hence compact
  have hT_closed : IsClosed T := by
    have hs_closed : IsClosed s := hscomp.isClosed
    have h_cont : Continuous (fun (t : ℝ) => x + t • v) := by
      continuity
    simpa [hT] using hs_closed.preimage h_cont
  have hT_bounded : Bornology.IsBounded T := by
    have hs_bounded : Bornology.IsBounded s := hscomp.isBounded
    rcases (isBounded_iff_forall_norm_le.mp hs_bounded) with ⟨C, hC⟩
    have h_norm_v_pos : 0 < ‖v‖ := by
      by_contra! hle
      have hzero : ‖v‖ = 0 := le_antisymm hle (norm_nonneg v)
      have hzero_v : v = 0 := norm_eq_zero.mp hzero
      exact hv hzero_v
    have h_bound : ∀ t ∈ T, |t| ≤ (C + ‖x‖) / ‖v‖ := by
      intro t ht
      have h_mem : x + t • v ∈ s := ht
      have h_norm_bound : ‖x + t • v‖ ≤ C := hC (x + t • v) h_mem
      have h_abs_bound : |t| * ‖v‖ ≤ C + ‖x‖ := by
        calc
          |t| * ‖v‖ = ‖t • v‖ := by simp [norm_smul]
          _ = ‖(x + t • v) - x‖ := by simp
          _ ≤ ‖x + t • v‖ + ‖x‖ := norm_sub_le _ _
          _ ≤ C + ‖x‖ := by linarith
      -- Use |t| ≤ (C + ‖x‖) / ‖v‖  ↔  ‖v‖ * |t| ≤ C + ‖x‖
      apply (le_div_iff₀' h_norm_v_pos).mpr
      calc
        ‖v‖ * |t| = |t| * ‖v‖ := mul_comm _ _
        _ ≤ C + ‖x‖ := h_abs_bound
    refine isBounded_iff_forall_norm_le.mpr ⟨(C + ‖x‖) / ‖v‖, ?_⟩
    intro t ht
    have h_abs : |t| ≤ (C + ‖x‖) / ‖v‖ := h_bound t ht
    simpa [Real.norm_eq_abs] using h_abs
  have hT_compact : IsCompact T :=
    Metric.isCompact_of_isClosed_isBounded hT_closed hT_bounded
  exact ⟨hT_compact, hT_convex⟩

/-- **The line section is a closed interval.** The section equals `Icc (sInf T) (sSup T)`. -/
theorem lineSection_eq_Icc {s : Set E} (hscomp : IsCompact s) (hsconv : Convex ℝ s)
    {x : E} (hx : x ∈ s) {v : E} (hv : v ≠ 0) :
    {t : ℝ | x + t • v ∈ s} =
      Set.Icc (sInf {t : ℝ | x + t • v ∈ s}) (sSup {t : ℝ | x + t • v ∈ s}) := by
  set T := {t : ℝ | x + t • v ∈ s} with hT
  have h_nonempty : T.Nonempty := by
    refine ⟨0, ?_⟩
    simp [hT, hx]
  have h_compact_convex := lineSection_isCompact_convex hscomp hsconv hx hv
  rcases h_compact_convex with ⟨h_compact, h_convex⟩
  have h_closed : IsClosed T :=
    h_compact.isClosed
  have h_bdd_below : BddBelow T :=
    h_compact.bddBelow
  have h_bdd_above : BddAbove T :=
    h_compact.bddAbove
  have h_connected : IsConnected T :=
    h_convex.isConnected h_nonempty
  rw [hT]
  exact eq_Icc_csInf_csSup_of_connected_bdd_closed h_connected h_bdd_below h_bdd_above h_closed

/-- **Zero is interior to the section.** If `0` is in the interior of the section, then
`sInf T < 0 < sSup T`. -/
theorem lineSection_zero_interior {s : Set E} (hscomp : IsCompact s) (hsconv : Convex ℝ s)
    {x : E} (hx : x ∈ s) {v : E} (hv : v ≠ 0)
    (h0 : 0 ∈ interior {t : ℝ | x + t • v ∈ s}) :
    sInf {t : ℝ | x + t • v ∈ s} < 0 ∧ 0 < sSup {t : ℝ | x + t • v ∈ s} := by
  set T := {t : ℝ | x + t • v ∈ s} with hT
  have hT_eq : T = Set.Icc (sInf T) (sSup T) :=
    lineSection_eq_Icc hscomp hsconv hx hv
  have h0_int_T : 0 ∈ interior T := by
    simpa [hT] using h0
  rw [hT_eq] at h0_int_T
  rw [interior_Icc] at h0_int_T
  rcases h0_int_T with ⟨h_lt, h_gt⟩
  exact ⟨h_lt, h_gt⟩

/-- If `x + c • v` belongs to the intrinsic interior of `s`, then `c` is an interior point of the
section `{t : ℝ | x + t • v ∈ s}`. -/
private lemma lineSection_param_mem_interior {s : Set E} {x : E} (hx : x ∈ s) {v : E}
    (hvspan : v ∈ vectorSpan ℝ s) {c : ℝ} (hc : x + c • v ∈ intrinsicInterior ℝ s) :
    c ∈ interior {t : ℝ | x + t • v ∈ s} := by
  set T := {t : ℝ | x + t • v ∈ s} with hT_def
  let A := affineSpan ℝ s
  have hx_affine : x ∈ A := subset_affineSpan ℝ s hx
  have hv_dir : v ∈ A.direction := by
    rw [direction_affineSpan]
    exact hvspan
  have hx_plus_tv_affine (t : ℝ) : x + t • v ∈ A := by
    have h_tv_dir : t • v ∈ A.direction := A.direction.smul_mem t hv_dir
    have hvadd := A.vadd_mem_of_mem_direction h_tv_dir hx_affine
    simpa [add_comm, vadd_eq_add] using hvadd
  rcases (mem_intrinsicInterior (𝕜 := ℝ)).mp hc with ⟨y, hy, hyx⟩
  let φ : ℝ → A := fun t => ⟨x + t • v, hx_plus_tv_affine t⟩
  have hφ_cont : Continuous φ := by
    refine Continuous.subtype_mk ?_ (fun t => hx_plus_tv_affine t)
    refine continuous_const.add (continuous_id.smul continuous_const)
  have hφc : φ c = y := Subtype.ext (by
    dsimp [φ]
    simp [hyx])
  have h_preimage_open : IsOpen (φ⁻¹' (interior ((↑)⁻¹' s : Set A))) :=
    isOpen_interior.preimage hφ_cont
  have hc_in_preimage : c ∈ φ⁻¹' (interior ((↑)⁻¹' s : Set A)) := by
    dsimp
    simpa [hφc] using hy
  have h_preimage_subset_T : φ⁻¹' (interior ((↑)⁻¹' s : Set A)) ⊆ T := by
    intro t ht
    have hφt_preimage : φ t ∈ (↑)⁻¹' s := interior_subset ht
    simpa [φ, T, hT_def] using hφt_preimage
  have hU_nhds : φ⁻¹' (interior ((↑)⁻¹' s : Set A)) ∈ nhds c :=
    h_preimage_open.mem_nhds hc_in_preimage
  have hT_nhds : T ∈ nhds c := Filter.mem_of_superset hU_nhds h_preimage_subset_T
  exact (mem_interior_iff_mem_nhds (x := c)).mpr hT_nhds

/-- **Endpoints of the section are not interior.** With `a = sInf T` and `b = sSup T`, neither
`x + a • v` nor `x + b • v` lies in the intrinsic interior of `s`. -/
theorem segment_endpoints_not_interior {s : Set E} (hscomp : IsCompact s) (hsconv : Convex ℝ s)
    {x : E} (hx : x ∈ s) {v : E} (hv : v ≠ 0) (hvspan : v ∈ vectorSpan ℝ s) :
    x + (sInf {t : ℝ | x + t • v ∈ s}) • v ∉ intrinsicInterior ℝ s ∧
      x + (sSup {t : ℝ | x + t • v ∈ s}) • v ∉ intrinsicInterior ℝ s := by
  set T := {t : ℝ | x + t • v ∈ s} with hT_def
  set a := sInf T with ha_def
  set b := sSup T with hb_def
  have hT_eq : T = Set.Icc a b := lineSection_eq_Icc hscomp hsconv hx hv
  have h_int_a : x + a • v ∉ intrinsicInterior ℝ s := by
    intro h
    have ha_int_T : a ∈ interior T := lineSection_param_mem_interior hx hvspan h
    rw [hT_eq] at ha_int_T
    rw [interior_Icc] at ha_int_T
    rcases ha_int_T with ⟨ha_lt_a, _⟩
    exact lt_irrefl a ha_lt_a
  have h_int_b : x + b • v ∉ intrinsicInterior ℝ s := by
    intro h
    have hb_int_T : b ∈ interior T := lineSection_param_mem_interior hx hvspan h
    rw [hT_eq] at hb_int_T
    rw [interior_Icc] at hb_int_T
    rcases hb_int_T with ⟨_, hb_gt_b⟩
    exact lt_irrefl b hb_gt_b
  exact ⟨h_int_a, h_int_b⟩

/-- **An interior point lies between two boundary points.** If `finrank (vectorSpan ℝ s) ≥ 1`
and `x` is in the intrinsic interior of `s`, then `x` lies on a segment between two points of `s`
that are not in the intrinsic interior of `s`. -/
theorem interior_in_segment {s : Set E} (hscomp : IsCompact s) (hsconv : Convex ℝ s)
    (h : 1 ≤ Module.finrank ℝ (vectorSpan ℝ s)) {x : E} (hx : x ∈ intrinsicInterior ℝ s) :
    ∃ y ∈ s, ∃ z ∈ s, y ∉ intrinsicInterior ℝ s ∧ z ∉ intrinsicInterior ℝ s ∧
      x ∈ segment ℝ y z := by
  rcases exists_direction_vector h with ⟨v, hv_span, hv_ne⟩
  have hx_s : x ∈ s := intrinsicInterior_subset hx
  set T := {t : ℝ | x + t • v ∈ s} with hT_def
  have h0_T_interior : 0 ∈ interior T := by
    let A := affineSpan ℝ s
    have hx_affine : x ∈ A := subset_affineSpan ℝ s hx_s
    have hv_dir : v ∈ A.direction := by
      rw [direction_affineSpan]
      exact hv_span
    have hx_plus_tv_affine (t : ℝ) : x + t • v ∈ A := by
      have h_tv_dir : t • v ∈ A.direction := A.direction.smul_mem t hv_dir
      have hvadd := A.vadd_mem_of_mem_direction h_tv_dir hx_affine
      simpa [add_comm, vadd_eq_add] using hvadd
    rcases (mem_intrinsicInterior (𝕜 := ℝ)).mp hx with ⟨y, hy, hyx⟩
    let φ : ℝ → A := fun t => ⟨x + t • v, hx_plus_tv_affine t⟩
    have hφ_cont : Continuous φ := by
      refine Continuous.subtype_mk ?_ (fun t => hx_plus_tv_affine t)
      refine continuous_const.add (continuous_id.smul continuous_const)
    have hφ0 : φ 0 = y := Subtype.ext (by
      dsimp [φ]; simp [hyx])
    have h_preimage_open : IsOpen (φ⁻¹' (interior ((↑)⁻¹' s : Set A))) :=
      isOpen_interior.preimage hφ_cont
    have h0_in_preimage : 0 ∈ φ⁻¹' (interior ((↑)⁻¹' s : Set A)) := by
      dsimp; simpa [hφ0] using hy
    have h_preimage_subset_T : φ⁻¹' (interior ((↑)⁻¹' s : Set A)) ⊆ T := by
      intro t ht
      have hφt_preimage : φ t ∈ (↑)⁻¹' s := interior_subset ht
      simpa [φ, T, hT_def] using hφt_preimage
    have hU_nhds : φ⁻¹' (interior ((↑)⁻¹' s : Set A)) ∈ nhds (0 : ℝ) :=
      h_preimage_open.mem_nhds h0_in_preimage
    have hT_nhds : T ∈ nhds (0 : ℝ) := Filter.mem_of_superset hU_nhds h_preimage_subset_T
    exact (mem_interior_iff_mem_nhds (x := (0 : ℝ))).mpr hT_nhds
  rcases lineSection_zero_interior hscomp hsconv hx_s hv_ne h0_T_interior with ⟨ha, hb⟩
  set a := sInf T with ha_def
  set b := sSup T with hb_def
  have ha_lt_zero : a < 0 := ha
  have hb_gt_zero : 0 < b := hb
  have ha_le_b : a ≤ b := by linarith
  have hpos_denom : 0 < b - a := sub_pos.mpr (by linarith)
  have ha_mem_T : a ∈ T := by
    rw [hT_def, lineSection_eq_Icc hscomp hsconv hx_s hv_ne]
    exact ⟨le_rfl, ha_le_b⟩
  have hb_mem_T : b ∈ T := by
    rw [hT_def, lineSection_eq_Icc hscomp hsconv hx_s hv_ne]
    exact ⟨ha_le_b, le_rfl⟩
  set y := x + a • v with hy_def
  set z := x + b • v with hz_def
  have hy_s : y ∈ s := ha_mem_T
  have hz_s : z ∈ s := hb_mem_T
  rcases segment_endpoints_not_interior hscomp hsconv hx_s hv_ne hv_span with ⟨hynot, hznot⟩
  have hx_seg : x ∈ segment ℝ y z := by
    have hcoeff_x : (b / (b - a : ℝ) + (-a) / (b - a : ℝ)) = 1 := by
      field_simp [hpos_denom.ne.symm]
      ring
    have hcoeff_v : (b / (b - a : ℝ) * a + (-a) / (b - a : ℝ) * b) = 0 := by
      field_simp [hpos_denom.ne.symm]
      ring
    refine ⟨b/(b-a), (-a)/(b-a), ?_, ?_, ?_, ?_⟩
    · refine div_nonneg (by linarith) (by linarith)
    · refine div_nonneg (by linarith) (by linarith)
    · exact hcoeff_x
    · calc
        (b/(b-a)) • y + ((-a)/(b-a)) • z
            = (b/(b-a)) • (x + a • v) + ((-a)/(b-a)) • (x + b • v) := rfl
        _ = ((b/(b-a)) • x + ((b/(b-a)) * a) • v) + (((-a)/(b-a)) • x + ((-a)/(b-a) * b) • v) := by
          simp [smul_add, smul_smul]
        _ = ((b/(b-a)) • x + ((-a)/(b-a)) • x) + (((b/(b-a)) * a) • v + ((-a)/(b-a) * b) • v) := by abel
        _ = ((b/(b-a) + (-a)/(b-a)) • x) + (((b/(b-a)) * a + (-a)/(b-a) * b) • v) := by
          simp [add_smul]
        _ = 1 • x + 0 • v := by simp [hcoeff_x, hcoeff_v]
        _ = x := by simp
  exact ⟨y, hy_s, z, hz_s, hynot, hznot, hx_seg⟩

/-! ### Minkowski's theorem -/

/-- **Zero-dimensional base case.** If `finrank (vectorSpan ℝ s) = 0` and `x ∈ s`, then `x` is an
extreme point of `s` (indeed `s = {x}`). -/
theorem base_case [FiniteDimensional ℝ E] {s : Set E} {x : E}
    (h : Module.finrank ℝ (vectorSpan ℝ s) = 0) (hx : x ∈ s) :
    x ∈ s.extremePoints ℝ := by
  -- finrank 0 implies vectorSpan ℝ s = ⊥
  have hspan_bot : vectorSpan ℝ s = ⊥ :=
    (Submodule.finrank_eq_zero (R := ℝ) (S := vectorSpan ℝ s)).mp h
  -- vectorSpan ℝ s = ⊥ implies s is subsingleton
  have hsubsingleton : s.Subsingleton :=
    (vectorSpan_eq_bot_iff_subsingleton (k := ℝ)).mp hspan_bot
  -- Show x is an extreme point of s
  rw [mem_extremePoints_iff_left]
  refine ⟨hx, ?_⟩
  intro x₁ hx₁ x₂ hx₂ hx_mem
  -- Since s is subsingleton, all points in s are equal
  exact hsubsingleton hx₁ hx

/-- **Reduction at a relative boundary point.** A relative boundary point `y` of a nonempty
compact convex set `s` lies in a compact convex face `F ⊆ s` of strictly smaller affine dimension
whose extreme points are extreme points of `s`. -/
theorem minkowski_boundary [FiniteDimensional ℝ E] {s : Set E} (hscomp : IsCompact s)
    (hsconv : Convex ℝ s) (hne : s.Nonempty) {y : E} (hy : y ∈ s)
    (hynotin : y ∉ intrinsicInterior ℝ s) :
    ∃ F : Set E, F ⊆ s ∧ IsCompact F ∧ Convex ℝ F ∧
      F.extremePoints ℝ ⊆ s.extremePoints ℝ ∧ y ∈ F ∧
      Module.finrank ℝ (vectorSpan ℝ F) < Module.finrank ℝ (vectorSpan ℝ s) := by
  rcases supporting_functional hsconv hne hy hynotin with ⟨ℓ, ⟨a, ha, b, hb, hneq⟩, hbound⟩
  set F := exposedFace ℓ s with hF
  have hF_sub_s : F ⊆ s := by
    intro x hx
    exact hx.1
  have hy_F : y ∈ F := by
    refine ⟨hy, ?_⟩
    intro z hz
    exact hbound z hz
  rcases exposedFace_isExtreme hscomp hsconv ℓ with ⟨hF_comp, hF_conv, hF_ext⟩
  have hF_finrank : Module.finrank ℝ (vectorSpan ℝ F) < Module.finrank ℝ (vectorSpan ℝ s) :=
    exposedFace_finrank_lt ℓ ha hb hneq
  refine ⟨F, hF_sub_s, hF_comp, hF_conv, hF_ext, hy_F, hF_finrank⟩

/-- **Boundary points are convex combinations of extreme points.** Assuming the induction
hypothesis on lower-dimensional compact convex sets, every relative boundary point `y` of `s`
lies in the convex hull of the extreme points of `s`. -/
theorem minkowski_boundary_mem [FiniteDimensional ℝ E] {s : Set E} (hscomp : IsCompact s)
    (hsconv : Convex ℝ s)
    (IH : ∀ (s₀ : Set E), IsCompact s₀ → Convex ℝ s₀ →
      Module.finrank ℝ (vectorSpan ℝ s₀) < Module.finrank ℝ (vectorSpan ℝ s) →
      ∀ x₀ ∈ s₀, x₀ ∈ convexHull ℝ (s₀.extremePoints ℝ))
    {y : E} (hy : y ∈ s) (hynotin : y ∉ intrinsicInterior ℝ s) :
    y ∈ convexHull ℝ (s.extremePoints ℝ) := by
  have hne : s.Nonempty := ⟨y, hy⟩
  rcases minkowski_boundary hscomp hsconv hne hy hynotin with ⟨F, hFsub, hFcomp, hFconv, hFext, hyF, hFfinrank⟩
  have hy_mem : y ∈ convexHull ℝ (F.extremePoints ℝ) :=
    IH F hFcomp hFconv hFfinrank y hyF
  have h_hull_sub : convexHull ℝ (F.extremePoints ℝ) ⊆ convexHull ℝ (s.extremePoints ℝ) :=
    convexHull_mono hFext
  exact h_hull_sub hy_mem

/-- **Minkowski's theorem** (finite-dimensional Krein–Milman). Every point of a compact convex set
`s` lies in the convex hull of the extreme points of `s`. -/
theorem minkowski [FiniteDimensional ℝ E] {s : Set E} (hscomp : IsCompact s) (hsconv : Convex ℝ s)
    {x : E} (hx : x ∈ s) :
    x ∈ convexHull ℝ (s.extremePoints ℝ) := by
  have h_ne : s.Nonempty := ⟨x, hx⟩
  -- Strong induction on the affine dimension d = finrank ℝ (vectorSpan ℝ s)
  let P : ℕ → Prop := λ d => ∀ (s' : Set E), IsCompact s' → Convex ℝ s' →
    Module.finrank ℝ (vectorSpan ℝ s') = d → ∀ x' ∈ s', x' ∈ convexHull ℝ (s'.extremePoints ℝ)
  have h_step : ∀ (d : ℕ), (∀ (d' : ℕ), d' < d → P d') → P d := by
    intro d ih s' hscomp' hsconv' hfinrank_eq_d' x' hx'
    -- Build the induction hypothesis for sets of lower dimension (the shape needed by minkowski_boundary_mem)
    have h_IH : ∀ (s₀ : Set E), IsCompact s₀ → Convex ℝ s₀ →
      Module.finrank ℝ (vectorSpan ℝ s₀) < Module.finrank ℝ (vectorSpan ℝ s') → ∀ x₀ ∈ s₀, x₀ ∈ convexHull ℝ (s₀.extremePoints ℝ) := by
      intro s₀ hscomp₀ hsconv₀ h_finrank_lt
      have h_finrank_lt_d : Module.finrank ℝ (vectorSpan ℝ s₀) < d := by
        rw [← hfinrank_eq_d']
        exact h_finrank_lt
      have hPm : P (Module.finrank ℝ (vectorSpan ℝ s₀)) :=
        ih (Module.finrank ℝ (vectorSpan ℝ s₀)) h_finrank_lt_d
      exact hPm s₀ hscomp₀ hsconv₀ rfl
    by_cases h_int : x' ∈ intrinsicInterior ℝ s'
    · by_cases h_d_zero : d = 0
      · have h_base : x' ∈ s'.extremePoints ℝ :=
          base_case (by
            rw [hfinrank_eq_d', h_d_zero]) hx'
        exact subset_convexHull ℝ (s'.extremePoints ℝ) h_base
      · have h_dim_pos : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr h_d_zero
        have h_dim_pos' : 1 ≤ Module.finrank ℝ (vectorSpan ℝ s') := by
          rw [hfinrank_eq_d']
          exact h_dim_pos
        rcases interior_in_segment hscomp' hsconv' h_dim_pos' h_int with ⟨y, hy, z, hz, hy_not, hz_not, hx_seg⟩
        have hy_mem : y ∈ convexHull ℝ (s'.extremePoints ℝ) :=
          minkowski_boundary_mem hscomp' hsconv' h_IH hy hy_not
        have hz_mem : z ∈ convexHull ℝ (s'.extremePoints ℝ) :=
          minkowski_boundary_mem hscomp' hsconv' h_IH hz hz_not
        have h_conv : Convex ℝ (convexHull ℝ (s'.extremePoints ℝ)) := convex_convexHull ℝ (s'.extremePoints ℝ)
        have h_seg : segment ℝ y z ⊆ convexHull ℝ (s'.extremePoints ℝ) :=
          h_conv.segment_subset hy_mem hz_mem
        exact h_seg hx_seg
    · exact minkowski_boundary_mem hscomp' hsconv' h_IH hx' h_int
  have h_result : P (Module.finrank ℝ (vectorSpan ℝ s)) :=
    Nat.strong_induction_on (Module.finrank ℝ (vectorSpan ℝ s)) h_step
  exact h_result s hscomp hsconv rfl x hx

/-! ### Main theorem -/

/-- **Minkowski–Carathéodory theorem.** Every point of a compact convex set in a
finite-dimensional real normed space is a convex combination of at most `finrank ℝ E + 1`
extreme points. -/
@[eval_problem]
theorem mem_convexHull_finset_extremePoints_of_mem_compact_convex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} {x : E}
    (hscomp : IsCompact s)
    (hsconv : Convex ℝ s)
    (hx : x ∈ s) :
    ∃ t : Finset E,
      (↑t : Set E) ⊆ s.extremePoints ℝ ∧
      t.card ≤ Module.finrank ℝ E + 1 ∧
      x ∈ convexHull ℝ (↑t : Set E) := by
  have hx_minkowski : x ∈ convexHull ℝ (s.extremePoints ℝ) :=
    minkowski hscomp hsconv hx
  rcases caratheodory_card hx_minkowski with ⟨t, ht_sub, ht_card, hx_t⟩
  refine ⟨t, ht_sub, ht_card, hx_t⟩

end ConvexGeometry
end LeanEval
