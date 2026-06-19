import LeanEval.Topology.Brouwer.Triangulation
open LeanEval.Topology

-- Simpler approach: just use `simp` or `apply`
example : LinearIndependent ℝ (fun (i : Fin 3) => EuclideanSpace.single i (1 : ℝ)) := by
  have h := Pi.linearIndependent_single_one (Fin 3) ℝ
  have hequiv : (Fin 3 → ℝ) ≃ₗ[ℝ] EuclSp 3 := (EuclideanSpace.equiv (Fin 3) ℝ).symm
  have h_comp : (fun (i : Fin 3) => EuclideanSpace.single i (1 : ℝ)) = hequiv ∘ (fun (i : Fin 3) => Pi.single i (1 : ℝ)) := by
    ext i; simp
  -- Use `map` with an injective linear map
  have hinj : Function.Injective (hequiv : (Fin 3 → ℝ) →ₗ[ℝ] EuclSp 3) := by
    apply hequiv.injective
  exact h.map hinj
