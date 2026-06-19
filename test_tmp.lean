import LeanEval.Topology.Brouwer.Triangulation
open LeanEval.Topology

-- Test the structure for ind'
example (n : ℕ) : AffineIndependent ℝ (cornerVertex n) := by
  rw [affineIndependent_iff_linearIndependent_vsub ℝ (cornerVertex n) (0 : Fin (n+1))]
  -- The codomain type is EuclSp n = EuclideanSpace ℝ (Fin n) which is a module over ℝ
  -- The vectors (cornerVertex n i -ᵥ cornerVertex n (0 : Fin (n+1))) for i ≠ 0 are the standard basis vectors
  -- We need to show LinearIndependent ℝ (fun (i : {x : Fin (n+1) // x ≠ 0}) => cornerVertex n i -ᵥ cornerVertex n (0 : Fin (n+1)))
  -- Since cornerVertex n 0 = 0 and vsub in a vector space is subtraction, cornerVertex n i -ᵥ 0 = cornerVertex n i
  have h0 : cornerVertex n (0 : Fin (n+1)) = 0 := by
    simp [cornerVertex]
  have h_vsub : ∀ (i : Fin (n+1)), (cornerVertex n i -ᵥ cornerVertex n (0 : Fin (n+1)) : EuclSp n) = cornerVertex n i := by
    intro i; simp [h0]
  -- We can rewrite using this
  -- But the goal is LinearIndependent ℝ (fun (i : {x // x ≠ 0}) => ...)
  -- Let's define a function f : {x : Fin (n+1) // x ≠ 0} → EuclSp n
  -- f i = cornerVertex n i -ᵥ cornerVertex n 0
  -- And we need to show it's linearly independent
  -- Since h_vsub says f i = cornerVertex n i for all i (including i ≠ 0)
  -- This is equivalent to showing linear independence of cornerVertex n restricted to {x // x ≠ 0}
  -- We can use the EuclideanSpace.basisFun
  sorry
