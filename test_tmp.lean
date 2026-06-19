import LeanEval.Topology.Brouwer.Triangulation
open LeanEval.Topology

example (n : ℕ) : AffineIndependent ℝ (cornerVertex n) := by
  rw [affineIndependent_iff_linearIndependent_vsub ℝ (cornerVertex n) (0 : Fin (n+1))]
  have h0 : cornerVertex n (0 : Fin (n+1)) = 0 := by
    simp [cornerVertex]
  have h_goal_eq : (fun (i : {x : Fin (n+1) // x ≠ 0}) => cornerVertex n (i.val) -ᵥ cornerVertex n (0 : Fin (n+1))) =
    (fun (i : {x : Fin (n+1) // x ≠ 0}) => cornerVertex n (i.val)) := by
    ext i; simp [h0]
  rw [h_goal_eq]
  -- Now goal: LinearIndependent ℝ (fun (i : {x : Fin (n+1) // x ≠ 0}) => cornerVertex n (i.val))
  have h_basis_li : LinearIndependent ℝ (EuclideanSpace.basisFun (Fin n) ℝ) :=
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.linearIndependent
  -- h_basis_li  : LinearIndependent ℝ (fun (j : Fin n) => EuclideanSpace.single j (1 : ℝ))
  -- Define h : {x : Fin (n+1) // x ≠ 0} → Fin n
  let h_fun : {x : Fin (n+1) // x ≠ 0} → Fin n := fun i =>
    Fin.pred i.val (by
      intro hzero; apply i.property; simpa using hzero)
  -- Show h_fun is injective
  have h_inj : Function.Injective h_fun := by
    intro a b h_eq
    ext
    apply Fin.succ_pred
    -- Since h_fun a = h_fun b, we have Fin.pred a.val = Fin.pred b.val
    -- So Fin.succ (Fin.pred a.val) = Fin.succ (Fin.pred b.val)
    -- And Fin.succ (Fin.pred x) = x for x ≠ 0
    -- So a.val = b.val
    -- Actually, we can use Fin.succ_pred
    have ha_succ : Fin.succ (h_fun a) = a.val := Fin.succ_pred (by exact a.property)
    have hb_succ : Fin.succ (h_fun b) = b.val := Fin.succ_pred (by exact b.property)
    calc
      a.val = Fin.succ (h_fun a) := by symm; exact ha_succ
      _ = Fin.succ (h_fun b) := by simpa [h_fun, h_eq]
      _ = b.val := hb_succ
  -- Show cornerVertex n (i.val) = EuclideanSpace.basisFun (Fin n) ℝ (h_fun i)
  have h_comp : ∀ (i : {x : Fin (n+1) // x ≠ 0}),
    cornerVertex n (i.val) = EuclideanSpace.basisFun (Fin n) ℝ (h_fun i) := by
    intro i
    simp [cornerVertex, h_fun, EuclideanSpace.basisFun]
  -- Now we have: (fun i => cornerVertex n (i.val)) = (EuclideanSpace.basisFun (Fin n) ℝ) ∘ h_fun
  -- Using h_comp
  calc
    (fun (i : {x : Fin (n+1) // x ≠ 0}) => cornerVertex n (i.val))
        = (EuclideanSpace.basisFun (Fin n) ℝ) ∘ h_fun := by
          ext i; simp [h_comp]
    _ is LinearIndependent ℝ (by
      apply h_basis_li.comp h_inj)
  sorry
