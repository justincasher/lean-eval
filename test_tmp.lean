import LeanEval.Topology.Brouwer.Triangulation
open LeanEval.Topology

#check (EuclideanSpace.basisFun (Fin 3) ℝ) (0 : Fin 3)
#check EuclideanSpace.basisFun (Fin 3) ℝ
example : (EuclideanSpace.basisFun (Fin 3) ℝ) (0 : Fin 3) = EuclideanSpace.single (0 : Fin 3) (1 : ℝ) := by
  simp
