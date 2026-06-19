import Mathlib
open LeanEval
open LeanEval.Topology

#check cornerVertex 3
#check cornerVertex 3 0
#check cornerVertex 3 (Fin.succ 0)
#check Pi.linearIndependent_single_one (Fin 3) ℝ
#check affineIndependent_iff_linearIndependent_vsub ℝ (cornerVertex 3) (0 : Fin 4)
