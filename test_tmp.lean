import LeanEval.Topology.Brouwer.Triangulation
open LeanEval.Topology

#check Pi.linearIndependent_single_one (Fin 3) ℝ
-- Let me see what Pi.linearIndependent_single_one says about EuclideanSpace
#check (Pi.linearIndependent_single_one (Fin 3) ℝ).map'
#check LinearIndependent.map
#check (Pi.linearIndependent_single_one (Fin 3) ℝ).comp (fun (i : Fin 3) => i) (by intro a b h; exact h)
#check (Pi.linearIndependent_single_one (Fin 3) ℝ).comp (fun (i : Fin 3) => i) Function.injective_id
#check (Function.Injective) (fun (f : EuclSp 3) => f)
#check (Pi.linearIndependent_single_one (Fin 3) ℝ)
#check (Pi.linearIndependent_single_one (Fin 3) ℝ).comp (fun (i : Fin 3) => i) (by intro a b h; exact Function.injective_id h)
-- Actually let's use `h` : EuclideanSpace.single = Pi.single
#check fun (i : Fin 3) => (Pi.single i (1 : ℝ) : EuclSp 3)
#check (Pi.linearIndependent_single_one (Fin 3) ℝ).map (fun (f : Fin 3 → ℝ) => (f : EuclSp 3)) (by
  intro f g h; ext i; exact congr_fun h i)
