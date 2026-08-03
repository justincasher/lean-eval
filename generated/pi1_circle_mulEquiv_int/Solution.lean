import ChallengeDeps
import Submission

open LeanEval.Topology

theorem pi1_circle_mulEquiv_int :
    Nonempty (HomotopyGroup.Pi 1 Circle (1 : Circle) ≃* Multiplicative ℤ) := by
  exact Submission.pi1_circle_mulEquiv_int
