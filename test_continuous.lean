import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Normed

open scoped Matrix Matrix.Norms.Operator

example (n : ℕ) (B : Matrix (Fin n) (Fin n) ℂ) : Continuous (fun (s : ℝ) => s • B) := by
  continuity