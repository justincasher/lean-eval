import Mathlib
open PiTensorProduct

variable {R : Type*} [Field R] {M : Type*} [AddCommGroup M] [Module R M] {k : ℕ}

#check (inferInstance : Module.Finite R (⨂[R]^k M))
