import LeanEval.ComplexAnalysis.Rouche.Boundary
import LeanEval.ComplexAnalysis.Rouche.LogDerivBasics
import LeanEval.ComplexAnalysis.Rouche.ArgumentPrinciple
import LeanEval.ComplexAnalysis.Rouche.Winding
import LeanEval.ComplexAnalysis.Rouche.Conclusion

/-!
# Supporting lemmas for Rouché's theorem via zero counting

This file aggregates the supporting lemmas of the blueprint
`rouche-theorem-via-zero-counting`, now split across focused modules:

- `Rouche/Boundary.lean` — behaviour of `f`, `g`, `f + g` and their divisors on the
  boundary circle.
- `Rouche/LogDerivBasics.lean` — logarithmic-derivative and circle-integral building
  blocks, including the factorization existence statement.
- `Rouche/ArgumentPrinciple.lean` — the argument-principle integral split and the
  assembled zero-counting statement.
- `Rouche/Winding.lean` — vanishing winding of `(f + g) / f`.
- `Rouche/Conclusion.lean` — matching pole divisors and the mass decomposition.

The conclusion theorem `thm:rouche` lives in `LeanEval/ComplexAnalysis/Rouche.lean`.
-/
