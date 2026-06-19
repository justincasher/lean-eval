# Milestones (run 980414ba)

## User request
Blueprint writer finished. Confirm all declarations updated, then launch the
formalizer and the prover.

## Blueprint state
- draft_blueprint ran 3 passes (reviewer FAIL on passes 1 and 2; pass 3 writer
  produced the current .tex). Decomposed from 41 -> 92 metadata entries.
- refresh_blueprint_metadata done: all 92 entries reflect the new .tex.

## CRITICAL FINDING: Hopf value is a genuine Mathlib obstruction
The pass-3 writer did not resolve the Hopf linking-number evaluation; it
documented it as an obstruction:
- lem:hopf-inner-integral (LeanEval.KnotTheory.hopf_inner_integral): the inner
  integral G(t) = int_0^2pi (1/2 D^-1/2 - 3/2 D^-3/2) ds is a nonzero
  combination of complete elliptic integrals K(k), E(k). Mathlib has no
  elliptic-integral theory; no elementary closed form / periodic antiderivative
  exists (integrand depends only on cos s, full-period average is elliptic).
- lem:hopf-outer-integral (hopf_outer_integral): int_0^2pi G(t) dt = 4pi is a
  mapping-degree/solid-angle fact; iterated 1D FTC cannot evaluate it in either
  order (both orders elliptic).
- Consequently lem:hopf-linking-value, lem:linking-hopf-nonzero, and
  thm:exists-nonisotopic-link cannot close through this chain.
This was independently confirmed: the elementary analytic route for lk(Hopf) is
not formalizable in Mathlib as-is. Resolving it needs a strategy decision
(mapping-degree ingredient, replace the distinguishing invariant, or choose a
link pair whose Gauss integral is elementary). DEFERRED pending user input.

## Plan this run
1. [done] refresh_blueprint_metadata.
2. [in progress] formalize whole blueprint into LeanEval/KnotTheory/Linking.lean
   (89 provable + ~2-3 obstruction stubs).
3. mark_declaration_formalized for labels the formalizer tags.
4. run_provers in dependency order on the provable declarations; leave the Hopf
   elliptic chain as documented sorries.

## Provable bulk (actionable)
All smoothness/continuity lemmas, divergence identity chain, periodic-divergence,
Leibniz/hasDerivAt, reparam invariance, isotopy invariance theorem, coordinate
circle lemmas, unlink/hopf disjointness, unlink integrand + antideriv + lk=0,
hopf integrand/reduced/denominator/halfangle-reduction/regularity.

## Blocked (deferred, needs strategy decision)
lem:hopf-inner-integral, lem:hopf-outer-integral, lem:hopf-linking-value, and
(transitively) thm:exists-nonisotopic-link.

## Status
- [in progress] Launching formalizer.
