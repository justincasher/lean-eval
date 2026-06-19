import Mathlib

/-!
# Kuznetsov / Boone–Higman: the computability engine

Supporting definitions and lemmas for Kuznetsov's theorem on the solvability of
the word problem of a finitely presented simple group.  This file sets up the
*conjugacy certificate* machinery and the computability facts feeding the
recursive-enumerability arguments.

Words are signed letters `List (Fin n × Bool)`; `FreeGroup.mk` turns such a word
into the free-group element it spells.  A **certificate** is a finite list of
triples `(g, ε, k)` with `g` a word, `ε : Bool` a sign and `k : ℕ` an index into
a list of relators `R`; its *value word* `evalCert R c` is the concatenation of
the conjugacy terms `g · (R_k)^{±1} · g⁻¹`.
-/

namespace LeanEval.GroupTheory.BooneHigmanSimpleProblem

/-- A signed word in the generators `Fin n` and their inverses. -/
abbrev Word (n : ℕ) := List (Fin n × Bool)

/-- A **conjugacy certificate** over a relator list `R`: a finite list of triples
`(g, ε, k)` with `g` a word, `ε : Bool` a sign, and `k : ℕ` an index into `R`. -/
abbrev Certificate (n : ℕ) := List (Word n × Bool × ℕ)

/-- The relator word `R_k` raised to the formal sign `ε`: `R_k` if `ε = true`,
its formal inverse `FreeGroup.invRev R_k` if `ε = false`. -/
def signedRelator {n : ℕ} (R : List (Word n)) (ε : Bool) (k : ℕ) : Word n :=
  bif ε then R.getD k [] else FreeGroup.invRev (R.getD k [])

/-- The conjugacy term word `g ++ (R_k)^{ε} ++ invRev g` attached to a triple
`(g, ε, k)`. -/
def conjTerm {n : ℕ} (R : List (Word n)) (t : Word n × Bool × ℕ) : Word n :=
  t.1 ++ signedRelator R t.2.1 t.2.2 ++ FreeGroup.invRev t.1

/-- The **value word** `evalCert R c` of a certificate `c`: the concatenation of
the conjugacy terms of its triples. -/
def evalCert {n : ℕ} (R : List (Word n)) (c : Certificate n) : Word n :=
  (c.map (conjTerm R)).flatten

/-- The single step folded by `FreeGroup.reduce`: prepend a letter `a` to an
already-reduced word `u`, cancelling against the head of `u` when they are
inverse. -/
def reduceStep {n : ℕ} (a : Fin n × Bool) (u : Word n) : Word n :=
  match u with
  | [] => [a]
  | hd :: tl => if a.1 = hd.1 ∧ a.2 = !hd.2 then tl else a :: hd :: tl

/-- **Letter equality is primitive recursive.** Equality of signed letters and
the cancellation test `a = (b.1, ¬ b.2)` are primitive-recursive relations. -/
lemma primrec_eq_letter {n : ℕ} :
    PrimrecRel (fun a b : Fin n × Bool => a = b) ∧
      PrimrecRel (fun a b : Fin n × Bool => a = (b.1, !b.2)) := by
  sorry

/-- **The reduction step is primitive recursive.** -/
lemma primrec_reduceStep {n : ℕ} :
    Primrec₂ (@reduceStep n) := by
  sorry

/-- **Reduction is primitive recursive.** -/
lemma primrec_reduce {n : ℕ} :
    Primrec (fun w : Word n => FreeGroup.reduce w) := by
  sorry

/-- **Reduction is computable.** -/
lemma reduce_computable {n : ℕ} :
    Computable (fun w : Word n => FreeGroup.reduce w) := by
  sorry

/-- **Formal inversion is primitive recursive.** -/
lemma primrec_invRev {n : ℕ} :
    Primrec (fun u : Word n => FreeGroup.invRev u) := by
  sorry

/-- **A conjugacy term is primitive recursive** in `(R, (g, ε, k))`. -/
lemma primrec_conjTerm {n : ℕ} :
    Primrec₂ (@conjTerm n) := by
  sorry

/-- **Certificate evaluation is primitive recursive** in `(R, c)`. -/
lemma primrec_eval {n : ℕ} :
    Primrec₂ (@evalCert n) := by
  sorry

/-- **Certificate evaluation is computable.** The relation
`reduce (evalCert R c) = reduce w` is a computable (hence pointwise-decidable)
relation in `(R, w, c)`. -/
lemma eval_computable {n : ℕ} :
    ComputablePred
      (fun p : List (Word n) × Word n × Certificate n =>
        FreeGroup.reduce (evalCert p.1 p.2.2) = FreeGroup.reduce p.2.1) := by
  sorry

/-- **Recursive enumerability of an existential over a computable relation.**
If `Q : α → β → Prop` is computable (as a predicate on `α × β`), then
`a ↦ ∃ b, Q a b` is recursively enumerable. -/
lemma re_projection {α β : Type*} [Primcodable α] [Primcodable β]
    {Q : α → β → Prop} (hQ : ComputablePred fun p : α × β => Q p.1 p.2) :
    REPred (fun a => ∃ b, Q a b) := by
  sorry

/-- **Recursive enumerability is closed under conjunction.** -/
lemma re_and {α : Type*} [Primcodable α] {p q : α → Prop}
    (hp : REPred p) (hq : REPred q) :
    REPred (fun a => p a ∧ q a) := by
  sorry

/-- **Finite conjunction over generators is r.e.** -/
lemma re_forall_fin {α : Type*} [Primcodable α] {n : ℕ} {p : Fin n → α → Prop}
    (hp : ∀ i, REPred (p i)) :
    REPred (fun a => ∀ i : Fin n, p i a) := by
  sorry

end LeanEval.GroupTheory.BooneHigmanSimpleProblem
