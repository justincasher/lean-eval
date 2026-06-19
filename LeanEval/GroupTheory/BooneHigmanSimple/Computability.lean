import Mathlib

set_option maxHeartbeats 400000

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
  refine ⟨?_, ?_⟩
  · exact Primrec.eq
  · refine PrimrecRel.comp₂ Primrec.eq ?_ ?_
    · exact Primrec.fst
    · exact Primrec.pair (Primrec.fst.comp Primrec.snd) (Primrec.not.comp (Primrec.snd.comp Primrec.snd))

/-- **The reduction step is primitive recursive.** -/
lemma primrec_reduceStep {n : ℕ} :
    Primrec₂ (@reduceStep n) := by
  -- Work with the uncurried form: Primrec (fun p : (Fin n × Bool) × Word n => reduceStep p.1 p.2)
  have h_nil : Primrec (fun (p : (Fin n × Bool) × Word n) => [p.1]) :=
    (Primrec.list_cons (α := Fin n × Bool)).comp
      (Primrec.fst : Primrec (fun p : (Fin n × Bool) × Word n => p.1))
      (Primrec.const [])
  -- define the body for the non-nil case
  let h' : (Fin n × Bool) × Word n → (Fin n × Bool) × Word n → Word n :=
    fun p q => if p.1 = (q.1.1, !q.1.2) then q.2 else p.1 :: q.1 :: q.2
  have h_cond : PrimrecPred (fun (pair : ((Fin n × Bool) × Word n) × ((Fin n × Bool) × Word n)) =>
    pair.1.1 = (pair.2.1.1, !pair.2.1.2)) :=
    (primrec_eq_letter.2).comp
      (Primrec.fst.comp Primrec.fst)  -- extracts a = p.1
      (Primrec.fst.comp Primrec.snd)  -- extracts hd = q.1
  have h_tl : Primrec (fun (pair : ((Fin n × Bool) × Word n) × ((Fin n × Bool) × Word n)) => pair.2.2) :=
    Primrec.snd.comp Primrec.snd
  have h_else : Primrec (fun (pair : ((Fin n × Bool) × Word n) × ((Fin n × Bool) × Word n)) =>
    pair.1.1 :: pair.2.1 :: pair.2.2) :=
    (Primrec.list_cons (α := Fin n × Bool)).comp (Primrec.fst.comp Primrec.fst)
      ((Primrec.list_cons (α := Fin n × Bool)).comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
  have h_pair : Primrec (fun (pair : ((Fin n × Bool) × Word n) × ((Fin n × Bool) × Word n)) =>
    if pair.1.1 = (pair.2.1.1, !pair.2.1.2) then pair.2.2 else pair.1.1 :: pair.2.1 :: pair.2.2) :=
    Primrec.ite h_cond h_tl h_else
  have h_primrec₂ : Primrec₂ h' := h_pair
  refine (Primrec.list_casesOn (α := (Fin n × Bool) × Word n) (β := Fin n × Bool) (σ := Word n)
    (f := fun p => p.2) (g := fun p => [p.1]) (h := h') Primrec.snd ?_ h_primrec₂).of_eq ?_
  · -- g is Primrec
    simpa using h_nil
  · -- the constructed function equals reduceStep
    intro p
    dsimp [reduceStep]
    cases p.2 with
    | nil => rfl
    | cons hd tl =>
      dsimp [h']
      simp [Prod.ext_iff]

/-- **`FreeGroup.reduce` folds `reduceStep` over the word.** -/
lemma reduce_foldr_eq {n : ℕ} (w : Word n) : w.foldr reduceStep [] = FreeGroup.reduce w := by
  induction w with
  | nil => rfl
  | cons h t ih =>
    calc
      (h :: t).foldr reduceStep [] = reduceStep h (t.foldr reduceStep []) := rfl
      _ = reduceStep h (FreeGroup.reduce t) := by rw [ih]
      _ = FreeGroup.reduce (h :: t) := by
        have h_lemma : ∀ (u : Word n),
            (match u with | [] => [h] | hd :: tl => if h.1 = hd.1 ∧ h.2 = !hd.2 then tl else h :: hd :: tl) =
            (List.rec [h] (fun head tail _ => if h.1 = head.1 ∧ h.2 = !head.2 then tail else h :: head :: tail) u) := by
          intro u; cases u <;> rfl
        calc
          reduceStep h (FreeGroup.reduce t) =
              (match FreeGroup.reduce t with | [] => [h] | hd :: tl => if h.1 = hd.1 ∧ h.2 = !hd.2 then tl else h :: hd :: tl) := rfl
          _ = (List.rec [h] (fun head tail _ => if h.1 = head.1 ∧ h.2 = !head.2 then tail else h :: head :: tail) (FreeGroup.reduce t)) :=
            h_lemma (FreeGroup.reduce t)
          _ = FreeGroup.reduce (h :: t) := by
            simp [FreeGroup.reduce]

/-- **Reduction is primitive recursive.** -/
lemma primrec_reduce {n : ℕ} :
    Primrec (fun w : Word n => FreeGroup.reduce w) := by
  have h_foldr : Primrec (fun (w : Word n) => w.foldr reduceStep []) :=
    Primrec.list_foldr (f := id) (g := fun (_ : Word n) => [])
      (h := fun (_ : Word n) (p : (Fin n × Bool) × Word n) => reduceStep p.1 p.2)
      (hf := Primrec.id)
      (hg := Primrec.const ([] : Word n))
      (hh := by
        have h_prs : Primrec (fun (p' : Word n × ((Fin n × Bool) × Word n)) => p'.2.1) :=
          Primrec.fst.comp Primrec.snd
        have h_prs2 : Primrec (fun (p' : Word n × ((Fin n × Bool) × Word n)) => p'.2.2) :=
          Primrec.snd.comp Primrec.snd
        exact Primrec₂.comp primrec_reduceStep h_prs h_prs2)
  refine h_foldr.of_eq reduce_foldr_eq

/-- **Reduction is computable.** -/
lemma reduce_computable {n : ℕ} :
    Computable (fun w : Word n => FreeGroup.reduce w) :=
  primrec_reduce.to_comp

/-- **Formal inversion is primitive recursive.** -/
lemma primrec_invRev {n : ℕ} :
    Primrec (fun u : Word n => FreeGroup.invRev u) := by
  have h_flip : Primrec (fun (g : Fin n × Bool) => (g.1, !g.2)) :=
    Primrec.pair Primrec.fst (Primrec.not.comp Primrec.snd)
  have h_flip₂ : Primrec₂ (fun (_ : Word n) (b : Fin n × Bool) => (b.1, !b.2)) :=
    Primrec.comp₂ h_flip Primrec₂.right
  have h_map : Primrec (fun (u : Word n) => List.map (fun g => (g.1, !g.2)) u) :=
    Primrec.list_map Primrec.id h_flip₂
  exact (Primrec.list_reverse.comp h_map).of_eq (by
    intro u
    simp [FreeGroup.invRev])

/-- **A conjugacy term is primitive recursive** in `(R, (g, ε, k))`. -/
lemma primrec_conjTerm {n : ℕ} :
    Primrec₂ (@conjTerm n) := by
  unfold Primrec₂
  -- projections from the input pair (R, (g, ε, k))
  have hR : Primrec (fun (p : List (Word n) × (Word n × Bool × ℕ)) => p.1) :=
    Primrec.fst
  have hg : Primrec (fun (p : List (Word n) × (Word n × Bool × ℕ)) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hε : Primrec (fun (p : List (Word n) × (Word n × Bool × ℕ)) => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hk : Primrec (fun (p : List (Word n) × (Word n × Bool × ℕ)) => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)

  -- R.getD k []  (using Primrec₂.comp since list_getD is a Primrec₂)
  have h_getD : Primrec (fun (p : List (Word n) × (Word n × Bool × ℕ)) =>
    (p.1).getD (p.2.2.2) []) :=
    (Primrec.list_getD ([] : Word n)).comp hR hk

  -- invRev (R.getD k [])
  have h_invRev_getD : Primrec (fun (p : List (Word n) × (Word n × Bool × ℕ)) =>
    FreeGroup.invRev ((p.1).getD (p.2.2.2) [])) :=
    primrec_invRev.comp h_getD

  -- signedRelator R ε k (using conditional on ε)
  have h_signedRelator : Primrec (fun (p : List (Word n) × (Word n × Bool × ℕ)) =>
    signedRelator p.1 p.2.2.1 p.2.2.2) :=
    Primrec.cond hε h_getD h_invRev_getD

  -- g ++ signedRelator R ε k
  have h_g_sr : Primrec (fun (p : List (Word n) × (Word n × Bool × ℕ)) =>
    p.2.1 ++ signedRelator p.1 p.2.2.1 p.2.2.2) := by
    have h_append : Primrec₂ ((· ++ ·) : List (Fin n × Bool) → List (Fin n × Bool) → List (Fin n × Bool)) :=
      Primrec.list_append (α := Fin n × Bool)
    have h := Primrec₂.comp h_append hg h_signedRelator
    simpa using h

  -- invRev g
  have h_invRev_g : Primrec (fun (p : List (Word n) × (Word n × Bool × ℕ)) =>
    FreeGroup.invRev (p.2.1)) :=
    primrec_invRev.comp hg

  -- (g ++ signedRelator R ε k) ++ invRev g = conjTerm R (g, ε, k)
  have h_append' : Primrec₂ ((· ++ ·) : List (Fin n × Bool) → List (Fin n × Bool) → List (Fin n × Bool)) :=
    Primrec.list_append (α := Fin n × Bool)
  refine (Primrec₂.comp h_append' h_g_sr h_invRev_g).of_eq ?_
  intro p
  rfl

/-- **Certificate evaluation is primitive recursive** in `(R, c)`. -/
lemma primrec_eval {n : ℕ} :
    Primrec₂ (@evalCert n) := by
  unfold evalCert
  -- We need Primrec (fun (p : (List (Word n) × Certificate n)) => (p.2.map (conjTerm p.1)).flatten)
  have h_map : Primrec (fun (p : List (Word n) × Certificate n) => p.2.map (conjTerm p.1)) :=
    Primrec.list_map (hf := Primrec.snd) (hg := by
      -- Need Primrec₂ (fun (p : List (Word n) × Certificate n) (t : Word n × Bool × ℕ) => conjTerm p.1 t)
      -- which is Primrec (fun ((p,t) : (List (Word n) × Certificate n) × (Word n × Bool × ℕ)) => conjTerm p.1 t)
      have hproj : Primrec (fun (p : (List (Word n) × Certificate n) × (Word n × Bool × ℕ)) =>
        ((p.1.1 : List (Word n)), p.2)) :=
        Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd
      have h' : Primrec (fun (p : (List (Word n) × Certificate n) × (Word n × Bool × ℕ)) =>
        conjTerm p.1.1 p.2) :=
        (show Primrec (fun (p' : (List (Word n) × (Word n × Bool × ℕ))) => conjTerm p'.1 p'.2) from
          primrec_conjTerm).comp hproj
      exact h')
  refine (Primrec.list_flatten.comp h_map).of_eq ?_
  intro p
  rfl

/-- **Certificate evaluation is computable.** The relation
`reduce (evalCert R c) = reduce w` is a computable (hence pointwise-decidable)
relation in `(R, w, c)`. -/
lemma eval_computable {n : ℕ} :
    ComputablePred
      (fun p : List (Word n) × Word n × Certificate n =>
        FreeGroup.reduce (evalCert p.1 p.2.2) = FreeGroup.reduce p.2.1) := by
  apply PrimrecPred.computablePred
  refine PrimrecRel.comp (Primrec.eq (α := Word n)) ?_ ?_
  · -- f(p) = FreeGroup.reduce (evalCert p.1 p.2.2)
    have h_eval_proj : Primrec (fun (p : List (Word n) × Word n × Certificate n) => evalCert p.1 p.2.2) := by
      have h1 : Primrec (Function.uncurry (@evalCert n)) := Primrec₂.uncurry.mpr primrec_eval
      have h2 : Primrec (fun (p : List (Word n) × Word n × Certificate n) => (p.1, p.2.2)) :=
        Primrec.pair Primrec.fst (Primrec.snd.comp Primrec.snd)
      exact (h1.comp h2).of_eq (by intro p; rfl)
    exact Primrec.comp primrec_reduce h_eval_proj
  · -- g(p) = FreeGroup.reduce p.2.1
    have h_w_proj : Primrec (fun (p : List (Word n) × Word n × Certificate n) => p.2.1) :=
      Primrec.fst.comp Primrec.snd
    exact Primrec.comp primrec_reduce h_w_proj

/-- **Free-group word equality is a reduce test.** Two words name the same
free-group element iff they have equal reductions. -/
lemma mk_eq_iff_reduce {n : ℕ} (u v : Word n) :
    FreeGroup.mk u = FreeGroup.mk v ↔ FreeGroup.reduce u = FreeGroup.reduce v := by
  constructor
  · intro h
    have h' : (FreeGroup.mk u).toWord = (FreeGroup.mk v).toWord := by rw [h]
    rw [FreeGroup.toWord_mk, FreeGroup.toWord_mk] at h'
    exact h'
  · exact FreeGroup.reduce.exact

/-- **The certificate check is a computable predicate.** Specialisation of
`eval_computable` to a fixed relator list `R`: the predicate
`(w, c) ↦ reduce (evalCert R c) = reduce w` is a `ComputablePred`. -/
lemma check_computablePred {n : ℕ} (R : List (Word n)) :
    ComputablePred
      (fun p : Word n × Certificate n =>
        FreeGroup.reduce (evalCert R p.2) = FreeGroup.reduce p.1) := by
  apply PrimrecPred.computablePred
  -- Build the PrimrecPred directly from primrec_reduce and evalCert with fixed R
  refine PrimrecRel.comp (Primrec.eq (α := Word n)) ?_ ?_
  · -- f(p) = reduce (evalCert R p.2)
    have h_eval : Primrec (fun (p : Word n × Certificate n) => evalCert R p.2) :=
      (Primrec₂.comp primrec_eval (Primrec.const R) Primrec.snd).of_eq (by intro p; rfl)
    exact Primrec.comp primrec_reduce h_eval
  · -- g(p) = reduce p.1
    exact Primrec.comp primrec_reduce (Primrec.fst (β := Certificate n))

/-- **Decision function of a computable relation.** For a computable, pointwise
decidable relation `Q`, the boolean function `p ↦ decide (Q p.1 p.2)` on
`α × β` is computable. -/
lemma computablePred_decide {α β : Type*} [Primcodable α] [Primcodable β]
    {Q : α → β → Prop} [∀ a b, Decidable (Q a b)]
    (hQ : ComputablePred fun p : α × β => Q p.1 p.2) :
    Computable (fun p : α × β => decide (Q p.1 p.2)) := by
  exact ComputablePred.decide hQ

/-- **The search kernel is computable.** Given the decision function of `Q`
computable, the option-valued search kernel is `Computable₂`. -/
lemma rproj_kernel {α β : Type*} [Primcodable α] [Primcodable β]
    {Q : α → β → Prop} [∀ a b, Decidable (Q a b)]
    (hdec : Computable (fun p : α × β => decide (Q p.1 p.2))) :
    Computable₂ (fun (a : α) (m : ℕ) =>
      (Encodable.decode m : Option β).bind
        (fun b => bif decide (Q a b) then some b else none)) := by
  unfold Computable₂
  -- Use Computable.option_bind: (f a').bind (g a') where
  --   f : α × ℕ → Option β  with f(a,m) = decode m
  --   g : α × ℕ → β → Option β  with g(a,m) b = bif decide (Q a b) then some b else none
  refine Computable.option_bind ?_ ?_
  · -- f(a,m) = decode m
    have h_snd : Computable (fun (p : α × ℕ) => p.2) := Computable.snd
    exact Computable.decode.comp h_snd
  · -- g(a,m) b = bif decide (Q a b) then some b else none
    unfold Computable₂
    have h_proj : Computable (fun (q : (α × ℕ) × β) => (q.1.1, q.2)) :=
      (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd).to_comp
    have h_inner : Computable (fun (p : α × β) => bif decide (Q p.1 p.2) then some p.2 else none) := by
      refine Computable.cond hdec ?_ ?_
      · -- true: some b
        have h_snd' : Computable (fun (p : α × β) => p.2) := Computable.snd
        exact Computable.option_some.comp h_snd'
      · -- false: none
        exact Computable.const (none : Option β)
    exact h_inner.comp h_proj

/-- **The unbounded search is partial recursive.** -/
lemma rproj_search {α β : Type*} [Primcodable α] [Primcodable β]
    {Q : α → β → Prop} [∀ a b, Decidable (Q a b)]
    (hk : Computable₂ (fun (a : α) (m : ℕ) =>
      (Encodable.decode m : Option β).bind
        (fun b => bif decide (Q a b) then some b else none))) :
    Partrec (fun a : α => Nat.rfindOpt (fun m =>
      (Encodable.decode m : Option β).bind
        (fun b => bif decide (Q a b) then some b else none))) :=
  Partrec.rfindOpt hk

/-- **Domain of the search equals the existential.** -/
lemma rproj_dom {α β : Type*} [Primcodable α] [Primcodable β]
    {Q : α → β → Prop} [∀ a b, Decidable (Q a b)] (a : α) :
    (Nat.rfindOpt (fun m =>
      (Encodable.decode m : Option β).bind
        (fun b => bif decide (Q a b) then some b else none))).Dom ↔ ∃ b, Q a b := by
  constructor
  · intro hdom
    rcases Nat.rfindOpt_dom.mp hdom with ⟨m, b, hmem⟩
    rw [Option.mem_bind_iff] at hmem
    rcases hmem with ⟨b', hmem_decode, hmem_bif⟩
    have hQ_b' : Q a b' := by
      by_cases hQ' : Q a b'
      · exact hQ'
      · exfalso
        have hdec : decide (Q a b') = false := decide_eq_false hQ'
        have hbif_eq : (bif decide (Q a b') then some b' else none) = none := by
          simp [hdec]
        rw [hbif_eq] at hmem_bif
        simp at hmem_bif
    exact ⟨b', hQ_b'⟩
  · intro ⟨b, hQ⟩
    have hQ_dec : decide (Q a b) = true := decide_eq_true hQ
    have hmem : b ∈ ((Encodable.decode (Encodable.encode b) : Option β).bind
        (fun b' => bif decide (Q a b') then some b' else none)) := by
      rw [Option.mem_bind_iff]
      refine ⟨b, ?_, ?_⟩
      · rw [Option.mem_def, Encodable.encodek]
      · have hbif_eq : (bif decide (Q a b) then some b else none) = some b := by
          simp [hQ_dec]
        rw [hbif_eq, Option.mem_def]
    exact (Nat.rfindOpt_dom (f := fun m =>
      (Encodable.decode m : Option β).bind
        (fun b' => bif decide (Q a b') then some b' else none))).mpr
      ⟨Encodable.encode b, b, hmem⟩

/-- **Recursive enumerability of an existential over a computable relation.**
If `Q : α → β → Prop` is computable (as a predicate on `α × β`), then
`a ↦ ∃ b, Q a b` is recursively enumerable. -/
lemma re_projection {α β : Type*} [Primcodable α] [Primcodable β]
    {Q : α → β → Prop} (hQ : ComputablePred fun p : α × β => Q p.1 p.2) :
    REPred (fun a => ∃ b, Q a b) := by
  -- From hQ we obtain a DecidablePred instance for the pair predicate
  rcases hQ with ⟨hQ_dec, hQ_comp⟩
  haveI : ∀ a b, Decidable (Q a b) := fun a b => hQ_dec (a, b)
  -- Obtain a computable decision function for Q
  have hdec : Computable (fun p : α × β => decide (Q p.1 p.2)) :=
    computablePred_decide ⟨hQ_dec, hQ_comp⟩
  -- Build the search kernel
  have hkernel : Computable₂ (fun (a : α) (m : ℕ) =>
      (Encodable.decode m : Option β).bind
        (fun b => bif decide (Q a b) then some b else none)) :=
    rproj_kernel hdec
  -- Make the unbounded search partial recursive
  have hsearch : Partrec (fun a : α => Nat.rfindOpt (fun m =>
      (Encodable.decode m : Option β).bind
        (fun b => bif decide (Q a b) then some b else none))) :=
    rproj_search hkernel
  -- The domain of the search is REPred
  have hdom : REPred (fun a : α => (Nat.rfindOpt (fun m =>
      (Encodable.decode m : Option β).bind
        (fun b => bif decide (Q a b) then some b else none))).Dom) :=
    hsearch.dom_re
  -- Rewrite the domain predicate to the existential using rproj_dom
  refine REPred.of_eq hdom fun a => rproj_dom (Q := Q) a

/-- **`ComputablePred` is closed under computable precomposition.** Keeping `p`
and `g` abstract makes the underlying `decide`-instance unification cheap, which
matters when the concrete predicate is a large term. -/
lemma computablePred_comp {α β : Type*} [Primcodable α] [Primcodable β]
    {p : β → Prop} (hp : ComputablePred p) {g : α → β} (hg : Computable g) :
    ComputablePred (fun a => p (g a)) := by
  classical
  exact Computable.computablePred ((ComputablePred.decide hp).comp hg)

/-- **Recursive enumerability is closed under conjunction.** -/
lemma re_and {α : Type*} [Primcodable α] {p q : α → Prop}
    (hp : REPred p) (hq : REPred q) :
    REPred (fun a => p a ∧ q a) := by
  unfold REPred at hp hq ⊢
  have h_bind : Partrec (fun a : α =>
    (Part.assert (p a) (fun _ => Part.some ())).bind (fun _ : Unit =>
      Part.assert (q a) (fun _ => Part.some ()))) :=
    Partrec.bind hp (hq.comp (Primrec.fst (α := α) (β := Unit)).to_comp)
  refine h_bind.of_eq fun a => ?_
  ext x
  simp [Part.mem_bind_iff, Part.mem_assert_iff]

/-- **Finite conjunction over generators is r.e.** -/
lemma re_forall_fin {α : Type*} [Primcodable α] {n : ℕ} {p : Fin n → α → Prop}
    (hp : ∀ i, REPred (p i)) :
    REPred (fun a => ∀ i : Fin n, p i a) := by
  induction' n with n ih
  · -- n = 0: the universal statement is vacuously true, thus decidable,
    -- and every decidable (hence computable) predicate is r.e.
    have h_true_comp : ComputablePred (fun _ : α => True) := by
      refine ⟨fun a => isTrue trivial, ?_⟩
      have : Computable (fun (_ : α) => true) := (Primrec.const true).to_comp
      exact this
    have h_eq : (fun a : α => ∀ i : Fin 0, p i a) = fun _ : α => True := by
      ext a; simp
    rw [h_eq]
    exact ComputablePred.to_re h_true_comp
  · -- n = n.succ: use Fin.forall_fin_succ to rewrite as conjunction,
    -- then apply re_and and the induction hypothesis
    have h0 : REPred (p 0) := hp 0
    have hrest : REPred (fun a : α => ∀ i : Fin n, p i.succ a) := ih fun i => hp i.succ
    have hand : REPred (fun a : α => p 0 a ∧ ∀ i : Fin n, p i.succ a) := re_and h0 hrest
    refine REPred.of_eq hand fun a => ?_
    rw [Fin.forall_fin_succ]

end LeanEval.GroupTheory.BooneHigmanSimpleProblem
