import Mathlib.Combinatorics.SimpleGraph.Clique
import EvalTools.Markers

namespace LeanEval
namespace Combinatorics

open SimpleGraph

/-!
Finite Ramsey theorem for graphs, phrased as the existence of a finite complete graph whose edges,
under any red/blue colouring, contain either a red `r`-clique or a blue `s`-clique.

We encode a 2-colouring by a simple graph `G` on `Fin n`; the red edges are the edges of `G` and
the blue edges are the edges of `Gᶜ`.
-/

/-- The Ramsey property `IsRamsey r s n`: for every finite type `V` with at least `n` vertices and
every simple graph `G` on `V`, either `G` is not `r`-clique-free or its complement `Gᶜ` is not
`s`-clique-free. Quantifying over all such `V` makes the property transfer to induced subgraphs. -/
def IsRamsey (r s n : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    n ≤ Fintype.card V → ¬ G.CliqueFree r ∨ ¬ Gᶜ.CliqueFree s

/-! ### Graph-theoretic preliminaries -/

/-- The complete graph on a finite type `V` with `s ≤ #V` is not `s`-clique-free. -/
theorem top_not_cliqueFree {V : Type*} [Fintype V] {s : ℕ} (h : s ≤ Fintype.card V) :
    ¬ (⊤ : SimpleGraph V).CliqueFree s := by
  sorry

/-- Complement commutes with inducing on a set. -/
theorem induce_compl {V : Type*} (G : SimpleGraph V) (A : Set V) :
    (G.induce A)ᶜ = Gᶜ.induce A := by
  sorry

/-- A clique in an induced subgraph forces a clique in the ambient graph. -/
theorem induce_lift {V : Type*} (G : SimpleGraph V) (A : Set V) {k : ℕ}
    (h : ¬ (G.induce A).CliqueFree k) : ¬ G.CliqueFree k := by
  sorry

/-- An `r`-clique of an induced subgraph lifts to an `r`-clique of the ambient graph all of whose
vertices lie in the inducing set. -/
theorem induce_clique_lift {V : Type*} (G : SimpleGraph V) (A : Set V) {r : ℕ}
    {t : Finset A} (ht : (G.induce A).IsNClique r t) :
    ∃ t' : Finset V, G.IsNClique r t' ∧ ↑t' ⊆ A := by
  sorry

/-- If `v ∉ A`, `v` is adjacent to every vertex of `A`, and the subgraph induced on `A` is not
`r`-clique-free, then `G` is not `(r+1)`-clique-free. -/
theorem common_neighbor {V : Type*} (G : SimpleGraph V) (v : V) (A : Set V) {r : ℕ}
    (hv : v ∉ A) (hadj : ∀ a ∈ A, G.Adj v a)
    (h : ¬ (G.induce A).CliqueFree r) : ¬ G.CliqueFree (r + 1) := by
  sorry

/-- The neighbourhood and the complement-neighbourhood of a vertex partition the remaining
vertices. -/
theorem degree_split {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) :
    (G.neighborFinset v).card + (Gᶜ.neighborFinset v).card = Fintype.card V - 1 := by
  sorry

/-- Neighbourhood side of the recursion: a clique result on the subgraph induced by the
neighbourhood of `v` yields a clique result for `G` with the red clique grown by one. -/
theorem neighbor_side {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) {r m : ℕ}
    (h : ¬ (G.induce ↑(G.neighborFinset v)).CliqueFree r ∨
        ¬ (G.induce ↑(G.neighborFinset v))ᶜ.CliqueFree m) :
    ¬ G.CliqueFree (r + 1) ∨ ¬ Gᶜ.CliqueFree m := by
  sorry

/-- Complement-neighbourhood side of the recursion: the dual of `neighbor_side` applied to `Gᶜ`. -/
theorem neighbor_side_compl {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) {a b : ℕ}
    (h : ¬ (G.induce ↑(Gᶜ.neighborFinset v)).CliqueFree a ∨
        ¬ (G.induce ↑(Gᶜ.neighborFinset v))ᶜ.CliqueFree b) :
    ¬ G.CliqueFree a ∨ ¬ Gᶜ.CliqueFree (b + 1) := by
  sorry

/-! ### Base cases and symmetry -/

/-- Base case `r = 2`: `IsRamsey 2 s s` holds for every `s`. -/
theorem base (s : ℕ) : IsRamsey 2 s s := by
  sorry

/-- The Ramsey property is symmetric in its first two arguments. -/
theorem symm {r s n : ℕ} (h : IsRamsey r s n) : IsRamsey s r n := by
  sorry

/-- Base case `s = 2`: `IsRamsey r 2 r` holds for every `r`. -/
theorem base_right (r : ℕ) : IsRamsey r 2 r := by
  sorry

/-! ### Inductive step and conclusion -/

/-- The Ramsey property transfers to the subgraph induced on a large enough finite set. -/
theorem ramsey_induce {V : Type} (G : SimpleGraph V) (A : Finset V) {r' m' N : ℕ}
    (hN : N ≤ A.card) (h : IsRamsey r' m' N) :
    ¬ (G.induce ↑A).CliqueFree r' ∨ ¬ (G.induce ↑A)ᶜ.CliqueFree m' := by
  sorry

/-- Inductive step: `R(r+1, s) ≤ N₁`, `R(r, s+1) ≤ N₂` give `R(r+1, s+1) ≤ N₁ + N₂ + 1`. -/
theorem step {r s N₁ N₂ : ℕ} (h1 : IsRamsey (r + 1) s N₁) (h2 : IsRamsey r (s + 1) N₂) :
    IsRamsey (r + 1) (s + 1) (N₁ + N₂ + 1) := by
  sorry

/-- Existence of the Ramsey number: for all `r, s ≥ 2` there is an `n` with `IsRamsey r s n`. -/
theorem ramsey_exists {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) : ∃ n : ℕ, IsRamsey r s n := by
  sorry

/-- Finite Ramsey theorem for graphs: for all `r, s ≥ 2` there is an `n` such that every simple
graph on `Fin n` contains a red `r`-clique or a blue `s`-clique. -/
@[eval_problem]
theorem finite_graph_ramsey_theorem :
    ∀ r s : ℕ, 2 ≤ r → 2 ≤ s → ∃ n : ℕ, ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree r ∨ ¬ Gᶜ.CliqueFree s := by
  sorry

end Combinatorics
end LeanEval
