import Mathlib

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
  have hcard : Fintype.card (Fin s) ≤ Fintype.card V := by
    simpa [Fintype.card_fin] using h
  have hembed : Nonempty (Fin s ↪ V) :=
    Function.Embedding.nonempty_of_card_le hcard
  let f : Fin s ↪ V := hembed.some
  have h_cont : completeGraph (Fin s) ⊑ (⊤ : SimpleGraph V) :=
    (Embedding.completeGraph f).isContained
  exact IsContained.not_cliqueFree h_cont

/-- Complement commutes with inducing on a set. -/
theorem induce_compl {V : Type*} (G : SimpleGraph V) (A : Set V) :
    (G.induce A)ᶜ = Gᶜ.induce A := by
  ext a b
  simp [SimpleGraph.compl_adj, SimpleGraph.induce, SimpleGraph.comap, Subtype.ext_iff]

/-- A clique in an induced subgraph forces a clique in the ambient graph. -/
theorem induce_lift {V : Type*} (G : SimpleGraph V) (A : Set V) {k : ℕ}
    (h : ¬ (G.induce A).CliqueFree k) : ¬ G.CliqueFree k := by
  intro hG
  apply h
  have h_cont : G.induce A ⊑ G := (SimpleGraph.Embedding.induce A).isContained
  exact SimpleGraph.CliqueFree.comap h_cont hG

/-- An `r`-clique of an induced subgraph lifts to an `r`-clique of the ambient graph all of whose
vertices lie in the inducing set. -/
theorem induce_clique_lift {V : Type*} (G : SimpleGraph V) (A : Set V) {r : ℕ}
    {t : Finset A} (ht : (G.induce A).IsNClique r t) :
    ∃ t' : Finset V, G.IsNClique r t' ∧ ↑t' ⊆ A := by
  let f : A ↪ V := Function.Embedding.subtype (· ∈ A)
  have hmap : (SimpleGraph.map (⇑f) (G.induce A)).IsNClique r (Finset.map f t) :=
    ht.map (f := f)
  have hle : SimpleGraph.map (⇑f) (G.induce A) ≤ G := by
    intro u v h
    rcases (SimpleGraph.map_adj f (G.induce A) u v).mp h with ⟨x, y, hadj, hx, hy⟩
    have hGadj : G.Adj (x : V) (y : V) := (SimpleGraph.induce_adj (s := A)).mp hadj
    have hx' : (x : V) = u := by
      simpa [f, Function.Embedding.coe_subtype] using hx
    have hy' : (y : V) = v := by
      simpa [f, Function.Embedding.coe_subtype] using hy
    rw [hx', hy'] at hGadj
    exact hGadj
  have hGclique : G.IsNClique r (Finset.map f t) :=
    hmap.mono hle
  have hsub : (Finset.map f t : Set V) ⊆ A := by
    intro x hx
    rcases Finset.mem_map.mp hx with ⟨a, ha, rfl⟩
    exact a.property
  exact ⟨Finset.map f t, hGclique, hsub⟩

/-- If `v ∉ A`, `v` is adjacent to every vertex of `A`, and the subgraph induced on `A` is not
`r`-clique-free, then `G` is not `(r+1)`-clique-free. -/
theorem common_neighbor {V : Type*} (G : SimpleGraph V) (v : V) (A : Set V) {r : ℕ}
    (_hv : v ∉ A) (hadj : ∀ a ∈ A, G.Adj v a)
    (h : ¬ (G.induce A).CliqueFree r) : ¬ G.CliqueFree (r + 1) := by
  classical
  -- From non-r-clique-freeness, extract an r-clique t of (G.induce A)
  have h_exists : ∃ t : Finset A, (G.induce A).IsNClique r t := by
    by_contra hne
    apply h
    exact (not_exists.mp hne)
  rcases h_exists with ⟨t, ht⟩
  -- Lift it to an r-clique t' of G with t' ⊆ A
  rcases induce_clique_lift G A ht with ⟨t', ht', hsub⟩
  -- Every vertex of t' is adjacent to v
  have h_adj' : ∀ b ∈ t', G.Adj v b := by
    intro b hb
    have hbA : b ∈ A := hsub (by
      -- b ∈ (t' : Set V)
      simpa using hb)
    exact hadj b hbA
  -- Insert v into t' to get an (r+1)-clique
  have h_clique : G.IsNClique (r + 1) (insert v t') :=
    ht'.insert h_adj'
  -- Therefore G is not (r+1)-clique-free
  exact h_clique.not_cliqueFree

/-- The neighbourhood and the complement-neighbourhood of a vertex partition the remaining
vertices. -/
theorem degree_split {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) :
    (G.neighborFinset v).card + (Gᶜ.neighborFinset v).card = Fintype.card V - 1 := by
  have hdeg_card : (G.neighborFinset v).card = G.degree v := by
    simp
  have hdeg_compl_card : (Gᶜ.neighborFinset v).card = Gᶜ.degree v := by
    simp
  rw [hdeg_card, hdeg_compl_card]
  rw [SimpleGraph.degree_compl G v]
  have hdeg_lt : G.degree v < Fintype.card V :=
    SimpleGraph.degree_lt_card_verts (G := G) v
  omega

/-- Neighbourhood side of the recursion: a clique result on the subgraph induced by the
neighbourhood of `v` yields a clique result for `G` with the red clique grown by one. -/
theorem neighbor_side {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) {r m : ℕ}
    (h : ¬ (G.induce ↑(G.neighborFinset v)).CliqueFree r ∨
        ¬ (G.induce ↑(G.neighborFinset v))ᶜ.CliqueFree m) :
    ¬ G.CliqueFree (r + 1) ∨ ¬ Gᶜ.CliqueFree m := by
  set A := (G.neighborFinset v : Set V) with hA
  have hv : v ∉ A := by
    rw [hA]
    simp
  have hadj : ∀ a ∈ A, G.Adj v a := by
    rw [hA]
    intro a ha
    simpa using ha
  rcases h with (h | h)
  · left
    exact common_neighbor G v A hv hadj h
  · right
    have h_eq : (G.induce A)ᶜ = Gᶜ.induce A := induce_compl G A
    rw [h_eq] at h
    exact induce_lift Gᶜ A h

/-- Complement-neighbourhood side of the recursion: the dual of `neighbor_side` applied to `Gᶜ`. -/
theorem neighbor_side_compl {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) {a b : ℕ}
    (h : ¬ (G.induce ↑(Gᶜ.neighborFinset v)).CliqueFree a ∨
        ¬ (G.induce ↑(Gᶜ.neighborFinset v))ᶜ.CliqueFree b) :
    ¬ G.CliqueFree a ∨ ¬ Gᶜ.CliqueFree (b + 1) := by
  set A := ↑(Gᶜ.neighborFinset v) with hA
  have h' : ¬ (Gᶜ.induce A).CliqueFree b ∨ ¬ (Gᶜ.induce A)ᶜ.CliqueFree a := by
    rcases h with (h1 | h2)
    · right
      simpa [induce_compl Gᶜ A, compl_compl] using h1
    · left
      simpa [induce_compl G A] using h2
  have h_neighbor := neighbor_side Gᶜ v (r := b) (m := a) h'
  rcases h_neighbor with (h1 | h2)
  · right; exact h1
  · left
    simpa [compl_compl] using h2

/-! ### Base cases and symmetry -/

/-- Base case `r = 2`: `IsRamsey 2 s s` holds for every `s`. -/
theorem base (s : ℕ) : IsRamsey 2 s s := by
  intro V _ G hcard
  by_cases h : G.CliqueFree 2
  · right
    have hG_bot : G = ⊥ := (SimpleGraph.cliqueFree_two.mp h)
    subst hG_bot
    have h_top : (⊥ : SimpleGraph V)ᶜ = (⊤ : SimpleGraph V) := by simp
    rw [h_top]
    exact top_not_cliqueFree hcard
  · left
    exact h

/-- The Ramsey property is symmetric in its first two arguments. -/
theorem symm {r s n : ℕ} (h : IsRamsey r s n) : IsRamsey s r n := by
  intro V _ G hV
  have h' := h V Gᶜ hV
  rcases h' with (hGc | hGcc)
  · right; exact hGc
  · left
    rw [compl_compl (α := SimpleGraph V)] at hGcc
    exact hGcc

/-- Base case `s = 2`: `IsRamsey r 2 r` holds for every `r`. -/
theorem base_right (r : ℕ) : IsRamsey r 2 r :=
  symm (base r)

/-! ### Inductive step and conclusion -/

/-- The Ramsey property transfers to the subgraph induced on a large enough finite set. -/
theorem ramsey_induce {V : Type} (G : SimpleGraph V) (A : Finset V) {r' m' N : ℕ}
    (hN : N ≤ A.card) (h : IsRamsey r' m' N) :
    ¬ (G.induce ↑A).CliqueFree r' ∨ ¬ (G.induce ↑A)ᶜ.CliqueFree m' := by
  have hcard : N ≤ Fintype.card ({x // x ∈ (A : Set V)}) := by
    simpa using hN
  exact h {x // x ∈ (A : Set V)} (G.induce (A : Set V)) hcard

/-- Inductive step: `R(r+1, s) ≤ N₁`, `R(r, s+1) ≤ N₂` give `R(r+1, s+1) ≤ N₁ + N₂ + 1`. -/
theorem step {r s N₁ N₂ : ℕ} (h1 : IsRamsey (r + 1) s N₁) (h2 : IsRamsey r (s + 1) N₂) :
    IsRamsey (r + 1) (s + 1) (N₁ + N₂ + 1) := by
  intro V _ G hcard
  classical
    have hpos : 0 < Fintype.card V := by omega
    have h_nonempty : Nonempty V := (Fintype.card_pos_iff.mp hpos)
    obtain ⟨v⟩ := h_nonempty
    set A := G.neighborFinset v with hA
    set B := Gᶜ.neighborFinset v with hB
    have h_deg : A.card + B.card = Fintype.card V - 1 := degree_split G v
    have h_cases : N₂ ≤ A.card ∨ N₁ ≤ B.card := by
      have h_ineq : N₁ + N₂ ≤ A.card + B.card := by
        have hcard' : N₁ + N₂ + 1 ≤ Fintype.card V := hcard
        omega
      omega
    rcases h_cases with (hAcase | hBcase)
    · apply neighbor_side G v
      simpa [hA] using ramsey_induce G A hAcase h2
    · apply neighbor_side_compl G v
      simpa [hB] using ramsey_induce G B hBcase h1

/-- Existence of the Ramsey number: for all `r, s ≥ 2` there is an `n` with `IsRamsey r s n`. -/
theorem ramsey_exists {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) : ∃ n : ℕ, IsRamsey r s n := by
  have hsum : r + s ≤ r + s := le_refl _
  have hP : ∀ k : ℕ, (∀ r' s', 2 ≤ r' → 2 ≤ s' → r' + s' ≤ k → ∃ n, IsRamsey r' s' n) := by
    intro k
    refine Nat.strong_induction_on k ?_
    intro k IH r' s' hr' hs' hsum
    by_cases h2r : r' = 2
    · subst h2r; exact ⟨s', base s'⟩
    · by_cases h2s : s' = 2
      · subst h2s; exact ⟨r', base_right r'⟩
      · have hr3 : 3 ≤ r' := by omega
        have hs3 : 3 ≤ s' := by omega
        have hlt1 : r' + (s' - 1) < k := by omega
        have hlt2 : (r' - 1) + s' < k := by omega
        have h2sm1 : 2 ≤ s' - 1 := by omega
        have h2rm1 : 2 ≤ r' - 1 := by omega
        rcases IH (r' + (s' - 1)) hlt1 r' (s' - 1) hr' h2sm1 (by omega) with ⟨N₁, hN₁⟩
        rcases IH ((r' - 1) + s') hlt2 (r' - 1) s' h2rm1 hs' (by omega) with ⟨N₂, hN₂⟩
        have h_r_eq : (r' - 1) + 1 = r' := by omega
        have h_s_eq : (s' - 1) + 1 = s' := by omega
        have hN₁' : IsRamsey ((r' - 1) + 1) (s' - 1) N₁ := by
          rw [h_r_eq]; exact hN₁
        have hN₂' : IsRamsey (r' - 1) ((s' - 1) + 1) N₂ := by
          rw [h_s_eq]; exact hN₂
        refine ⟨N₁ + N₂ + 1, ?_⟩
        simpa [h_r_eq, h_s_eq] using step hN₁' hN₂'
  exact hP (r + s) r s hr hs hsum



end Combinatorics
end LeanEval
