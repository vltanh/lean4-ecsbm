module

public import ECSBM.Clique
public import ECSBM.Theorem1
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Runs exist

The hypotheses of Theorems 1 and 2 can be met, so neither theorem is vacuous.

* `ECSBM.IsEdgeConnected.add_one_le_card`: a `k`-edge-connected graph with at least two vertices
  has at least `k + 1` vertices. The proof of Theorem 1 states this for `N₀` ("`N₀` is
  `k`-edge-connected, from which it follows that `|N₀| ≥ k + 1`"), without the condition that `N₀`
  has at least two vertices, which it needs: a single vertex is `k`-edge-connected for every `k`.
* `ECSBM.minCutSize_le_card_sub_one`: the minimum cut size of a graph with `n ≥ 2` vertices is at
  most `n - 1`, so the desired edge connectivity `k` of a non-singleton cluster `C` satisfies
  `k + 1 ≤ |C|`, and the `(k + 1)`-clique that Step 1 starts from fits in `C`.
* `ECSBM.Step1Run.ofSubset`: a run of Step 1 from any graph `N₀` on `V₀`, in which every vertex
  added is made adjacent to the same `k` vertices of `V₀`; `ECSBM.exists_step1Run_clique` starts
  it from a `(k + 1)`-clique.
* `ECSBM.Run.exists_clique`: EC-SBM can be run on every clustered network, with Step 1 started in
  every non-singleton cluster from a `(k + 1)`-clique, as in the paper; these initial graphs are
  `k`-edge-connected, so Theorem 2 applies to the run.
-/

@[expose] public section

namespace ECSBM

open SimpleGraph

/-- A `k`-edge-connected graph with at least two vertices has at least `k + 1` vertices: each
vertex has at least `k` neighbours. -/
theorem IsEdgeConnected.add_one_le_card {V : Type*} [Finite V] {H : SimpleGraph V} {k : ℕ}
    (h : H.IsEdgeConnected k) (hV : 2 ≤ Nat.card V) : k + 1 ≤ Nat.card V := by
  sorry

/-- The minimum cut size of a graph with `n ≥ 2` vertices is at most `n - 1`. -/
theorem minCutSize_le_card_sub_one {V : Type*} [Finite V] [Nontrivial V] (H : SimpleGraph V) :
    minCutSize H ≤ (Nat.card V - 1 : ℕ) := by
  sorry

/-- A run of Step 1 started from the graph `N₀` on `V₀`, in which every vertex added is made
adjacent to the `k` vertices of a set `S ⊆ V₀`, which are present from the start. -/
noncomputable def Step1Run.ofSubset {V : Type*} (V₀ : Set V) [Finite (V₀ᶜ : Set V)]
    (N₀ : SimpleGraph V₀) {k : ℕ} (S : Finset V) (hS : (S : Set V) ⊆ V₀) (hk : S.card = k) :
    Step1Run V k where
  V₀ := V₀
  N₀ := N₀
  p := Nat.card (V₀ᶜ : Set V)
  order := (Finite.equivFin _).symm
  nbrs := fun _ => S
  nbrs_present := fun _ _ hu => Or.inl (hS hu)
  card_nbrs := fun _ => hk

/-- On a vertex set with more than `k` vertices, there is a run of Step 1 started from a complete
graph on `k + 1` vertices, which is `k`-edge-connected. -/
theorem exists_step1Run_clique {V : Type*} [Finite V] {k : ℕ} (hk : k + 1 ≤ Nat.card V) :
    ∃ r : Step1Run V k, r.V₀.ncard = k + 1 ∧ r.N₀ = ⊤ ∧ r.N₀.IsEdgeConnected k := by
  sorry

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The desired edge connectivity `k` of a non-singleton cluster `C` satisfies `k + 1 ≤ |C|`, so
the `(k + 1)`-clique that Step 1 starts from fits in `C`. -/
theorem desiredConnectivity_add_one_le {G : SimpleGraph W}
    {𝒞 : Finpartition (Finset.univ : Finset W)} {C : Finset W}
    (hC : C ∈ nonsingletonClusters 𝒞) : desiredConnectivity G C + 1 ≤ C.card := by
  sorry

/-- EC-SBM can be run on every clustered network `(G, 𝒞)`, with Step 1 started, in every
non-singleton cluster `C`, from a complete graph on `k + 1` vertices of `C`, `k` being the desired
edge connectivity of `C`, as in the paper. These initial graphs are `k`-edge-connected, so the run
meets the hypothesis of Theorem 2. -/
theorem Run.exists_clique (G : SimpleGraph W) (𝒞 : Finpartition (Finset.univ : Finset W)) :
    ∃ r : Run G 𝒞, ∀ C (hC : C ∈ nonsingletonClusters 𝒞),
      (r.step1 C hC).V₀.ncard = desiredConnectivity G C + 1 ∧ (r.step1 C hC).N₀ = ⊤ ∧
        (r.step1 C hC).N₀.IsEdgeConnected (desiredConnectivity G C) := by
  sorry

end ECSBM
