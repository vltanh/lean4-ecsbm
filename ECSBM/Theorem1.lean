module

public import ECSBM.Terminology

/-!
# Theorem 1: Step 1 of Stage 1 outputs a `k`-edge-connected spanning subnetwork

Section "Theoretical guarantees" of the paper. Step 1 of Stage 1 builds, for a cluster with
vertex set `V` and desired edge connectivity `k`, a spanning subnetwork: it starts from a
`(k + 1)`-clique and adds the remaining vertices one at a time, each made adjacent to exactly `k`
vertices already present. Theorem 1 shows that the output is `k`-edge-connected, whatever
`k`-edge-connected graph `N₀` the procedure starts from. A run of the procedure from `N₀` is an
`ECSBM.Step1Run`.

The proof follows the paper's. Let `E₀` be an edge cut of the output `G`, and `(S, T)` the two
sides that removing it leaves, so that every edge of `G` between `S` and `T` lies in `E₀`
(`ECSBM.IsEdgeCut.exists_side`).

* Case 1: the vertex set `V₀` of `N₀` lies on one side, say `S`. The first vertex of `T` to be
  added was made adjacent to `k` vertices already present, which all lie in `S`; these `k` edges
  cross the cut (`ECSBM.Step1Run.case1`).
* Case 2: `V₀` meets both sides. Since `N₀` is `k`-edge-connected, at least `k` of its edges join
  `S ∩ V₀` to `T ∩ V₀`, and they cross the cut (`ECSBM.Step1Run.case2`).
-/

@[expose] public section

namespace ECSBM

open SimpleGraph

/-- **Theorem 1** (`FPar1`). Let `C` be a cluster on vertex set `V`, and let `k` be the desired
edge connectivity. Let `N₀` be any graph on the vertex set `V₀ ⊆ V` that is `k`-edge-connected.
Then after completing Step 1 of Stage 1 for this cluster, the output synthetic network `G` for `C`
has every node in `V` and is `k`-edge-connected.

A run `r` of Step 1 started from `N₀` adds every vertex of `V` outside `V₀`: the first conjunct
says so, and holds by construction. Its output `r.output` is a graph on all of `V` (the paper's
"has every node in `V`"), and the second conjunct says that it is `k`-edge-connected.

Each added vertex gets exactly `k` neighbours already present, as Section "Theoretical
guarantees" says. Section "The EC-SBM network simulator" makes a vertex adjacent to
`min{k, |N₀|}` vertices of the growing subnetwork instead (printed `max{k, |N₀|}`, a misprint);
the two rules agree once `k` vertices are present, which the proof's claim `|N₀| ≥ k + 1` is meant
to ensure. That claim needs `N₀` to have at least two vertices
(`ECSBM.IsEdgeConnected.add_one_le_card`): a graph with one vertex has no edge cut, so it is
`k`-edge-connected for every `k`. From a one-vertex `N₀` and with `k ≥ 2`, no vertex can be added
with exactly `k` neighbours. The `min` rule would add vertices, and its output is `k`-edge-connected
when `V` has more than `k` vertices (the first `k + 1` vertices form a clique,
`ECSBM.CliqueStep1Run.isEdgeConnected`), but not when `V` has at most `k` vertices: for
`V = {a, b}` and `k = 2` it is a single edge. In EC-SBM, `k` is less than the number of vertices of
the cluster. -/
theorem theorem1 {V : Type*} {k : ℕ} (r : Step1Run V k) (hN₀ : r.N₀.IsEdgeConnected k) :
    (∀ v : V, v ∈ r.V₀ ∨ ∃ j, (r.order j : V) = v) ∧ r.output.IsEdgeConnected k := by
  sorry

end ECSBM
