module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Order.Partition.Finpartition

/-!
# The definitions that the main theorems use

This module holds the definitions that the statements of Theorems 1 and 2 need, between the two
marker lines. `scripts/sync_challenge_defs.py` copies the block word for word into
`Challenge.lean`, which may not import the project, so that the Challenge and the library use the
same definitions.

* `ECSBM.IsEdgeCut`, `ECSBM.minCutSize`: edge cuts and the minimum cut size of a graph (Section
  "Terminology" of the paper).
* `ECSBM.Step1Run`: a run of Step 1 of Stage 1 on one cluster, started from any graph `N₀`
  (Theorem 1), and `ECSBM.Step1Run.output`, the graph it outputs.
* `ECSBM.Run`: a run of EC-SBM on a clustered network (Theorem 2), with the networks after each
  stage, and `ECSBM.Run.output`, the synthetic network it returns.
-/

@[expose] public section

-- BEGIN SHARED DEFINITIONS
namespace ECSBM

open SimpleGraph

/-! ### Edge cuts and the minimum cut size (Section "Terminology") -/

/-- An **edge cut** of a graph `H` (Section "Terminology"): a set `F` of edges of `H` whose
removal, keeping the endpoints, disconnects `H` into two or more parts. -/
def IsEdgeCut {V : Type*} (H : SimpleGraph V) (F : Set (Sym2 V)) : Prop :=
  F ⊆ H.edgeSet ∧ ¬ (H.deleteEdges F).Preconnected

/-- The **minimum cut size** of a graph `H` (Section "Terminology"): the size of a minimum edge
cut of `H`, or `⊤` when `H` has no edge cut, that is, when `H` has at most one vertex. The minimum
cut size of a cluster is that of the subgraph that its vertices induce. A graph is
`k`-edge-connected when its minimum cut size is at least `k`; the theorem `le_minCutSize_iff`
shows that this is Mathlib's `SimpleGraph.IsEdgeConnected`. -/
noncomputable def minCutSize {V : Type*} (H : SimpleGraph V) : ℕ∞ :=
  ⨅ (F : Set (Sym2 V)) (_ : IsEdgeCut H F), F.encard

/-! ### Step 1 of Stage 1, started from any graph (Theorem 1) -/

/-- A run of **Step 1 of Stage 1** of EC-SBM on a cluster with vertex set `V` and desired edge
connectivity `k`, started from a graph `N₀` on a vertex set `V₀ ⊆ V` (Section "Theoretical
guarantees" and Theorem 1). The vertices of `V` outside `V₀` are added one at a time, in the order
`order 0, order 1, …, order (p - 1)`, and the vertex `order j` is made adjacent to the `k`
vertices of `nbrs j`, which are already present: each lies in `V₀` or was added before
`order j`. The choices of the order and of the neighbours are arbitrary. Each added vertex gets
exactly `k` neighbours, as Section "Theoretical guarantees" says; so there is no run that adds a
vertex while fewer than `k` vertices are present. -/
structure Step1Run (V : Type*) (k : ℕ) where
  /-- The vertex set of the initial graph. -/
  V₀ : Set V
  /-- The initial graph, on the vertex set `V₀`. -/
  N₀ : SimpleGraph V₀
  /-- The number of vertices added to the initial graph. -/
  p : ℕ
  /-- The order in which the vertices outside `V₀` are added: `order j` is added `j`-th. -/
  order : Fin p ≃ (V₀ᶜ : Set V)
  /-- The vertices that `order j` is made adjacent to. -/
  nbrs : Fin p → Finset V
  /-- Each of them is already present when `order j` is added. -/
  nbrs_present : ∀ j, ∀ u ∈ nbrs j, u ∈ V₀ ∨ ∃ i < j, (order i : V) = u
  /-- There are exactly `k` of them. -/
  card_nbrs : ∀ j, (nbrs j).card = k

/-- The graph that a run of Step 1 outputs: the graph on all of `V` whose edges are the edges of
`N₀` and, for each `j`, the edges joining `order j` to the vertices of `nbrs j`. -/
def Step1Run.output {V : Type*} {k : ℕ} (r : Step1Run V k) : SimpleGraph V :=
  r.N₀.map Subtype.val ⊔ fromEdgeSet {e | ∃ j, ∃ u ∈ r.nbrs j, e = s((r.order j : V), u)}

/-! ### The three stages of EC-SBM (Theorem 2) -/

/-- The non-singleton clusters of a clustering `𝒞` of the vertices `W` of a network: the clusters
of the clustered subnetwork. The vertices of the other clusters, which are singletons, are the
outliers (Section "Terminology"). -/
def nonsingletonClusters {W : Type*} [Fintype W] [DecidableEq W]
    (𝒞 : Finpartition (Finset.univ : Finset W)) : Finset (Finset W) :=
  𝒞.parts.filter fun C ↦ 1 < C.card

/-- The desired edge connectivity of a cluster `C` of the empirical network `G`: the minimum cut
size of `C` in `G` (Stage 1). It is finite when `C` has at least two vertices, the only case in
which it is used; for a singleton cluster the minimum cut size is `⊤`, and this is `0`. -/
noncomputable def desiredConnectivity {W : Type*} (G : SimpleGraph W) (C : Finset W) : ℕ :=
  (minCutSize (G.induce (C : Set W))).toNat

/-- Adding the edges of a multigraph `M` to a graph `H`, and then removing the excess edges: every
self-loop, and all but one edge of every set of parallel edges (Steps 2a and 2b of Stage 1, and
Stage 2). The multigraph is the multiset of its edges, an edge `s(v, v)` being a self-loop. -/
def addThenSimplify {W : Type*} (H : SimpleGraph W) (M : Multiset (Sym2 W)) : SimpleGraph W :=
  fromEdgeSet (H.edgeSet ∪ {e | e ∈ M})

/-- A run of **EC-SBM** on the clustered empirical network `(G, 𝒞)` (Sections "The EC-SBM network
simulator" and "A three-stage generation of the synthetic network"). The synthetic network has
the vertices `W` of `G`, and its clustering is `𝒞`. A run consists of:

* Stage 1, Step 1: for each non-singleton cluster `C`, a run of Step 1 on the vertices of `C` with
  the desired edge connectivity of `C`, started from any graph;
* Stage 1, Step 2a: the multigraph that SBM generates with the updated parameters, any multigraph;
* Stage 2: the multigraph that SBM generates for the outlier subnetwork, any multigraph;
* Stage 3: the edges that degree correction adds, any edges.

The model does not restrict what SBM generates or which edges degree correction adds, so it
covers every run of EC-SBM. -/
structure Run {W : Type*} [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    (𝒞 : Finpartition (Finset.univ : Finset W)) where
  /-- Stage 1, Step 1: a run of Step 1 on each non-singleton cluster `C`. -/
  step1 : ∀ C ∈ nonsingletonClusters 𝒞, Step1Run (C : Set W) (desiredConnectivity G C)
  /-- Stage 1, Step 2a: the multigraph that SBM generates. -/
  stage1SBM : Multiset (Sym2 W)
  /-- Stage 2: the multigraph that SBM generates for the outlier subnetwork. -/
  stage2SBM : Multiset (Sym2 W)
  /-- Stage 3: the edges that degree correction adds. -/
  stage3 : SimpleGraph W

namespace Run

variable {W : Type*} [Fintype W] [DecidableEq W] {G : SimpleGraph W}
  {𝒞 : Finpartition (Finset.univ : Finset W)}

/-- The result of Step 1 of Stage 1 (`N₀` in the proof of Theorem 2): the union of the spanning
subnetworks that Step 1 generates for the non-singleton clusters. -/
noncomputable def step1Output (r : Run G 𝒞) : SimpleGraph W :=
  ⨆ (C) (hC : C ∈ nonsingletonClusters 𝒞), (r.step1 C hC).output.map Subtype.val

/-- The result of Stage 1 (`N₁` in the proof of Theorem 2), the synthetic clustered subnetwork:
Step 2a adds the multigraph that SBM generates, and Step 2b removes the excess edges. -/
noncomputable def stage1Output (r : Run G 𝒞) : SimpleGraph W :=
  addThenSimplify r.step1Output r.stage1SBM

/-- The result of Stage 2, the partially complete synthetic network: the synthetic outlier
subnetwork that SBM generates is added, and the excess edges are removed. -/
noncomputable def stage2Output (r : Run G 𝒞) : SimpleGraph W :=
  addThenSimplify r.stage1Output r.stage2SBM

/-- The synthetic network that EC-SBM returns: Stage 3 adds edges to improve the fit to the
degree sequence. -/
noncomputable def output (r : Run G 𝒞) : SimpleGraph W :=
  r.stage2Output ⊔ r.stage3

end Run

end ECSBM
-- END SHARED DEFINITIONS
