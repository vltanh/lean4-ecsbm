module

public import ECSBM.Defs

/-!
# Edge cuts and the minimum cut size

Facts about the notions of Section "Terminology" that the paper uses without proof:

* `ECSBM.le_minCutSize_iff`: the minimum cut size of a graph is at least `k` exactly when the graph
  is `k`-edge-connected in Mathlib's sense (`SimpleGraph.IsEdgeConnected`): removing fewer than `k`
  edges leaves every two vertices joined by a path;
* `ECSBM.IsEdgeCut.exists_side`: removing an edge cut leaves a side `S`, with vertices on both
  sides of it, such that every edge between `S` and the rest of the vertices belongs to the cut;
* `ECSBM.IsEdgeConnected.le_encard_crossingEdges`: in a `k`-edge-connected graph, at least `k`
  edges cross every partition of the vertices into two nonempty parts;
* `ECSBM.minCutSize_mono`: adding edges does not decrease the minimum cut size;
* `ECSBM.minCutSize_eq_zero_iff`: the minimum cut size is `0` exactly for the graphs that are not
  preconnected;
* `ECSBM.minCutSize_eq_top` and `ECSBM.minCutSize_lt_top`: the minimum cut size is `⊤` exactly for
  graphs with at most one vertex (for finite graphs).
-/

@[expose] public section

namespace ECSBM

open SimpleGraph

variable {V : Type*}

/-- The edges of `H` between a set `S` of vertices and its complement. -/
def crossingEdges (H : SimpleGraph V) (S : Set V) : Set (Sym2 V) :=
  {e | e ∈ H.edgeSet ∧ ∃ x ∈ S, ∃ y ∉ S, e = s(x, y)}

/-- The minimum cut size of a graph is at least `k` exactly when the graph is `k`-edge-connected
in the sense of Mathlib: removing fewer than `k` edges leaves every two vertices joined by a
path. -/
theorem le_minCutSize_iff (H : SimpleGraph V) (k : ℕ) :
    (k : ℕ∞) ≤ minCutSize H ↔ H.IsEdgeConnected k := by
  sorry

/-- The edges between `S` and its complement are the edges between the complement and `S`. -/
theorem crossingEdges_compl (H : SimpleGraph V) (S : Set V) :
    crossingEdges H Sᶜ = crossingEdges H S := by
  sorry

/-- Removing an edge cut `F` of `H` leaves a side `S`, with vertices on both sides of it, such
that every edge of `H` between `S` and its complement belongs to `F`: take for `S` the vertices
that remain joined to one vertex by a path. -/
theorem IsEdgeCut.exists_side {H : SimpleGraph V} {F : Set (Sym2 V)} (hF : IsEdgeCut H F) :
    ∃ S : Set V, S.Nonempty ∧ Sᶜ.Nonempty ∧ crossingEdges H S ⊆ F := by
  sorry

/-- The edges between a set `S` of vertices and its complement form an edge cut, if both are
nonempty. -/
theorem isEdgeCut_crossingEdges (H : SimpleGraph V) {S : Set V} (hS : S.Nonempty)
    (hSc : Sᶜ.Nonempty) : IsEdgeCut H (crossingEdges H S) := by
  sorry

/-- In a `k`-edge-connected graph, at least `k` edges join a set `S` of vertices to its
complement, if both are nonempty. -/
theorem IsEdgeConnected.le_encard_crossingEdges {H : SimpleGraph V} {k : ℕ}
    (h : H.IsEdgeConnected k) {S : Set V} (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) :
    (k : ℕ∞) ≤ (crossingEdges H S).encard := by
  sorry

/-- Adding edges to a graph does not decrease its minimum cut size. -/
theorem minCutSize_mono {H H' : SimpleGraph V} (h : H ≤ H') : minCutSize H ≤ minCutSize H' := by
  sorry

/-- The minimum cut size of a graph is `0` exactly when the graph is not preconnected, that is,
when it has at least two connected components (a disconnected cluster, Section "Terminology"):
the empty set of edges is then an edge cut. -/
theorem minCutSize_eq_zero_iff (H : SimpleGraph V) : minCutSize H = 0 ↔ ¬ H.Preconnected := by
  sorry

/-- A graph with at most one vertex has no edge cut: its minimum cut size is `⊤`. -/
theorem minCutSize_eq_top [Subsingleton V] (H : SimpleGraph V) : minCutSize H = ⊤ := by
  sorry

/-- A finite graph with at least two vertices has an edge cut, all its edges: its minimum cut
size is finite. -/
theorem minCutSize_lt_top [Finite V] [Nontrivial V] (H : SimpleGraph V) : minCutSize H < ⊤ := by
  sorry

end ECSBM
