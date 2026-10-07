module

public import ECSBM.Terminology

/-!
# The edge connectivity of a clique

Step 1 of Stage 1 starts from a `(k + 1)`-clique, and the paper applies Theorem 1 to it, which
needs the clique to be `k`-edge-connected. The published version uses this standard fact without
proof. Its arXiv version (arXiv:2502.03662v1, Case 1 of the proof of its theorem) proves it by
counting: if `d` vertices of the clique lie on one side of a cut and `k - d + 1` on the other,
then the `d (k - d + 1)` edges between them cross the cut, and `d (k - d + 1) - k =
(k - d) (d - 1) ≥ 0`. `ECSBM.isEdgeConnected_completeGraph` is proved by this argument.

`ECSBM.minCutSize_completeGraph` computes the minimum cut size of a complete graph. It shows that
`ECSBM.minCutSize` has its ordinary meaning on an example.
-/

@[expose] public section

namespace ECSBM

open SimpleGraph

variable {V : Type*}

/-- The arithmetic of the counting argument of the arXiv version: if `d` and `e` are positive
then `d * e ≥ d + e - 1`, because `(d - 1) (e - 1) ≥ 0` (with `d + e = k + 1`, this is
`d (k - d + 1) ≥ k`). -/
theorem add_sub_one_le_mul {d e : ℕ} (hd : 1 ≤ d) (he : 1 ≤ e) : d + e - 1 ≤ d * e := by
  sorry

/-- **The complete graph on `n` vertices is `(n - 1)`-edge-connected.** If `S` and its
complement are nonempty, with `d` and `e` vertices, the `d * e ≥ d + e - 1 = n - 1` edges between
them cross the cut (the counting argument of the arXiv version). -/
theorem isEdgeConnected_completeGraph [Finite V] :
    (completeGraph V).IsEdgeConnected (Nat.card V - 1) := by
  sorry

/-- The complete graph on `n + 2` vertices has minimum cut size `n + 1`: the edges at one vertex
form an edge cut with `n + 1` edges, and there is none smaller. -/
theorem minCutSize_completeGraph (n : ℕ) :
    minCutSize (completeGraph (Fin (n + 2))) = n + 1 := by
  sorry

end ECSBM
