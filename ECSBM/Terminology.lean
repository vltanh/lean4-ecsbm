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
* `ECSBM.minCutSize_mono` and `ECSBM.IsEdgeConnected.mono`: adding edges does not decrease the
  minimum cut size;
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
  constructor
  · intro hk u v s hs
    by_contra hnr
    -- the edges of `s` that are edges of `H` form an edge cut with fewer than `k` edges
    have hcut : IsEdgeCut H (s ∩ H.edgeSet) := by
      refine ⟨Set.inter_subset_right, fun hpre => hnr ?_⟩
      rw [deleteEdges_eq_inter_edgeSet]
      exact hpre u v
    have h₁ : minCutSize H ≤ (s ∩ H.edgeSet).encard := iInf₂_le _ hcut
    have h₂ : (s ∩ H.edgeSet).encard ≤ s.encard := Set.encard_le_encard Set.inter_subset_left
    exact absurd (hk.trans (h₁.trans h₂)) (not_le.mpr hs)
  · intro h
    refine le_iInf₂ fun F hF => ?_
    by_contra hlt
    exact hF.2 fun u v => h u v (not_le.mp hlt)

/-- The edges between `S` and its complement are the edges between the complement and `S`. -/
theorem crossingEdges_compl (H : SimpleGraph V) (S : Set V) :
    crossingEdges H Sᶜ = crossingEdges H S := by
  ext e
  simp only [crossingEdges, Set.mem_ofPred_eq, Set.mem_compl_iff, not_not]
  constructor
  · rintro ⟨he, x, hx, y, hy, rfl⟩
    exact ⟨he, y, hy, x, hx, Sym2.eq_swap⟩
  · rintro ⟨he, x, hx, y, hy, rfl⟩
    exact ⟨he, y, hy, x, hx, Sym2.eq_swap⟩

/-- Removing an edge cut `F` of `H` leaves a side `S`, with vertices on both sides of it, such
that every edge of `H` between `S` and its complement belongs to `F`: take for `S` the vertices
that remain joined to one vertex by a path. -/
theorem IsEdgeCut.exists_side {H : SimpleGraph V} {F : Set (Sym2 V)} (hF : IsEdgeCut H F) :
    ∃ S : Set V, S.Nonempty ∧ Sᶜ.Nonempty ∧ crossingEdges H S ⊆ F := by
  obtain ⟨-, hnp⟩ := hF
  simp only [Preconnected, not_forall] at hnp
  obtain ⟨a, b, hab⟩ := hnp
  refine ⟨{x | (H.deleteEdges F).Reachable a x}, ⟨a, Reachable.refl a⟩, ⟨b, hab⟩, ?_⟩
  rintro e ⟨he, x, hx, y, hy, rfl⟩
  by_contra hxy
  exact hy (hx.trans (Adj.reachable (deleteEdges_adj.mpr ⟨(H.mem_edgeSet).mp he, hxy⟩)))

/-- The edges between a set `S` of vertices and its complement form an edge cut, if both are
nonempty. -/
theorem isEdgeCut_crossingEdges (H : SimpleGraph V) {S : Set V} (hS : S.Nonempty)
    (hSc : Sᶜ.Nonempty) : IsEdgeCut H (crossingEdges H S) := by
  refine ⟨fun e he => he.1, fun hpre => ?_⟩
  obtain ⟨a, ha⟩ := hS
  obtain ⟨b, hb⟩ := hSc
  obtain ⟨w⟩ := hpre a b
  -- a walk that avoids the crossing edges and starts in `S` stays in `S`
  have key : ∀ (u v : V) (_ : (H.deleteEdges (crossingEdges H S)).Walk u v), u ∈ S → v ∈ S := by
    intro u v w
    induction w with
    | nil => exact id
    | cons hadj _ ih =>
      intro hu
      apply ih
      by_contra hv
      rw [deleteEdges_adj] at hadj
      exact hadj.2 ⟨(H.mem_edgeSet).mpr hadj.1, _, hu, _, hv, rfl⟩
  exact hb (key a b w ha)

/-- In a `k`-edge-connected graph, at least `k` edges join a set `S` of vertices to its
complement, if both are nonempty. -/
theorem IsEdgeConnected.le_encard_crossingEdges {H : SimpleGraph V} {k : ℕ}
    (h : H.IsEdgeConnected k) {S : Set V} (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) :
    (k : ℕ∞) ≤ (crossingEdges H S).encard :=
  ((le_minCutSize_iff H k).mpr h).trans (iInf₂_le _ (isEdgeCut_crossingEdges H hS hSc))

/-- Adding edges to a graph does not decrease its minimum cut size. -/
theorem minCutSize_mono {H H' : SimpleGraph V} (h : H ≤ H') : minCutSize H ≤ minCutSize H' := by
  refine le_iInf₂ fun F hF => ?_
  -- the edges of an edge cut of `H'` that are edges of `H` form an edge cut of `H`
  have hcut : IsEdgeCut H (F ∩ H.edgeSet) := by
    refine ⟨Set.inter_subset_right, fun hpre => hF.2 fun u v => ?_⟩
    have huv := hpre u v
    rw [← deleteEdges_eq_inter_edgeSet] at huv
    exact huv.mono (deleteEdges_mono h)
  exact (iInf₂_le _ hcut).trans (Set.encard_le_encard Set.inter_subset_left)

/-- Adding edges to a `k`-edge-connected graph leaves it `k`-edge-connected. -/
theorem IsEdgeConnected.mono {H H' : SimpleGraph V} {k : ℕ} (h : H.IsEdgeConnected k)
    (hle : H ≤ H') : H'.IsEdgeConnected k :=
  fun u v => (h u v).mono hle

/-- The minimum cut size of a graph is `0` exactly when the graph is not preconnected, that is,
when it has at least two connected components (a disconnected cluster, Section "Terminology"):
the empty set of edges is then an edge cut. -/
theorem minCutSize_eq_zero_iff (H : SimpleGraph V) : minCutSize H = 0 ↔ ¬ H.Preconnected := by
  constructor
  · intro h hpre
    have h₁ : ((1 : ℕ) : ℕ∞) ≤ minCutSize H :=
      (le_minCutSize_iff H 1).mpr (isEdgeConnected_one.mpr hpre)
    rw [h] at h₁
    exact absurd h₁ (by simp)
  · intro h
    refine le_antisymm ?_ bot_le
    have hcut : IsEdgeCut H ∅ := ⟨Set.empty_subset _, by rwa [deleteEdges_empty]⟩
    exact (iInf₂_le _ hcut).trans (by simp)

/-- A graph with at most one vertex has no edge cut: its minimum cut size is `⊤`. -/
theorem minCutSize_eq_top [Subsingleton V] (H : SimpleGraph V) : minCutSize H = ⊤ :=
  eq_top_iff.mpr (le_iInf₂ fun _ hF => (hF.2 Preconnected.of_subsingleton).elim)

/-- A finite graph with at least two vertices has an edge cut, all its edges: its minimum cut
size is finite. -/
theorem minCutSize_lt_top [Finite V] [Nontrivial V] (H : SimpleGraph V) : minCutSize H < ⊤ := by
  have hcut : IsEdgeCut H H.edgeSet := by
    refine ⟨subset_rfl, fun hpre => ?_⟩
    obtain ⟨a, b, hab⟩ := exists_pair_ne V
    rw [deleteEdges_edgeSet, sdiff_self] at hpre
    exact hab (reachable_bot.mp (hpre a b))
  exact (iInf₂_le _ hcut).trans_lt (Set.encard_lt_top_iff.mpr (Set.toFinite _))

end ECSBM
