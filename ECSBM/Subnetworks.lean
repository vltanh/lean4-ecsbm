module

public import ECSBM.Defs

/-!
# The clustered and the outlier subnetworks

Section "The EC-SBM network simulator" splits the vertices of the empirical network `G` into the
vertices of the non-singleton clusters and the outliers, the vertices of the singleton clusters.
This defines two subnetworks:

* the clustered subnetwork `G_c`, induced by the vertices that are not outliers
  (`ECSBM.clusteredSubnetwork`);
* the outlier subnetwork `G_out`, formed by removing all edges of `G_c` from `G`
  (Section "A three-stage generation of the synthetic network", `ECSBM.outlierSubnetwork`).

Section "The EC-SBM network simulator" describes the edges of `G_out` as those that have at least
one endpoint an outlier (`ECSBM.outlierSubnetwork_adj`), and notes that every edge of `G` is in
exactly one of the two subnetworks (`ECSBM.edge_mem_clustered_xor_outlier`). Both subnetworks are
graphs on all the vertices of `G` here: the outliers are isolated in `G_c`.
-/

@[expose] public section

namespace ECSBM

open SimpleGraph

variable {W : Type*}

/-- The outliers of a clustering: the vertices of its singleton clusters (Section
"Terminology"). -/
def outliers [Fintype W] [DecidableEq W] (𝒞 : Finpartition (Finset.univ : Finset W)) : Set W :=
  {v | {v} ∈ 𝒞.parts}

/-- The clustered subnetwork `G_c` of `G`, for the set `O` of outliers: the subnetwork induced by
the vertices that are not outliers, as a graph on all the vertices of `G`. -/
def clusteredSubnetwork (G : SimpleGraph W) (O : Set W) : SimpleGraph W :=
  (G.induce Oᶜ).map Subtype.val

/-- The outlier subnetwork `G_out` of `G`, for the set `O` of outliers: the subnetwork formed by
removing all edges of `G_c` from `G`. -/
def outlierSubnetwork (G : SimpleGraph W) (O : Set W) : SimpleGraph W :=
  G \ clusteredSubnetwork G O

/-- The edges of the outlier subnetwork are the edges of `G` with at least one endpoint an
outlier (Section "The EC-SBM network simulator"). -/
theorem outlierSubnetwork_adj (G : SimpleGraph W) (O : Set W) (u v : W) :
    (outlierSubnetwork G O).Adj u v ↔ G.Adj u v ∧ (u ∈ O ∨ v ∈ O) := by
  rw [outlierSubnetwork, sdiff_adj, clusteredSubnetwork, map_adj']
  constructor
  · rintro ⟨hG, hc⟩
    refine ⟨hG, ?_⟩
    by_contra h
    rw [not_or] at h
    exact hc ⟨hG.ne, ⟨u, h.1⟩, ⟨v, h.2⟩, hG, rfl, rfl⟩
  · rintro ⟨hG, h⟩
    refine ⟨hG, ?_⟩
    rintro ⟨-, a, b, -, rfl, rfl⟩
    rcases h with h | h
    · exact a.2 h
    · exact b.2 h

/-- "Every edge in `N` is in exactly one of these two subnetworks" (Section "The EC-SBM network
simulator"): the clustered subnetwork and the outlier subnetwork of the clustering `𝒞`. -/
theorem edge_mem_clustered_xor_outlier [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    (𝒞 : Finpartition (Finset.univ : Finset W)) {e : Sym2 W} (he : e ∈ G.edgeSet) :
    Xor (e ∈ (clusteredSubnetwork G (outliers 𝒞)).edgeSet)
      (e ∈ (outlierSubnetwork G (outliers 𝒞)).edgeSet) := by
  induction e using Sym2.ind with
  | _ u v =>
  by_cases hc : (clusteredSubnetwork G (outliers 𝒞)).Adj u v
  · exact Or.inl ⟨hc, fun ho => ho.2 hc⟩
  · exact Or.inr ⟨⟨he, hc⟩, hc⟩

end ECSBM
