module

public import ECSBM.CliqueStep1

/-!
# Beyond the paper: Step 1 gives exactly the desired edge connectivity

This module is not part of the paper. Theorem 1 shows that the spanning subnetwork that Step 1 of
Stage 1 builds has minimum cut size at least `k`. It is in fact exactly `k`, as soon as the
cluster has at least two vertices: the last vertex added has exactly `k` neighbours, since no
vertex added after it is made adjacent to it, so the edges at it form an edge cut with `k` edges.

* `ECSBM.Step1Run.minCutSize_output_eq`: for a run of Step 1 started from a `k`-edge-connected
  graph that adds at least one vertex, on at least two vertices.
* `ECSBM.CliqueStep1Run.minCutSize_output_eq`: for Step 1 as the paper runs it, on a cluster with
  at least two vertices and more than `k`. The last vertex processed may then belong to the
  `(k + 1)`-clique, when no vertex follows it.

So whatever excess the synthetic clusters of EC-SBM show over their desired edge connectivity comes
from the later stages; the paper observes such an excess in Section "Results of Experiment 2".
-/

@[expose] public section

namespace ECSBM

open SimpleGraph

/-- **Beyond the paper.** A run of Step 1 started from a `k`-edge-connected graph that adds at least
one vertex, on at least two vertices, outputs a graph with minimum cut size exactly `k`: at least
`k` by Theorem 1, and at most `k` because the edges at the last vertex added, which has exactly `k`
neighbours, form an edge cut. -/
theorem Step1Run.minCutSize_output_eq {V : Type*} [Nontrivial V] {k : ℕ} (r : Step1Run V k)
    (hN₀ : r.N₀.IsEdgeConnected k) (hp : 0 < r.p) : minCutSize r.output = k := by
  apply le_antisymm
  · set last : Fin r.p := ⟨r.p - 1, by omega⟩ with hlast
    set v : V := (r.order last : V) with hv
    obtain ⟨w, hw⟩ := exists_ne v
    have hcut := isEdgeCut_crossingEdges r.output (S := {v}) (Set.singleton_nonempty v)
      ⟨w, by simpa using hw⟩
    refine (iInf₂_le _ hcut).trans ?_
    -- every edge at `v` joins it to a vertex it was made adjacent to when it was added
    have hsub : crossingEdges r.output {v} ⊆ (fun u => s(v, u)) '' (r.nbrs last : Set V) := by
      rintro e ⟨he, x, hx, y, -, rfl⟩
      rw [Set.mem_singleton_iff] at hx
      subst hx
      rcases (sup_adj _ _ _ _).mp ((r.output.mem_edgeSet).mp he) with h | h
      · -- an edge of `N₀` has its endpoints in `V₀`, and `v` is not in `V₀`
        obtain ⟨-, a, -, -, ha, -⟩ := (map_adj' _ _ _ _).mp h
        have hvV : v ∈ r.V₀ := ha ▸ a.2
        exact absurd hvV (r.order last).2
      · obtain ⟨⟨j, u, hu, he'⟩, -⟩ := (fromEdgeSet_adj _).mp h
        rcases Sym2.eq_iff.mp he' with ⟨h₁, h₂⟩ | ⟨h₁, -⟩
        · -- the edge was added with `v`
          have hj : j = last := r.order.injective (Subtype.ext h₁.symm)
          subst hj
          obtain rfl : y = u := h₂
          exact ⟨y, hu, rfl⟩
        · -- the edge was added with a later vertex, but none follows `v`
          rcases r.nbrs_present j u hu with h₀ | ⟨i, hij, hi⟩
          · have hvV : v ∈ r.V₀ := h₁ ▸ h₀
            exact absurd hvV (r.order last).2
          · have hi' : i = last := r.order.injective (Subtype.ext (hi.trans h₁.symm))
            subst hi'
            have := j.isLt
            have : r.p - 1 < (j : ℕ) := hij
            omega
    refine (Set.encard_le_encard hsub).trans ((Set.encard_image_le _ _).trans ?_)
    rw [Set.encard_coe_eq_coe_finsetCard, r.card_nbrs last]
  · exact (le_minCutSize_iff _ _).mpr (theorem1 r hN₀).2

/-- **Beyond the paper.** The spanning subnetwork that Step 1 builds, as the paper runs it, on a
cluster with at least two vertices and more than `k`, has minimum cut size exactly `k`: at least
`k` (Fig. 3, by Theorem 1), and at most `k` because the last vertex processed is adjacent to
exactly `min k (|V| - 1) = k` vertices. -/
theorem CliqueStep1Run.minCutSize_output_eq {V : Type*} [Fintype V] [Nontrivial V] {k : ℕ}
    (r : CliqueStep1Run V k) (hk : k < Fintype.card V) : minCutSize r.output = k := by
  apply le_antisymm
  · set n := Fintype.card V with hn
    set last : Fin n := ⟨n - 1, by omega⟩ with hlast
    set v : V := r.order last with hv
    obtain ⟨w, hw⟩ := exists_ne v
    have hcut := isEdgeCut_crossingEdges r.output (S := {v}) (Set.singleton_nonempty v)
      ⟨w, by simpa using hw⟩
    refine (iInf₂_le _ hcut).trans ?_
    -- every edge at `v` joins it to a vertex it was made adjacent to when it was processed
    have hsub : crossingEdges r.output {v} ⊆ (fun u => s(v, u)) '' (r.nbrs last : Set V) := by
      rintro e ⟨he, x, hx, y, -, rfl⟩
      rw [Set.mem_singleton_iff] at hx
      subst hx
      obtain ⟨⟨j, u, hu, he'⟩, -⟩ := (fromEdgeSet_adj _).mp he
      rcases Sym2.eq_iff.mp he' with ⟨h₁, h₂⟩ | ⟨h₁, -⟩
      · -- the edge was added with `v`
        have hj : j = last := r.order.injective h₁.symm
        subst hj
        obtain rfl : y = u := h₂
        exact ⟨y, hu, rfl⟩
      · -- the edge was added with a later vertex, but none follows `v`
        obtain ⟨i, hij, hi⟩ := r.nbrs_present j u hu
        have hi' : i = last := r.order.injective (hi.trans h₁.symm)
        subst hi'
        have := j.isLt
        have : n - 1 < (j : ℕ) := hij
        omega
    refine (Set.encard_le_encard hsub).trans ((Set.encard_image_le _ _).trans ?_)
    rw [Set.encard_coe_eq_coe_finsetCard, r.card_nbrs last]
    simp only [last, Nat.cast_le]
    omega
  · exact (le_minCutSize_iff _ _).mpr (r.isEdgeConnected hk)

end ECSBM
