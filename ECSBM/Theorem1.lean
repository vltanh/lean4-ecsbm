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

The paper takes `E₀` to be a minimum edge cut; the argument works for every edge cut. It also
disposes first of the case where `N₀` contains all of `V`, which Case 2 covers.
-/

@[expose] public section

namespace ECSBM

open SimpleGraph

namespace Step1Run

variable {V : Type*} {k : ℕ} (r : Step1Run V k)

/-- Every vertex of `V` is in `V₀` or is added at some step: the run adds all the vertices of
`V` outside `V₀`. -/
theorem mem_V₀_or_added (v : V) : v ∈ r.V₀ ∨ ∃ j, (r.order j : V) = v := by
  by_cases hv : v ∈ r.V₀
  · exact Or.inl hv
  · exact Or.inr ⟨r.order.symm ⟨v, hv⟩, by simp⟩

/-- The vertex added `j`-th is adjacent, in the output, to the vertices chosen for it. -/
theorem output_adj_nbrs {j : Fin r.p} {u : V} (hu : u ∈ r.nbrs j) :
    r.output.Adj (r.order j : V) u := by
  refine (sup_adj _ _ _ _).mpr (Or.inr ((fromEdgeSet_adj _).mpr ⟨⟨j, u, hu, rfl⟩, ?_⟩))
  rcases r.nbrs_present j u hu with h | ⟨i, hij, rfl⟩
  · exact fun heq => (r.order j).2 (heq ▸ h)
  · exact fun heq => hij.ne' (r.order.injective (Subtype.ext heq))

/-- The edges of `N₀` are edges of the output. -/
theorem output_adj_of_N₀ {a b : r.V₀} (h : r.N₀.Adj a b) : r.output.Adj (a : V) b :=
  (sup_adj _ _ _ _).mpr (Or.inl (map_adj_apply' h (fun hab => h.ne (Subtype.ext hab))))

/-- **Case 1 of the proof of Theorem 1.** If `V₀` lies on the side `S` of a cut and the other side
`T` is nonempty, at least `k` edges of the output cross the cut. Let `v ∈ T` be the first vertex of
`T` to be added. The `k` vertices it was made adjacent to were present before it, so they lie in
`V₀ ⊆ S` or were added before `v`, hence also lie in `S`; the edges from `v` to them join `v` to
`S`. (The paper says that `v` has exactly `k` neighbours in `S`; it may have more, since vertices
of `S` added later may be made adjacent to `v`, but these `k` suffice.) -/
theorem case1 {S : Set V} (hV₀ : r.V₀ ⊆ S) (hT : Sᶜ.Nonempty) :
    (k : ℕ∞) ≤ (crossingEdges r.output S).encard := by
  classical
  obtain ⟨t, ht⟩ := hT
  have htV : t ∉ r.V₀ := fun h => ht (hV₀ h)
  -- the steps that add a vertex of `T`, and the first of them
  set J : Finset (Fin r.p) := Finset.univ.filter fun j => (r.order j : V) ∉ S with hJdef
  have hJ : J.Nonempty := ⟨r.order.symm ⟨t, htV⟩, by simpa [J] using ht⟩
  set j := J.min' hJ
  have hjS : (r.order j : V) ∉ S := (Finset.mem_filter.mp (J.min'_mem hJ)).2
  -- the vertices present when `order j` is added lie in `S`
  have hnbrs : ∀ u ∈ r.nbrs j, u ∈ S := by
    intro u hu
    rcases r.nbrs_present j u hu with h | ⟨i, hij, rfl⟩
    · exact hV₀ h
    · by_contra hiS
      exact absurd (J.min'_le i (by simp [J, hiS])) (not_le.mpr hij)
  set v : V := ((r.order j : (r.V₀ᶜ : Set V)) : V)
  -- the edges of the output joining `v` to `S` cross the cut
  set EvS : Set (Sym2 V) := {e | ∃ v' ∈ S, r.output.Adj v v' ∧ e = s(v, v')}
  have hEvS : EvS ⊆ crossingEdges r.output S := by
    rintro e ⟨v', hv', hadj, rfl⟩
    exact ⟨(r.output.mem_edgeSet).mpr hadj, v', hv', v, hjS, Sym2.eq_swap⟩
  -- and there are at least `k` of them: the edges to the vertices chosen for `v`
  have hmaps : Set.MapsTo (fun u => s(v, u)) (r.nbrs j : Set V) EvS :=
    fun u hu => ⟨u, hnbrs u hu, r.output_adj_nbrs hu, rfl⟩
  have hinj : Set.InjOn (fun u => s(v, u)) (r.nbrs j : Set V) :=
    fun _ _ _ _ hab => Sym2.congr_right.mp hab
  calc (k : ℕ∞) = ((r.nbrs j : Set V)).encard := by
        rw [Set.encard_coe_eq_coe_finsetCard, r.card_nbrs j]
    _ ≤ EvS.encard := Set.encard_le_encard_of_injOn hmaps hinj
    _ ≤ _ := Set.encard_le_encard hEvS

/-- **Case 2 of the proof of Theorem 1.** If `V₀` meets both sides `S` and `T` of a cut, then
`(S ∩ V₀, T ∩ V₀)` is a cut of `N₀`. Since `N₀` is `k`-edge-connected, at least `k` of its edges
join `S ∩ V₀` to `T ∩ V₀`, and they are edges of the output that cross the cut. (The paper writes
"Since `V₀` is `k`-edge connected" for `N₀`.) -/
theorem case2 (hN₀ : r.N₀.IsEdgeConnected k) {S : Set V} (hS : ∃ x ∈ r.V₀, x ∈ S)
    (hT : ∃ y ∈ r.V₀, y ∉ S) : (k : ℕ∞) ≤ (crossingEdges r.output S).encard := by
  obtain ⟨x, hx₀, hxS⟩ := hS
  obtain ⟨y, hy₀, hyS⟩ := hT
  set S' : Set r.V₀ := {z | (z : V) ∈ S}
  have hk := IsEdgeConnected.le_encard_crossingEdges hN₀ (S := S') ⟨⟨x, hx₀⟩, hxS⟩ ⟨⟨y, hy₀⟩, hyS⟩
  have hmaps : Set.MapsTo (Sym2.map Subtype.val) (crossingEdges r.N₀ S')
      (crossingEdges r.output S) := by
    rintro _ ⟨he, a, ha, b, hb, rfl⟩
    exact ⟨(r.output.mem_edgeSet).mpr (r.output_adj_of_N₀ ((r.N₀).mem_edgeSet.mp he)),
      a, ha, b, hb, rfl⟩
  exact hk.trans (Set.encard_le_encard_of_injOn hmaps
    (Sym2.map.injective Subtype.val_injective).injOn)

end Step1Run

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
  refine ⟨r.mem_V₀_or_added, ?_⟩
  rw [← le_minCutSize_iff]
  -- every edge cut `E₀` of the output has at least `k` edges
  refine le_iInf₂ fun E₀ hE₀ => ?_
  obtain ⟨S, hS, hT, hsub⟩ := hE₀.exists_side
  refine le_trans ?_ (Set.encard_le_encard hsub)
  -- Case 1: `V₀` lies within `S` or within `T = Sᶜ`
  by_cases h₁ : r.V₀ ⊆ S
  · exact r.case1 h₁ hT
  by_cases h₂ : r.V₀ ⊆ Sᶜ
  · rw [← crossingEdges_compl]
    exact r.case1 h₂ (by simpa using hS)
  -- Case 2: `V₀` meets both sides
  obtain ⟨y, hy₀, hyS⟩ := Set.not_subset.mp h₁
  obtain ⟨x, hx₀, hxS⟩ := Set.not_subset.mp h₂
  exact r.case2 hN₀ ⟨x, hx₀, by simpa using hxS⟩ ⟨y, hy₀, hyS⟩

end ECSBM
