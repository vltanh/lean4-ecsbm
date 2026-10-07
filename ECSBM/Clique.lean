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
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hd
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le he
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one]
  omega

/-- **The complete graph on `n` vertices is `(n - 1)`-edge-connected.** If `S` and its
complement are nonempty, with `d` and `e` vertices, the `d * e ≥ d + e - 1 = n - 1` edges between
them cross the cut (the counting argument of the arXiv version). -/
theorem isEdgeConnected_completeGraph [Finite V] :
    (completeGraph V).IsEdgeConnected (Nat.card V - 1) := by
  rw [← le_minCutSize_iff]
  refine le_iInf₂ fun F hF => ?_
  obtain ⟨S, hS, hSc, hsub⟩ := hF.exists_side
  -- the edges `s(x, y)` with `x ∈ S` and `y ∉ S` cross the cut, and they are distinct
  have hmaps : Set.MapsTo (fun p : V × V => s(p.1, p.2)) (S ×ˢ Sᶜ)
      (crossingEdges (completeGraph V) S) := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact ⟨((completeGraph V).mem_edgeSet).mpr ((top_adj x y).mpr fun h => hy (h ▸ hx)),
      x, hx, y, hy, rfl⟩
  have hinj : Set.InjOn (fun p : V × V => s(p.1, p.2)) (S ×ˢ Sᶜ) := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩ ⟨x', y'⟩ ⟨hx', hy'⟩ h
    rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact absurd hx hy'
  -- there are `|S| * |Sᶜ| ≥ |S| + |Sᶜ| - 1 = n - 1` of them
  have hcount : ((Nat.card V - 1 : ℕ) : ℕ∞) ≤ (S ×ˢ Sᶜ).encard := by
    rw [Set.encard_prod, ← (Set.toFinite S).cast_ncard_eq, ← (Set.toFinite Sᶜ).cast_ncard_eq,
      ← Set.ncard_add_ncard_compl S]
    exact_mod_cast add_sub_one_le_mul ((Set.ncard_pos).mpr hS) ((Set.ncard_pos).mpr hSc)
  exact hcount.trans ((Set.encard_le_encard_of_injOn hmaps hinj).trans
    (Set.encard_le_encard hsub))

/-- The complete graph on `n + 2` vertices has minimum cut size `n + 1`: the edges at one vertex
form an edge cut with `n + 1` edges, and there is none smaller. -/
theorem minCutSize_completeGraph (n : ℕ) :
    minCutSize (completeGraph (Fin (n + 2))) = n + 1 := by
  apply le_antisymm
  · -- the `n + 1` edges at the vertex `0` form an edge cut
    have hcut := isEdgeCut_crossingEdges (completeGraph (Fin (n + 2)))
      (S := {0}) (Set.singleton_nonempty 0) ⟨1, by simp⟩
    refine (iInf₂_le _ hcut).trans ?_
    have hsub : crossingEdges (completeGraph (Fin (n + 2))) {0} ⊆
        (fun j => s(0, j)) '' ({0}ᶜ : Set (Fin (n + 2))) := by
      rintro e ⟨-, x, hx, y, hy, rfl⟩
      rw [Set.mem_singleton_iff] at hx
      exact ⟨y, hy, by rw [hx]⟩
    refine (Set.encard_le_encard hsub).trans ((Set.encard_image_le _ _).trans ?_)
    have h₀ : ({0}ᶜ : Set (Fin (n + 2))) = ↑((Finset.univ : Finset (Fin (n + 2))).erase 0) := by
      ext
      simp
    rw [h₀, Set.encard_coe_eq_coe_finsetCard, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin]
    simp
  · simpa using (le_minCutSize_iff _ _).mpr (isEdgeConnected_completeGraph (V := Fin (n + 2)))

end ECSBM
