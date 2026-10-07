module

public import ECSBM.Theorem1
public import ECSBM.Clique
public import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Order.Interval.Finset.Fin

/-!
# Step 1 of Stage 1 as the paper describes it

Section "The EC-SBM network simulator" (Stage 1) and Fig. 3 describe Step 1 for a cluster with
vertex set `V` and desired edge connectivity `k` as follows. The vertices are processed one at a
time, in the order of their availability. At the start of an iteration, the growing subnetwork
`N₀` holds the vertices processed so far, and the next vertex `v` is made adjacent to
`min{k, |N₀|}` vertices of `N₀`. The paper prints `max{k, |N₀|}`, a misprint: with `max`, the
first vertex could not be made adjacent to `k ≥ 1` vertices of the empty subnetwork, and every
later vertex would be made adjacent to all of `N₀`. During the first `k + 1` iterations, each
vertex is made adjacent to all the vertices before it, so that they form a `(k + 1)`-clique
(`ECSBM.CliqueStep1Run.isClique`), and each later vertex is made adjacent to exactly `k` vertices
already present.

Fig. 3 states that the spanning subnetwork built this way has minimum cut size at least `k`, by
Theorem 1, and the section "Theoretical guarantees" says the same. This is
`ECSBM.CliqueStep1Run.isEdgeConnected`: the run is a run of Step 1 started from the
`(k + 1)`-clique (`ECSBM.CliqueStep1Run.toStep1Run`, with the same output), and the clique is
`k`-edge-connected (`ECSBM.isEdgeConnected_completeGraph`).
-/

@[expose] public section

namespace ECSBM

open SimpleGraph

/-- A run of Step 1 of Stage 1 on a cluster with vertex set `V` and desired edge connectivity
`k`, as Section "The EC-SBM network simulator" describes it: the vertices are processed in the
order `order 0, order 1, …`, and the vertex `order j` is made adjacent to `min k j` of the `j`
vertices processed before it. The choices of the order and of the neighbours are arbitrary. -/
structure CliqueStep1Run (V : Type*) [Fintype V] (k : ℕ) where
  /-- The order in which the vertices are processed: `order j` is processed `j`-th. -/
  order : Fin (Fintype.card V) ≃ V
  /-- The vertices that `order j` is made adjacent to. -/
  nbrs : Fin (Fintype.card V) → Finset V
  /-- Each of them was processed before `order j`. -/
  nbrs_present : ∀ j, ∀ u ∈ nbrs j, ∃ i < j, order i = u
  /-- There are `min k j` of them. -/
  card_nbrs : ∀ j, (nbrs j).card = min k j

namespace CliqueStep1Run

variable {V : Type*} [Fintype V] {k : ℕ}

/-- The spanning subnetwork that the run outputs. -/
def output (r : CliqueStep1Run V k) : SimpleGraph V :=
  fromEdgeSet {e | ∃ j, ∃ u ∈ r.nbrs j, e = s(r.order j, u)}

/-- The vertex processed `j`-th is adjacent to the vertices chosen for it. -/
theorem output_adj (r : CliqueStep1Run V k) {j : Fin (Fintype.card V)} {u : V}
    (hu : u ∈ r.nbrs j) : r.output.Adj (r.order j) u := by
  refine (fromEdgeSet_adj _).mpr ⟨⟨j, u, hu, rfl⟩, ?_⟩
  obtain ⟨i, hij, rfl⟩ := r.nbrs_present j u hu
  exact fun h => hij.ne' (r.order.injective h)

/-- During the first `k + 1` iterations, every vertex is made adjacent to all the vertices
processed before it: the `j ≤ k` vertices before it are present, and it must be made adjacent to
`min k j = j` of them. -/
theorem mem_nbrs_of_lt (r : CliqueStep1Run V k) {i j : Fin (Fintype.card V)} (hij : i < j)
    (hj : (j : ℕ) ≤ k) : r.order i ∈ r.nbrs j := by
  classical
  by_contra hnot
  have hsub : r.nbrs j ⊆ ((Finset.Iio j).image r.order).erase (r.order i) := by
    intro u hu
    obtain ⟨i', hi', rfl⟩ := r.nbrs_present j u hu
    exact Finset.mem_erase.mpr
      ⟨fun h => hnot (h ▸ hu), Finset.mem_image_of_mem _ (Finset.mem_Iio.mpr hi')⟩
  have h₁ := Finset.card_le_card hsub
  rw [r.card_nbrs j, min_eq_right hj,
    Finset.card_erase_of_mem (Finset.mem_image_of_mem _ (Finset.mem_Iio.mpr hij)),
    Finset.card_image_of_injective _ r.order.injective, Fin.card_Iio] at h₁
  have : (i : ℕ) < j := hij
  omega

/-- "The result of the first `k + 1` iterations is a `(k + 1)`-clique": the vertices processed
first, `order i` for `i ≤ k`, are pairwise adjacent. -/
theorem isClique (r : CliqueStep1Run V k) :
    r.output.IsClique {v | (r.order.symm v : ℕ) ≤ k} := by
  intro a ha b hb hab
  have hne : r.order.symm a ≠ r.order.symm b := fun h => hab (r.order.symm.injective h)
  rcases lt_or_gt_of_ne hne with h | h
  · simpa using (r.output_adj (r.mem_nbrs_of_lt h hb)).symm
  · simpa using r.output_adj (r.mem_nbrs_of_lt h ha)

/-- The vertices processed in the first `k + 1` iterations, which form a `(k + 1)`-clique. -/
def cliqueVertices (r : CliqueStep1Run V k) : Set V :=
  {v | (r.order.symm v : ℕ) ≤ k}

/-- The index of the `j`-th vertex processed after the first `k + 1`. -/
def addedIndex (hk : k < Fintype.card V) (j : Fin (Fintype.card V - (k + 1))) :
    Fin (Fintype.card V) :=
  ⟨j + (k + 1), by omega⟩

theorem addedIndex_val (hk : k < Fintype.card V) (j : Fin (Fintype.card V - (k + 1))) :
    (addedIndex hk j : ℕ) = j + (k + 1) := rfl

theorem order_addedIndex_mem_compl (r : CliqueStep1Run V k) (hk : k < Fintype.card V)
    (j : Fin (Fintype.card V - (k + 1))) : r.order (addedIndex hk j) ∈ r.cliqueVertices ᶜ := by
  simp only [cliqueVertices, Set.mem_compl_iff, Set.mem_ofPred_eq, Equiv.symm_apply_apply,
    addedIndex_val, not_le]
  omega

/-- The `j`-th vertex processed after the first `k + 1`. -/
def addedVertex (r : CliqueStep1Run V k) (hk : k < Fintype.card V)
    (j : Fin (Fintype.card V - (k + 1))) : (r.cliqueVertices ᶜ : Set V) :=
  ⟨r.order (addedIndex hk j), r.order_addedIndex_mem_compl hk j⟩

theorem addedVertex_bijective (r : CliqueStep1Run V k) (hk : k < Fintype.card V) :
    Function.Bijective (r.addedVertex hk) := by
  constructor
  · intro j₁ j₂ h
    have h' := congrArg Fin.val (r.order.injective (congrArg Subtype.val h))
    rw [addedIndex_val, addedIndex_val] at h'
    exact Fin.ext (by omega)
  · rintro ⟨v, hv⟩
    simp only [cliqueVertices, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hv
    refine ⟨⟨(r.order.symm v : ℕ) - (k + 1), by omega⟩, Subtype.ext ?_⟩
    change r.order (addedIndex hk _) = v
    rw [show addedIndex hk ⟨(r.order.symm v : ℕ) - (k + 1), by omega⟩ = r.order.symm v from
      Fin.ext (by rw [addedIndex_val, Fin.val_mk]; omega), Equiv.apply_symm_apply]

/-- The run, seen as a run of Step 1 started from the `(k + 1)`-clique on the vertices processed
first: each later vertex is made adjacent to `min k j = k` vertices already present. -/
noncomputable def toStep1Run (r : CliqueStep1Run V k) (hk : k < Fintype.card V) :
    Step1Run V k where
  V₀ := r.cliqueVertices
  N₀ := ⊤
  p := Fintype.card V - (k + 1)
  order := Equiv.ofBijective _ (r.addedVertex_bijective hk)
  nbrs := fun j => r.nbrs (addedIndex hk j)
  nbrs_present := fun j u hu => by
    obtain ⟨i, hij, rfl⟩ := r.nbrs_present _ u hu
    by_cases hi : (i : ℕ) ≤ k
    · exact Or.inl (by simpa [cliqueVertices] using hi)
    · have hij' : (i : ℕ) < j + (k + 1) := hij
      refine Or.inr ⟨⟨(i : ℕ) - (k + 1), by omega⟩, Fin.lt_def.mpr (by simp only; omega), ?_⟩
      change r.order (addedIndex hk _) = r.order i
      rw [show addedIndex hk ⟨(i : ℕ) - (k + 1), by omega⟩ = i from
        Fin.ext (by rw [addedIndex_val, Fin.val_mk]; omega)]
  card_nbrs := fun j => by
    rw [r.card_nbrs, addedIndex_val]
    omega

/-- The run starts from the `(k + 1)`-clique: its initial graph is complete on `k + 1`
vertices. -/
theorem toStep1Run_V₀_ncard (r : CliqueStep1Run V k) (hk : k < Fintype.card V) :
    (r.toStep1Run hk).V₀.ncard = k + 1 := by
  have hV₀ : (r.toStep1Run hk).V₀ =
      ↑((Finset.Iic (⟨k, hk⟩ : Fin (Fintype.card V))).map r.order.toEmbedding) := by
    ext v
    simp [toStep1Run, cliqueVertices, Fin.le_def]
  rw [hV₀, Set.ncard_coe_finset, Finset.card_map, Fin.card_Iic]

/-- Every edge of the run seen as started from the clique is an edge of the run: the edges of the
clique join vertices processed first, and the other edges are the same. -/
theorem toStep1Run_output_le (r : CliqueStep1Run V k) (hk : k < Fintype.card V) :
    (r.toStep1Run hk).output ≤ r.output := by
  intro a b h
  rcases (sup_adj _ _ _ _).mp h with h | h
  · obtain ⟨hne, a', b', -, rfl, rfl⟩ := (map_adj' _ _ _ _).mp h
    exact r.isClique a'.2 b'.2 hne
  · obtain ⟨⟨j, u, hu, he⟩, -⟩ := (fromEdgeSet_adj _).mp h
    have hadj := r.output_adj hu
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hadj
    · exact hadj.symm

/-- Seen as a run of Step 1 started from the clique, the run has the same output. -/
theorem toStep1Run_output (r : CliqueStep1Run V k) (hk : k < Fintype.card V) :
    (r.toStep1Run hk).output = r.output := by
  refine le_antisymm (r.toStep1Run_output_le hk) ?_
  intro a b h
  obtain ⟨⟨j, u, hu, he⟩, hne⟩ := (fromEdgeSet_adj _).mp h
  obtain ⟨i, hij, rfl⟩ := r.nbrs_present j u hu
  have hij' : (i : ℕ) < j := hij
  by_cases hj : (j : ℕ) ≤ k
  · -- an edge between two of the first `k + 1` vertices: an edge of the clique
    have hjC : r.order j ∈ r.cliqueVertices := by simp [cliqueVertices, hj]
    have hiC : r.order i ∈ r.cliqueVertices := by simp [cliqueVertices]; omega
    refine (sup_adj _ _ _ _).mpr (Or.inl ((map_adj' _ _ _ _).mpr ⟨hne, ?_⟩))
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨⟨_, hjC⟩, ⟨_, hiC⟩, (top_adj _ _).mpr fun h => hne (congrArg Subtype.val h),
        rfl, rfl⟩
    · exact ⟨⟨_, hiC⟩, ⟨_, hjC⟩, (top_adj _ _).mpr fun h => hne (congrArg Subtype.val h),
        rfl, rfl⟩
  · -- an edge added at a later step
    have hjlt := j.isLt
    set j' : Fin (Fintype.card V - (k + 1)) := ⟨(j : ℕ) - (k + 1), by omega⟩ with hj'
    have hjj : addedIndex hk j' = j := Fin.ext (by rw [addedIndex_val, hj', Fin.val_mk]; omega)
    refine (sup_adj _ _ _ _).mpr (Or.inr ((fromEdgeSet_adj _).mpr ⟨⟨j', r.order i, ?_, ?_⟩, hne⟩))
    · change r.order i ∈ r.nbrs (addedIndex hk j')
      rw [hjj]
      exact hu
    · change s(a, b) = s(r.order (addedIndex hk j'), r.order i)
      rw [hjj]
      exact he

/-- At the end of Step 1, the spanning subnetwork has minimum cut size at least `k` (Fig. 3), if
the cluster has more than `k` vertices: the run is a run of Step 1 started from the
`(k + 1)`-clique, which is `k`-edge-connected, so Theorem 1 applies. -/
theorem isEdgeConnected (r : CliqueStep1Run V k) (hk : k < Fintype.card V) :
    r.output.IsEdgeConnected k := by
  have hN₀ : (r.toStep1Run hk).N₀.IsEdgeConnected k := by
    have h := isEdgeConnected_completeGraph (V := (r.toStep1Run hk).V₀)
    rwa [Nat.card_coe_set_eq, r.toStep1Run_V₀_ncard hk, Nat.add_sub_cancel] at h
  rw [← r.toStep1Run_output hk]
  exact (theorem1 (r.toStep1Run hk) hN₀).2

/-- The procedure can always be run: there is a run on every finite vertex set, for every `k`. -/
theorem nonempty : Nonempty (CliqueStep1Run V k) := by
  classical
  let e := (Fintype.equivFin V).symm
  have h : ∀ j : Fin (Fintype.card V), ∃ s ⊆ (Finset.Iio j).image e, s.card = min k j :=
    fun j => Finset.exists_subset_card_eq (by
      rw [Finset.card_image_of_injective _ e.injective, Fin.card_Iio]
      exact min_le_right _ _)
  choose s hs hcard using h
  exact ⟨⟨e, s, fun j u hu => by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hs j hu)
    exact ⟨i, Finset.mem_Iio.mp hi, rfl⟩, hcard⟩⟩

end CliqueStep1Run

end ECSBM
