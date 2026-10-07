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

/-- "The result of the first `k + 1` iterations is a `(k + 1)`-clique": the vertices processed
first, `order i` for `i ≤ k`, are pairwise adjacent. -/
theorem isClique (r : CliqueStep1Run V k) :
    r.output.IsClique {v | (r.order.symm v : ℕ) ≤ k} := by
  sorry

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
  sorry

/-- The `j`-th vertex processed after the first `k + 1`. -/
def addedVertex (r : CliqueStep1Run V k) (hk : k < Fintype.card V)
    (j : Fin (Fintype.card V - (k + 1))) : (r.cliqueVertices ᶜ : Set V) :=
  ⟨r.order (addedIndex hk j), r.order_addedIndex_mem_compl hk j⟩

theorem addedVertex_bijective (r : CliqueStep1Run V k) (hk : k < Fintype.card V) :
    Function.Bijective (r.addedVertex hk) := by
  sorry

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
    sorry
  card_nbrs := fun j => by
    sorry

/-- The run starts from the `(k + 1)`-clique: its initial graph is complete on `k + 1`
vertices. -/
theorem toStep1Run_V₀_ncard (r : CliqueStep1Run V k) (hk : k < Fintype.card V) :
    (r.toStep1Run hk).V₀.ncard = k + 1 := by
  sorry

/-- Seen as a run of Step 1 started from the clique, the run has the same output. -/
theorem toStep1Run_output (r : CliqueStep1Run V k) (hk : k < Fintype.card V) :
    (r.toStep1Run hk).output = r.output := by
  sorry

/-- At the end of Step 1, the spanning subnetwork has minimum cut size at least `k` (Fig. 3), if
the cluster has more than `k` vertices: the run is a run of Step 1 started from the
`(k + 1)`-clique, which is `k`-edge-connected, so Theorem 1 applies. -/
theorem isEdgeConnected (r : CliqueStep1Run V k) (hk : k < Fintype.card V) :
    r.output.IsEdgeConnected k := by
  sorry

/-- The procedure can always be run: there is a run on every finite vertex set, for every `k`. -/
theorem nonempty : Nonempty (CliqueStep1Run V k) := by
  sorry

end CliqueStep1Run

end ECSBM
