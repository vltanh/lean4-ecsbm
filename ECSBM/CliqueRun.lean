module

public import ECSBM.CliqueStep1
public import ECSBM.Existence
public import ECSBM.Theorem2

/-!
# Theorem 2 for EC-SBM as the paper runs it

Theorem 2 lets Step 1 start, in each non-singleton cluster, from any `k`-edge-connected graph. The
paper runs Step 1 as Section "The EC-SBM network simulator" describes it
(`ECSBM.CliqueStep1Run`): each vertex processed is made adjacent to `min{k, |N₀|}` vertices
already processed, so that the first `k + 1` vertices form a `(k + 1)`-clique.

`ECSBM.CliqueRun` is a run of EC-SBM whose Step 1 is this procedure in every non-singleton cluster,
and `ECSBM.CliqueRun.theorem2` is Theorem 2 for it, with no hypothesis on the initialization. A
run of this kind is a run of EC-SBM in the sense of `ECSBM.Run` (`ECSBM.CliqueRun.toRun`), with the
same output: the clique is `k`-edge-connected, and the desired edge connectivity `k` of a
non-singleton cluster is less than its number of vertices
(`ECSBM.CliqueRun.desiredConnectivity_lt_card`).
-/

@[expose] public section

namespace ECSBM

open SimpleGraph

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- A run of EC-SBM on the clustered network `(G, 𝒞)` in which Step 1 of Stage 1 is the procedure
of Section "The EC-SBM network simulator" in every non-singleton cluster `C`, with the desired edge
connectivity of `C`. The multigraphs that SBM generates and the edges that degree correction adds
are arbitrary, as in `ECSBM.Run`. -/
structure CliqueRun (G : SimpleGraph W) (𝒞 : Finpartition (Finset.univ : Finset W)) where
  /-- Stage 1, Step 1: the paper's procedure on each non-singleton cluster `C`. -/
  step1 : ∀ C ∈ nonsingletonClusters 𝒞, CliqueStep1Run (C : Set W) (desiredConnectivity G C)
  /-- Stage 1, Step 2a: the multigraph that SBM generates. -/
  stage1SBM : Multiset (Sym2 W)
  /-- Stage 2: the multigraph that SBM generates for the outlier subnetwork. -/
  stage2SBM : Multiset (Sym2 W)
  /-- Stage 3: the edges that degree correction adds. -/
  stage3 : SimpleGraph W

namespace CliqueRun

variable {G : SimpleGraph W} {𝒞 : Finpartition (Finset.univ : Finset W)}

/-- The synthetic network that the run returns: the union of the spanning subnetworks of the
clusters, to which Step 2a adds the SBM multigraph and Step 2b removes the excess edges; Stage 2
then adds the outlier subnetwork and removes the excess edges; Stage 3 adds edges. -/
noncomputable def output (r : CliqueRun G 𝒞) : SimpleGraph W :=
  addThenSimplify (addThenSimplify
    (⨆ (C) (hC : C ∈ nonsingletonClusters 𝒞), (r.step1 C hC).output.map Subtype.val)
    r.stage1SBM) r.stage2SBM ⊔ r.stage3

/-- The desired edge connectivity of a non-singleton cluster is less than its number of vertices
(`ECSBM.desiredConnectivity_add_one_le`). -/
theorem desiredConnectivity_lt_card {C : Finset W} (hC : C ∈ nonsingletonClusters 𝒞) :
    desiredConnectivity G C < Fintype.card (C : Set W) := by
  sorry

/-- The run as a run of EC-SBM in the sense of `ECSBM.Run`: in each non-singleton cluster, Step 1
is the run of `ECSBM.CliqueStep1Run.toStep1Run`, started from the `(k + 1)`-clique. -/
noncomputable def toRun (r : CliqueRun G 𝒞) : Run G 𝒞 where
  step1 := fun C hC => (r.step1 C hC).toStep1Run (desiredConnectivity_lt_card hC)
  stage1SBM := r.stage1SBM
  stage2SBM := r.stage2SBM
  stage3 := r.stage3

/-- The two descriptions of the run give the same synthetic network. -/
theorem toRun_output (r : CliqueRun G 𝒞) : r.toRun.output = r.output := by
  sorry

/-- **Theorem 2** for EC-SBM as the paper runs it: in the synthetic network, every cluster has
minimum cut size at least its minimum cut size in the empirical network `G`. -/
theorem theorem2 (r : CliqueRun G 𝒞) :
    ∀ C ∈ 𝒞.parts,
      minCutSize (G.induce (C : Set W)) ≤ minCutSize (r.output.induce (C : Set W)) := by
  sorry

end CliqueRun

end ECSBM
