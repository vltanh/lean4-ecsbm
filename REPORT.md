# Audit of the paper and the formalization

Paper: The-Anh Vu-Le, Lahari Anne, George Chacko and Tandy Warnow, *EC-SBM synthetic network
generator*, Applied Network Science 10, 15 (2025), <https://doi.org/10.1007/s41109-025-00701-2>,
the version of record (received 5 February 2025, accepted 18 March 2025, published 1 May 2025,
CC BY 4.0). The published version has no TeX source. The audit was made against the publisher's
HTML, whose mathematics is TeX, and checked against the PDF. Quotations give the section of the
paper and, for the theorems and proofs, the anchors of the published HTML: Theorem 1 is
[`#FPar1`](https://link.springer.com/article/10.1007/s41109-025-00701-2#FPar1) and its proof
`#FPar2`, Theorem 2 is `#FPar3` and its proof `#FPar4`. The earlier version, arXiv:2502.03662v1
(5 February 2025), is cited by the line numbers of its TeX source (`main.tex`). Section, result
and equation numbers are the paper's.

Status of the formalization:

- **Proved:** both theorems of the paper, Theorem 1 ([`ECSBM.theorem1`](ECSBM/Theorem1.lean#L140)) and Theorem 2
  ([`ECSBM.theorem2`](ECSBM/Theorem2.lean#L84)), each by the paper's own proof, and the paper's unnumbered claims: the first
  `k + 1` vertices of Step 1 form a clique ([`ECSBM.CliqueStep1Run.isClique`](ECSBM/CliqueStep1.lean#L85)), the spanning
  subnetwork that Step 1 builds is `k`-edge-connected (Fig. 3, [`ECSBM.CliqueStep1Run.isEdgeConnected`](ECSBM/CliqueStep1.lean#L209)),
  every edge of the network lies in exactly one of the clustered and the outlier subnetworks
  ([`ECSBM.edge_mem_clustered_xor_outlier`](ECSBM/Subnetworks.lean#L66)), and Theorem 2 for the procedure that the paper runs
  ([`ECSBM.CliqueRun.theorem2`](ECSBM/CliqueRun.lean#L88)).
- **Beyond the paper:** the library also proves that the spanning subnetwork of Step 1 has minimum
  cut size exactly `k`, not only at least `k` (Section 11).
- **Cited results:** the paper's proofs cite no result from the literature, so nothing is
  assumed and nothing lives in an `External/` directory. The formalization is unconditional.
- **Build:** `lake build` succeeds; the only `sorry`s are the six in [`Challenge.lean`](Challenge.lean), by design.
  There is no `axiom`. [`scripts/Audit.lean`](scripts/Audit.lean) checks that every declaration of the library depends
  only on [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound).
- **Challenge and Comparator:** [`Challenge.lean`](Challenge.lean) states Theorems 1 and 2 and four comparison
  theorems in Mathlib's vocabulary; Comparator accepts [`Solution.lean`](Solution.lean) against it, under Lean's
  kernel and NanoDa.
- **Statements:** no statement of the paper had to change. One misprint in the description of
  Step 1 is corrected (E1), and Theorem 2's phrase "allowing for any way of initializing Step 1" is
  read as the initializations of Theorem 1 (Section 4).
- **Proofs:** every proof follows the paper's. No proof departs from it (Section 7).

## 1. Summary

- **Errors.** None in the statements of the theorems. The description of Step 1 has a misprint,
  `max{k, |N₀|}` for `min{k, |N₀|}` (E1).
- **Gaps.** The proof of Theorem 1 claims that a `k`-edge-connected `N₀` has at least `k + 1`
  vertices, which needs `N₀` to have two vertices; the argument does not use the claim (E3). Its
  Case 1 claims "exactly `k`" neighbours where the argument needs "at least `k`" (true for a
  minimum cut, but not shown), and gives half of the reason (E4). The published version uses
  without proof that the `(k + 1)`-clique is `k`-edge-connected (E8). None of these affects a
  result.
- **Missing hypotheses.** Theorem 2 needs the initialization of Step 1 to be `k`-edge-connected.
  The statement says "allowing for any way of initializing Step 1", and the text before Theorem 1
  says which ways: "any `k`-edge-connected subgraph". The formalization states the condition
  (Section 4).
- **Redundant hypotheses.** None.
- **Use of cited results.** The proofs use no cited result. They use four standard facts of graph
  theory without proof (Section 2), all proved here.
- **Typos.** Two in the proof of Theorem 1 (E5, E6), notation clashes (E9), and a few elsewhere
  (E10).

## 2. Results from prior work and how the paper uses them

### Proved in `External/`

None: the paper's proofs cite no result from the literature.

### Standard facts used without citation

| Fact | Where the paper uses it | In the formalization |
| --- | --- | --- |
| The `(k + 1)`-clique is `k`-edge-connected | Section "Theoretical guarantees" and the caption of Fig. 3, to apply Theorem 1 to Step 1 as the paper runs it | [`ECSBM.isEdgeConnected_completeGraph`](ECSBM/Clique.lean#L39), by the counting argument of the arXiv version (E8) |
| A graph is `k`-edge-connected when at least `k` edges cross every partition of its vertices into two nonempty parts | Proof of Theorem 1, Case 2: "(S ∩ V₀, T ∩ V₀) is a cut for V₀ ... there are at least k edges that go between" | [`ECSBM.IsEdgeConnected.le_encard_crossingEdges`](ECSBM/Terminology.lean#L105), [`ECSBM.le_minCutSize_iff`](ECSBM/Terminology.lean#L40) |
| Removing an edge cut leaves two sides, and every edge between them lies in the cut | Proof of Theorem 1: "Let E₀ be a minimum edge cut for G whose deletion produces (S, T)" | [`ECSBM.IsEdgeCut.exists_side`](ECSBM/Terminology.lean#L72) |
| Adding edges does not reduce the edge connectivity of a cluster | Proof of Theorem 2: "Step 2a adds edges, which cannot reduce the edge-connectivity of any cluster" | [`ECSBM.minCutSize_mono`](ECSBM/Terminology.lean#L111), [`ECSBM.IsEdgeConnected.mono`](ECSBM/Terminology.lean#L122) |

### Does the paper use each cited result correctly?

No proof uses a cited result. The citations give context: the generators compared with EC-SBM
(SBM in graph-tool, RECCS, LFR, ABCD+o, nPSO), the clustering methods (Leiden, InfoMap, CM, WCC),
the network corpus, and RECCS's degree correction, which Stage 3 reuses.

## 3. Errors and gaps in the paper

**E1. Section "The EC-SBM network simulator", Stage 1: `max` for `min`.** The paper says: "We
make v adjacent to max{k,|N₀|} nodes in N₀, selecting its neighbors from N₀ by random sampling
without replacement", where `N₀` is the growing subnetwork. With `max`, a vertex processed while
fewer than `k` vertices are present, the first one for instance, would have to be made adjacent to
more vertices than there are, and every later vertex to all of `N₀`. The next sentence, "during the first k+1 generations, every node that is added is
made adjacent to every other node in the growing subnetwork, and therefore the result of the
first k+1 iterations is a (k+1)-clique", and Fig. 3 ("making each vertex adjacent to k previously
processed vertices") fit `min{k, |N₀|}` only. The formalization uses `min`
([`ECSBM.CliqueStep1Run`](ECSBM/CliqueStep1.lean#L39)). No result is affected.

**E2. Two descriptions of Step 1.** Section "The EC-SBM network simulator" makes each vertex
adjacent to `min{k, |N₀|}` vertices of the growing subnetwork (E1); Section "Theoretical
guarantees" adds the vertices "always ensuring that each vertex is made adjacent to exactly k nodes
already present in the growing subgraph", and Theorem 1 starts that procedure from any
`k`-edge-connected graph `N₀`. The two rules agree once `k` vertices are present. They differ when
the initial graph has fewer than `k` vertices, which the claim of E3 is meant to exclude: started
from a single vertex, which has no edge cut and so is `k`-edge-connected for every `k`, the `min`
rule on a cluster with at most `k` vertices (two vertices and `k = 2`, say) outputs a graph that is
not `k`-edge-connected. The formalization reads Theorem 1 with the rule of its own section,
"exactly `k`" ([`ECSBM.Step1Run`](Challenge.lean#L105)); with it, Theorem 1 holds as stated. In EC-SBM itself the desired
edge connectivity of a cluster is less than its number of vertices
([`ECSBM.desiredConnectivity_add_one_le`](ECSBM/Existence.lean#L89)), and the two rules give the same output.

**E3. Proof of Theorem 1 (`#FPar2`), first sentence: `|N₀| ≥ k + 1`.** "By construction, N₀ is
k-edge-connected, from which it follows that |N₀| ≥ k+1." Under the paper's definition of the
minimum cut size, the size of a minimum edge cut, where an edge cut "disconnects the cluster into
two or more parts", a graph with at most one vertex has no edge cut, so it is `k`-edge-connected
for every `k`, and the claim fails for `k ≥ 1` when `N₀` has one vertex, or none (Theorem 1 allows
any `V₀ ⊆ V`). It holds when `N₀` has at least two vertices: a cut around one vertex shows that each
vertex has degree at least `k` ([`ECSBM.IsEdgeConnected.add_one_le_card`](ECSBM/Existence.lean#L36)). The rest of the proof does
not use the claim. The statement of Theorem 1 holds as printed (with the rule "exactly `k`",
E2).

**E4. Proof of Theorem 1, Case 1: "exactly k".** "Let v ∈ T be the first vertex added to the
growing synthetic spanning subgraph. Then v must have exactly k neighbors in S, since v is added
after everything in V₀ is added." What the argument needs is that the `k` vertices `v` was made
adjacent to when it was added lie in `S`. The justification given covers those in `V₀`; for the
others it needs that every vertex added before `v` lies in `S`, which holds because `v` is the
first vertex of `T` to be added. "Exactly `k`" is more than the argument needs, and the paper does
not show it. For the paper's minimum edge cut it is true: the last vertex added has exactly `k`
neighbours, so a minimum edge cut has at most `k` edges, and every edge from `v` to `S` lies in it.
For other edge cuts it can fail, since a vertex of `S` added after `v` may be made adjacent to `v`:
with `N₀` the edge `{0, 1}`, `k = 1`, vertex `2` joined to `0` and vertex `3` joined to `2`, and
`S = {0, 1, 3}`, vertex `2` has two neighbours in `S`. The formalization proves "at least `k`" with
both reasons, for every edge cut ([`ECSBM.Step1Run.case1`](ECSBM/Theorem1.lean#L66)). The result holds.

**E5. Proof of Theorem 1, Case 1: a set of vertices for a set of edges.** "Note that
{v′ ∈ S: (v,v′) ∈ E(G)} ⊆ E₀" puts a set of vertices inside the set of edges `E₀`; the intended set
is that of the edges `(v, v′)` with `v′ ∈ S`. Typo.

**E6. Proof of Theorem 1, Case 2: `V₀` for `N₀`.** "Since V₀ is k-edge connected, there are at
least k edges that go between S ∩ V₀ and T ∩ V₀": `V₀` is a set of vertices, and the
`k`-edge-connected graph is `N₀`. The step also uses, without saying so, that the edges of `N₀`
are edges of `G` (Step 1 only adds edges). Typo.

**E7. Theorem 2 (`#FPar3`): "allowing for any way of initializing Step 1".** Read literally, the
theorem is false; read with the text before Theorem 1, it holds. See Section 4.

**E8. The `(k + 1)`-clique.** Section "Theoretical guarantees" applies Theorem 1 to Step 1 started
from a `(k + 1)`-clique ("we asserted but did not prove that the synthetic spanning subgraph we
generate in this process for the cluster C is k-edge-connected; here, we prove this (see
Theorem 1)"), and so does the caption of Fig. 3. This needs the clique to be `k`-edge-connected,
which the published version does not prove. It is standard, and the arXiv version proves it in
Case 1 of its proof (`main.tex`, lines 454–458): if `d ≥ 1` vertices of the clique lie in `T`, the
`d(k - d + 1)` edges between the two parts of the clique cross the cut, and
`d(k - d + 1) - k = (k - d)(d - 1) ≥ 0`. There, "Then, d ≤ k + 1" (line 452) is not enough for
`(k - d)(d - 1) ≥ 0`, which needs `d ≤ k`. That follows from the "without loss of generality" of
the same line, which makes `T` hold the smaller part of the clique, so that `2d ≤ k + 1`. The
formalization proves the fact by this counting argument, applied to a cut of the clique itself,
whose two sides are nonempty ([`ECSBM.isEdgeConnected_completeGraph`](ECSBM/Clique.lean#L39), with
[`ECSBM.add_sub_one_le_mul`](ECSBM/Clique.lean#L30)). The arXiv version also writes `λ(G)` (lines 458 and 466), `E`
(lines 456, 462 and 464) and `U` (lines 464 and 466) for `λ(G_n)`, `E_n` and `U_t`, and `|S| = k`
(line 437) for `|S_i| = k`. It already remarked that "any k-edge-connected graph can be used
instead of a (k+1)-clique" (line 441), without proof; the published version proves it
(Theorem 1).

**E9. Notation.** `N₀` denotes three objects: the growing subnetwork in the description of Stage 1,
the initial `k`-edge-connected graph in Theorem 1, and the result of Step 1 for all clusters in the
proof of Theorem 2, which the sentence between the two theorems ("every cluster has at least the
minimum edge-connectivity in N₀") already uses before that proof defines it. `G` denotes the
output of Step 1 in Theorem 1 and the empirical network in Theorem 2 and Section "Materials and
methods"; `N` denotes the input network in Section "The EC-SBM network simulator" and the synthetic
network in Theorem 2. The formalization names them apart (`ECSBM.Step1Run.N₀`,
[`ECSBM.Step1Run.output`](Challenge.lean#L123), [`ECSBM.Run.step1Output`](Challenge.lean#L177), [`ECSBM.Run.output`](Challenge.lean#L192)).

**E10. Other typos.** "the synthetic clustered subnework" (proof of Theorem 2); "an edge between
vertex i and vertex j in for the spanning subnetwork" (Section "Additional details about
Stage 1"); WCC is expanded as "Well-Connected Clusters" in Section "Evaluating SBM synthetic
networks" and as "Well-Connected Components" in Section "Experimental study design"; the reference
Kamiński, Prałat and Théberge (2023), ABCD+o, gives the DOI of their 2021 ABCD paper
(10.1017/nws.2020.45) instead of its own (10.1007/s41109-023-00552-9), and both of their ABCD
references spell the second author "Prańat"; "Excess(E), the number of excess edges in G" (Section "Terminology") names the
multigraph both `E` and `G`.

## 4. Missing hypotheses

| Where | Missing hypothesis | Counterexample without it | In the formalization |
| --- | --- | --- | --- |
| Theorem 2 | Step 1 starts, in each cluster `C`, from a `k`-edge-connected graph, `k` being the desired edge connectivity of `C` | A 6-cycle as the only cluster (`k = 2`), Step 1 started from the graph with no edge on its six vertices, and SBM sampling two disjoint triangles, which has the required degrees (all `2`) and number of edges (six), so that Stages 2 and 3 add nothing: the cluster ends disconnected, with minimum cut size `0 < 2` | The hypothesis `hinit` of [`ECSBM.theorem2`](ECSBM/Theorem2.lean#L84) |

Theorem 2 says "allowing for any way of initializing Step 1 of Stage 1". The paragraph before
Theorem 1 says which ways are meant ("we prove that this guarantee holds even if we initialize the
synthetic spanning subgraph with any k-edge-connected subgraph"), and the proof of Theorem 2 uses
Theorem 1, which assumes it. The formalization therefore states the condition explicitly; it is
the paper's, not a new one. The paper's own procedure meets it
([`ECSBM.CliqueRun.theorem2`](ECSBM/CliqueRun.lean#L88), [`ECSBM.Challenge.Run.exists_clique`](Challenge.lean#L249)).

## 5. Redundant hypotheses

None. Each hypothesis of Theorems 1 and 2 is used: the `k`-edge-connectivity of `N₀` in Case 2 of
Theorem 1, and that of the initial graphs in Theorem 2. The cleanup removed no hypothesis. The
formal Theorem 1 does not need `V₀` or `V` to be finite, only the set of vertices added.

## 6. How the formalization reads the paper

- **Graphs.** A network is a simple graph, Mathlib's `SimpleGraph` (Section "Terminology"). A
  multigraph is the multiset of its edges, an unordered pair `s(v, v)` being a self-loop and a
  repeated pair a set of parallel edges. Removing the excess edges keeps one edge of each set of
  parallel edges and no self-loop ([`ECSBM.addThenSimplify`](Challenge.lean#L144)).
- **Edge cuts and the minimum cut size.** An edge cut of a graph is a set of its edges whose
  removal leaves a graph that is not preconnected, "disconnects the cluster into two or more
  parts" ([`ECSBM.IsEdgeCut`](Challenge.lean#L84)). The minimum cut size is the least size of an edge cut, in `ℕ∞`
  ([`ECSBM.minCutSize`](Challenge.lean#L92)). A graph with at most one vertex has no edge cut; its minimum cut size is
  `⊤`, where the paper leaves it undefined. A cluster's minimum cut size is that of the subgraph it
  induces. "k-edge-connected", which the published version does not define, means minimum cut size
  at least `k`, as in the arXiv version ("λ(G_n) ≥ k"); [`ECSBM.le_minCutSize_iff`](ECSBM/Terminology.lean#L40) shows that this is
  Mathlib's `SimpleGraph.IsEdgeConnected k`. [`ECSBM.minCutSize_eq_zero_iff`](ECSBM/Terminology.lean#L129) and
  [`ECSBM.minCutSize_completeGraph`](ECSBM/Clique.lean#L65) check the definition on disconnected graphs and complete graphs.
- **Clusterings.** A clustering is a partition of all the vertices (`Finpartition`), and the
  outliers are the vertices of its singleton clusters, as in Sections "Terminology" and
  "Stochastic block model (SBM)". Section "Materials and methods" instead lets the outliers belong
  to no cluster; the two conventions differ only by singleton clusters, for which Theorem 2 holds
  with both sides `⊤`.
- **Step 1 started from `N₀`** (Theorem 1) is a run [`ECSBM.Step1Run`](Challenge.lean#L105): a graph `N₀` on a set `V₀`
  of vertices, an order of the other vertices (a bijection from `Fin p`, indexed from `0` where the
  paper writes `v₁, …, v_p`), and for each added vertex a set of exactly `k` vertices already
  present. The output is a graph on all of `V`, which is the paper's "has every node in `V`"; the
  first conjunct of [`ECSBM.theorem1`](ECSBM/Theorem1.lean#L140) says that every vertex is in `V₀` or added. The paper chooses
  the order and the neighbours by "availability", and the authors' code chose the neighbours
  greedily until May 2026 (Section 10); the formalization allows every choice, so it covers both.
  On the rule "exactly `k`" (Section "Theoretical guarantees"), see E2.
- **Step 1 as the paper runs it** is [`ECSBM.CliqueStep1Run`](ECSBM/CliqueStep1.lean#L39): the vertex processed `j`-th is made
  adjacent to `min{k, j}` vertices processed before it (E1). [`ECSBM.CliqueStep1Run.toStep1Run`](ECSBM/CliqueStep1.lean#L132)
  shows that it is a run of Step 1 started from the `(k + 1)`-clique, with the same output.
- **EC-SBM** is a run [`ECSBM.Run`](Challenge.lean#L159): a run of Step 1 on every non-singleton cluster, with its desired
  edge connectivity `k`, the minimum cut size of the cluster in the empirical network
  ([`ECSBM.desiredConnectivity`](Challenge.lean#L138)); the multigraphs that SBM generates in Stage 1 (Step 2a) and
  Stage 2; and the edges that Stage 3 adds. The SBM samples and the added edges are arbitrary,
  since Theorem 2 holds whatever they are. The parameter updates of Step 1 (degrees and edge
  counts) and the rules of SBM and of degree correction are not modelled: they decide which edges
  are added, and the guarantee does not depend on that. The output follows the proof of Theorem 2:
  Step 1 gives `N₀`, Steps 2a and 2b give `N₁`, Stage 2 adds the outlier subnetwork and removes
  excess edges, and Stage 3 adds edges ([`ECSBM.Run.output`](Challenge.lean#L192)). [`ECSBM.CliqueRun`](ECSBM/CliqueRun.lean) is the same with
  Step 1 as the paper runs it.
- **The clustered and outlier subnetworks** are graphs on all the vertices: `G_c` is the
  subnetwork induced by the vertices that are not outliers, and `G_out` is `G` without the edges of
  `G_c`, as Section "Materials and methods" defines it. [`ECSBM.outlierSubnetwork_adj`](ECSBM/Subnetworks.lean#L48) shows that
  its edges are those with an outlier endpoint, as Section "The EC-SBM network simulator" says.

Corrections of the paper: `max{k, |N₀|}` read as `min{k, |N₀|}` (E1). Readings: the rule
"exactly `k`" for Theorem 1 (E2), and the initializations of Theorem 2 (Section 4).

## 7. Departures from the paper's proofs

None: every proof follows the paper's argument, and an independent comparison of the formal
proofs with the paper's confirmed it. The proof of Theorem 1 has the paper's two cases
([`ECSBM.Step1Run.case1`](ECSBM/Theorem1.lean#L66), [`ECSBM.Step1Run.case2`](ECSBM/Theorem1.lean#L103)), and the proof of Theorem 2 the paper's steps:
Theorem 1 for each cluster, the claim for `N₁` at the end of Stage 1
([`ECSBM.Run.step1Output_le_stage1Output`](ECSBM/Theorem2.lean#L49)), then Stages 2 and 3
([`ECSBM.Run.stage1Output_le_stage2Output`](ECSBM/Theorem2.lean#L54), [`ECSBM.Run.stage2Output_le_output`](ECSBM/Theorem2.lean#L59)). The differences
are mechanical:

- The proof of Theorem 1 bounds every edge cut, where the paper takes a minimum one. The side `S`
  is the set of vertices that remain joined to one vertex, and `T` is the rest, a union of parts
  if the cut leaves more than two.
- "Without loss of generality, assume V₀ ⊆ S" is done by applying Case 1 to `S` or to its
  complement.
- The paper first disposes of the case where `N₀` contains all of `V`; Case 2 covers it, since
  then `V₀` meets both sides of every cut. The claim `|N₀| ≥ k + 1`, which the proof does not use,
  is proved separately with its missing condition (E3).
- In Theorem 2, the cluster `C` in `N₀` is the spanning subnetwork that Step 1 builds for `C`,
  since the clusters are disjoint; the formal proof uses only that it contains it.
- For Stage 2, the paper says that adding the outlier subnetwork "does not affect N₁ and so cannot
  modify the edge-connectivity of any cluster": in EC-SBM its edges all have an outlier endpoint.
  The formal model lets the multigraph of Stage 2 be any multigraph, so that every run is covered,
  and the proof uses for Stage 2 what the paper uses for Step 2a and Stage 3: the step keeps `N₁`,
  and adding edges cannot reduce the edge connectivity of a cluster.
- The proof of Theorem 2 treats the singleton clusters, which the paper does not mention: both of
  their sides are `⊤`.

## 8. What each result depends on

Generated by [`scripts/Audit.lean`](scripts/Audit.lean).

| Result | Lean | Results from prior work used |
| --- | --- | --- |
| Thm 1 | [`ECSBM.theorem1`](ECSBM/Theorem1.lean#L140) | – |
| Thm 2 | [`ECSBM.theorem2`](ECSBM/Theorem2.lean#L84) | – |
| Stage 1: first k + 1 vertices form a clique | [`ECSBM.CliqueStep1Run.isClique`](ECSBM/CliqueStep1.lean#L85) | – |
| Fig. 3: spanning subnetwork is k-edge-connected | [`ECSBM.CliqueStep1Run.isEdgeConnected`](ECSBM/CliqueStep1.lean#L209) | – |
| Thm 2 for the paper's Step 1 | [`ECSBM.CliqueRun.theorem2`](ECSBM/CliqueRun.lean#L88) | – |
| Each edge in exactly one subnetwork | [`ECSBM.edge_mem_clustered_xor_outlier`](ECSBM/Subnetworks.lean#L66) | – |
| Proof of Thm 1: N₀ has k + 1 vertices | [`ECSBM.IsEdgeConnected.add_one_le_card`](ECSBM/Existence.lean#L36) | – |

The route check ([`scripts/route_check.py`](scripts/route_check.py)) finds that every proof uses the results that the
paper's proof cites and no other: the proof of Theorem 2 uses Theorem 1, and the proof of
Theorem 1 uses no result of the paper. [`docs/route_differences.tsv`](docs/route_differences.tsv) records no difference.

## 9. Not formalized

- The stochastic block model and its generation in graph-tool (Section "Stochastic block model
  (SBM)"), the update of the degree sequence and the edge count matrix in Step 1 (Section
  "Additional details about Stage 1"), and the rules of degree correction (Stage 3, taken from
  RECCS). The formalization lets these produce any edges; the guarantee does not depend on them.
- The proportion of excess edges (Section "Terminology").
- The experiments (Experiments 1 to 4), the statistics of Table 1 and the distances between them,
  the runtime study, the network corpus and the comparison with SBM, RECCS, LFR, ABCD+o and nPSO.

## 10. The paper in the literature

Written from the paper's own account and a search made on 7 October 2026 in Semantic Scholar,
OpenAlex, Crossref, DataCite, arXiv, GitHub, the Palomar registry and the web (Google Scholar was
not queried directly). It covers everything found that bears on the two theorems, the generators
the paper builds on, and every work that cites it.

### Before the paper

- **The stochastic block model and graph-tool.** The SBM goes back to Holland, Laskey and Leinhardt
  ([Soc. Netw. 5, 1983](https://doi.org/10.1016/0378-8733(83)90021-7)). EC-SBM samples the
  micro-canonical degree-corrected SBM of graph-tool
  ([Peixoto 2014](https://doi.org/10.6084/m9.figshare.1164194)); the model is Peixoto's
  ([arXiv:1610.02703](https://arxiv.org/abs/1610.02703), PRE 95, 2017, which the paper does not
  cite), after the degree correction of Karrer and Newman
  ([arXiv:1008.3926](https://arxiv.org/abs/1008.3926), PRE 83, 2011). Vaca-Ramírez and Peixoto
  ([arXiv:2201.01658](https://arxiv.org/abs/2201.01658), PRE 105, 2022) showed that graph-tool's
  SBMs reproduce many network statistics, without examining the connectivity of the clusters; that
  is the paper's starting point.
- **Clusterings with connectivity guarantees.** The Connectivity Modifier
  ([arXiv:2303.02813](https://arxiv.org/abs/2303.02813); PLOS Complex Systems 1, 2024) and
  Well-Connected Clusters ([arXiv:2408.10464](https://arxiv.org/abs/2408.10464); Complex Networks
  XIII, 2025) of Park et al. split clusters until they are well connected. SBM followed by WCC gave
  EC-SBM its best fit.
- **RECCS**, by Anne et al., is EC-SBM's direct predecessor
  ([arXiv:2408.13647](https://arxiv.org/abs/2408.13647), Complex Networks XIII, 2025; extended
  version [arXiv:2502.02050](https://arxiv.org/abs/2502.02050), Advances in Complex Systems 28,
  2025). It also reaches a minimum cut size of each cluster at least that of the input, but by
  repair: it generates an SBM network and then adds edges to a cluster "until the mincut of the
  cluster is at least" its target. EC-SBM obtains the guarantee by construction, with a proof
  (Theorem 2), and reuses RECCS's degree correction as its Stage 3.
- **Other generators** that the paper compares with EC-SBM, LFR
  ([arXiv:0805.4770](https://arxiv.org/abs/0805.4770)), ABCD+o
  ([arXiv:2301.05749](https://arxiv.org/abs/2301.05749)) and nPSO
  ([arXiv:1707.07325](https://arxiv.org/abs/1707.07325)), and ABCD
  ([arXiv:2002.00843](https://arxiv.org/abs/2002.00843)), which it cites, do not target the edge
  connectivity of clusters.
- **Theorem 1 was known in substance.** Its argument is the edge version of the "expansion lemma",
  applied once per added vertex: adding a vertex adjacent to at least `k` vertices of a
  `k`-edge-connected graph keeps it `k`-edge-connected. This is Lemma 5.3 of Havet's course notes
  on connectivity
  ([INRIA, undated](https://www-sop.inria.fr/members/Frederic.Havet/Cours/connectivity.pdf), proof
  left as an exercise), and a special case of the expansion theorem of Alvarez-Hamelin and Busch
  ([arXiv:0803.3057](https://arxiv.org/abs/0803.3057), 2008; also Corollary 2 of
  Alvarez-Hamelin, Beiró and Busch, [arXiv:0912.1424](https://arxiv.org/abs/0912.1424), Internet
  Mathematics 7(1), 2011), whose authors note that their Corollary 1 "includes an
  edge-connectivity version of the Expansion Lemma". Induction on the added vertices gives
  Theorem 1. The vertex version is West's
  Expansion Lemma (*Introduction to Graph Theory*, 2nd ed., 2001, Lemma 4.2.3, as cited by
  Alvarez-Hamelin and Busch); with Whitney's inequality between vertex and edge connectivity it
  gives Theorem 1 when `N₀` is `k`-vertex-connected, as the `(k + 1)`-clique is, but not for every
  `k`-edge-connected `N₀`. The `k`-trees of Beineke and Pippert (JCT 6, 1969) and Rose (Discrete
  Math. 7, 1974), in which each new vertex is joined to a `k`-clique, are a special case of the
  construction. The constructive characterizations of edge connectivity by Lovász (1976) and Mader
  (1978) do not imply Theorem 1 directly. The paper cites none of these works. Its contribution is
  a generator built around the construction, which obtains RECCS's guarantee by construction,
  with a proof (Theorem 2).

### Concurrent work

None found. The only other generator found that targets the connectivity of clusters is RECCS,
from the same group. Recent extensions of ABCD (ABCD+o²,
[arXiv:2506.05486](https://arxiv.org/abs/2506.05486); mABCD,
[arXiv:2507.10795](https://arxiv.org/abs/2507.10795)) and other generators of 2025
([arXiv:2506.02686](https://arxiv.org/abs/2506.02686),
[arXiv:2503.09585](https://arxiv.org/abs/2503.09585)) do not address the internal connectivity of
communities.

### Since the paper

- **Versions.** arXiv has only the first version; Crossref records no update or erratum, and none
  was found elsewhere. The published version proves Theorem 1 for any `k`-edge-connected initial
  graph, which the arXiv version only remarked (E8), and adds Theorem 2.
- **Works that cite it** are all by the authors or their collaborators, and none extends, corrects
  or disputes the theorems.
  - Vu-Le, Park, Chen and Warnow, *Using stochastic block models for community detection*
    ([arXiv:2508.03843](https://arxiv.org/abs/2508.03843), there subtitled "The issue of
    edge-connectivity"; Applied Network Science 11, 2, 2025), use EC-SBM as their benchmark
    generator, and say that it "aims to produce the same minimum edge-cut size as the given input
    clustering", which is more than Theorem 2 gives.
  - *Dense subgraph clustering and a new cluster ensemble method*
    ([arXiv:2508.17013](https://arxiv.org/abs/2508.17013); Studies in Computational Intelligence,
    2026) and *Improving community detection with CVC* (Applied Network Science 11, 53, 2026,
    [doi:10.1007/s41109-026-00809-z](https://doi.org/10.1007/s41109-026-00809-z)) benchmark on
    networks generated by EC-SBM.
  - *Large scale community-aware network generation*
    ([arXiv:2511.19717](https://arxiv.org/abs/2511.19717), preprint) uses 73 of the paper's 74
    real-world networks and reuses EC-SBM's degree correction.
  - FastEnsemble ([arXiv:2409.02077](https://arxiv.org/abs/2409.02077); PLOS Complex Systems 2,
    2025) names EC-SBM among the simulators that future work should use.
  - The benchmark networks are published as a data set
    ([doi:10.13012/B2IDB-3284069_V1](https://doi.org/10.13012/B2IDB-3284069_V1), 2025).
- **The software.** The code of EC-SBM
  ([illinois-or-research-analytics/ec-sbm](https://github.com/illinois-or-research-analytics/ec-sbm))
  makes each of the first `k + 1` vertices adjacent to all those before it and every later vertex
  adjacent to `k` earlier ones, which confirms the reading `min{k, |N₀|}` of E1. Until May 2026 it
  chose these neighbours greedily, the processed vertices of highest remaining degree (with a
  degree-weighted random fallback), rather than by the availability-weighted random sampling that
  the paper describes. A commit of 15 May 2026, labelled a performance change, replaced the greedy
  choice by that sampling. Theorems 1 and 2 hold for every choice of neighbours, so both versions
  have the guarantee.

### Formalizations

- No formalization of the paper or of its theorems was found, in Lean, Isabelle, Coq/Rocq, HOL or
  Mizar, nor in the Palomar registry.
- This formalization uses Mathlib's `k`-edge-connectivity, `SimpleGraph.IsEdgeConnected`
  ([`EdgeConnectivity.lean`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Combinatorics/SimpleGraph/Connectivity/EdgeConnectivity.lean),
  added in December 2025,
  [PR #32870](https://github.com/leanprover-community/mathlib4/pull/32870)). Mathlib has no
  characterization of it by cuts, no edge connectivity as a number and no vertex connectivity yet;
  pull requests for vertex connectivity
  ([#33355](https://github.com/leanprover-community/mathlib4/pull/33355)) and for connectivity
  numbers ([#42494](https://github.com/leanprover-community/mathlib4/pull/42494)) are open. Outside
  Mathlib, [AlgoLib](https://github.com/cslib-community/AlgoLib) defines the edge connectivity as a
  number in `ℕ∞` through edge cuts, as [`ECSBM.minCutSize`](Challenge.lean#L92) does, and vertex connectivity.
- Menger's theorem, which the paper's proofs do not need, is formalized in Isabelle (the AFP entry
  [Menger](https://www.isa-afp.org/entries/Menger.html), Dittmann, 2017), in Coq
  ([graph-theory](https://github.com/rocq-community/graph-theory), Doczkal and Pous, 2020) and in
  Lean outside Mathlib ([kmill/msri2023_graphs](https://github.com/kmill/msri2023_graphs),
  [apnelson1/Matroid](https://github.com/apnelson1/Matroid),
  [facebookresearch/atlas-lean](https://github.com/facebookresearch/atlas-lean)). This
  formalization used none of them.

## 11. What's next

### Open directions

- **Step 1 gives exactly the desired edge connectivity.** The spanning subnetwork that Step 1
  builds, as the paper runs it, has minimum cut size exactly `k` when the cluster has at least two
  vertices and more than `k`: Theorem 1 gives at least `k`, and the last vertex processed has
  exactly `k` edges, or, when no vertex follows the clique, the `(k + 1)`-clique has minimum cut
  size `k`. The same holds for Step 1 started from any `k`-edge-connected graph, as soon as one
  vertex is added and there are at least two vertices. Both are proved in the library, beyond the
  paper ([`ECSBM.CliqueStep1Run.minCutSize_output_eq`](ECSBM/Exactness.lean#L76), [`ECSBM.Step1Run.minCutSize_output_eq`](ECSBM/Exactness.lean#L33)), and
  the first was also checked on 2,422 random runs. So whatever excess the synthetic clusters show
  over the desired edge connectivity comes from Steps 2a to 3, as the paper observes in
  Experiment 2 ("edges can be added ... which can increase the cluster connectivity beyond the
  desired value"). A natural target is a variant of the later stages that keeps the minimum cut
  size of every cluster exactly at its desired value, or a bound on the excess: adding a new edge
  to a connected graph leaves its minimum cut size unchanged exactly when some minimum edge cut
  leaves the edge's two endpoints on the same side.
- **Vertex connectivity.** Started from the `(k + 1)`-clique, as the paper runs it, Step 1's
  spanning subnetwork is even `k`-vertex-connected: the clique is, and adding a vertex adjacent to
  `k` vertices of a `k`-connected graph keeps it `k`-connected (the expansion lemma for vertex
  connectivity). Since adding edges keeps a graph `k`-connected, Theorem 2 then strengthens, for
  the paper's procedure, to: every synthetic cluster has vertex connectivity at least the empirical
  cluster's edge connectivity, which is at least its vertex connectivity. This needs the clique:
  from another `k`-edge-connected initial graph, the output need not be `k`-vertex-connected.
  Checked on 2,422 random runs, not in Lean: Mathlib has no vertex connectivity yet.
- **More neighbours.** Theorem 1 and its proof hold unchanged when each added vertex is made
  adjacent to at least `k` vertices already present, which covers variants of Step 1 that add more
  edges at once; Case 1 uses only `k` of them.
- **Other generators and network types.** The paper proposes to extend the techniques of EC-SBM to
  other generators (nPSO, LFR, ABCD+o), and names the simulation of dynamic and multilayer
  networks, hypergraphs and overlapping communities as relevant future work. Theorem 1's argument uses only the order in which vertices are added,
  so any generator that first builds such a spanning subnetwork per cluster and never removes its
  edges inherits Theorem 2; for overlapping communities, a vertex can be added to several
  clusters' subnetworks, and the argument applies to each cluster separately.

### Simpler proofs

The proofs are already short. The published proof of Theorem 1 is simpler than the arXiv
version's: by allowing any `k`-edge-connected initial graph, it replaces the count of clique edges
(`d(k - d + 1) ≥ k`) by the definition of `k`-edge-connectivity, and the count moves to the
standard fact that a clique is `k`-edge-connected (E8). An induction on the added vertices, by the
edge version of the expansion lemma (adding a vertex with `k` edges to a `k`-edge-connected graph
keeps it `k`-edge-connected, which is published, Section 10), is an equivalent proof, not a simpler
one: the paper's proof is that induction unrolled, Case 2 being its base and Case 1 the first step
at which the cut separates the vertices. No simpler argument was found for Theorem 2.

### The formalization

- **Contributions to Mathlib.** Mathlib has `SimpleGraph.IsEdgeConnected` but not: the
  characterization by cuts (at least `k` edges cross every partition into two nonempty parts,
  [`ECSBM.IsEdgeConnected.le_encard_crossingEdges`](ECSBM/Terminology.lean#L105) and [`ECSBM.IsEdgeCut.exists_side`](ECSBM/Terminology.lean#L72)), the edge
  connectivity as a number ([`ECSBM.minCutSize`](Challenge.lean#L92)), the edge connectivity of complete graphs
  ([`ECSBM.isEdgeConnected_completeGraph`](ECSBM/Clique.lean#L39)), the edge version of the expansion lemma, and vertex
  connectivity. These are general facts; pull requests for connectivity numbers and for vertex
  connectivity are open (Section 10), and the vertex-connectivity strengthening above needs the
  latter. Monotonicity under adding edges ([`ECSBM.IsEdgeConnected.mono`](ECSBM/Terminology.lean#L122)) is immediate from
  Mathlib's `SimpleGraph.IsEdgeReachable.mono`.
- **The random part of EC-SBM.** The formalization proves the guarantee for every output, whatever
  the stochastic block model samples. Statements about the distribution of the output, such as the
  expected degree sequence or the expected excess of the minimum cut sizes, would need a model of
  the micro-canonical degree-corrected SBM and of degree correction.
