# EC-SBM's edge-connectivity guarantees, in Lean

[![Lean Action CI](https://github.com/vltanh/lean4-ecsbm/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/vltanh/lean4-ecsbm/actions/workflows/lean_action_ci.yml)

A Lean 4 and Mathlib formalization of the two theorems of The-Anh Vu-Le, Lahari Anne, George
Chacko and Tandy Warnow, *EC-SBM synthetic network generator*, Applied Network Science 10, 15
(2025), <https://doi.org/10.1007/s41109-025-00701-2>. EC-SBM generates a synthetic network that
resembles a given clustered network. Its first step builds, for each cluster whose minimum edge
cut has `k` edges, a spanning subnetwork: it starts from a `(k + 1)`-clique and adds the other
vertices one at a time, each made adjacent to `k` vertices already present. The paper proves that
this subnetwork is `k`-edge-connected, whatever `k`-edge-connected graph it starts from
(Theorem 1), and that every cluster of the network EC-SBM returns therefore has a minimum edge cut
at least as large as in the input network (Theorem 2). Both are formalized, unconditionally, by the
paper's own proofs.

## What is proved

- **Theorem 1** ([`ECSBM.theorem1`](ECSBM/Theorem1.lean#L140)) and **Theorem 2** ([`ECSBM.theorem2`](ECSBM/Theorem2.lean#L84)), each by the paper's
  proof: Theorem 1 by its two cases, Theorem 2 by Theorem 1 and the observation that the later
  steps never remove an edge.
- The paper's unnumbered claims: the first `k + 1` vertices of Step 1 form a clique
  ([`ECSBM.CliqueStep1Run.isClique`](ECSBM/CliqueStep1.lean#L85)); the spanning subnetwork of Step 1, as the paper runs it, is
  `k`-edge-connected ([`ECSBM.CliqueStep1Run.isEdgeConnected`](ECSBM/CliqueStep1.lean#L209), Fig. 3); Theorem 2 for that
  procedure ([`ECSBM.CliqueRun.theorem2`](ECSBM/CliqueRun.lean#L88)); every edge lies in exactly one of the clustered and the
  outlier subnetworks ([`ECSBM.edge_mem_clustered_xor_outlier`](ECSBM/Subnetworks.lean#L66)).
- **Beyond the paper:** the spanning subnetwork of Step 1 has minimum cut size exactly `k`, not
  only at least `k`, both as the paper runs it ([`ECSBM.CliqueStep1Run.minCutSize_output_eq`](ECSBM/Exactness.lean#L76)) and
  from any `k`-edge-connected start ([`ECSBM.Step1Run.minCutSize_output_eq`](ECSBM/Exactness.lean#L33)).
- The paper's proofs cite no result from the literature. The standard facts they use, such as the
  `k`-edge-connectivity of the `(k + 1)`-clique, are proved in the library.
- `lake build` succeeds with no `sorry` outside [`Challenge.lean`](Challenge.lean) and no `axiom`;
  `lake env lean scripts/Audit.lean` checks that every declaration depends only on [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext),
  [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound).

## The main results

[`Challenge.lean`](Challenge.lean) states them in Mathlib's vocabulary, with its own copy of the definitions they
need:

- [`ECSBM.Challenge.theorem1`](Challenge.lean#L211): start from a `k`-edge-connected graph `N₀` on some vertices `V₀` of a
  cluster `V`, and add the other vertices of `V` one at a time, each made adjacent to exactly `k`
  vertices already present, in any order and with any choice of neighbours. The resulting graph on
  `V` is `k`-edge-connected (Mathlib's `SimpleGraph.IsEdgeConnected`).
- [`ECSBM.Challenge.theorem2`](Challenge.lean#L220): for every clustered network `(G, 𝒞)` and every run of EC-SBM in which
  Step 1 starts, in each non-singleton cluster, from a `k`-edge-connected graph, `k` being the
  cluster's minimum cut size in `G`, every cluster's minimum cut size in the synthetic network is
  at least its minimum cut size in `G`. The run's stochastic block model samples and degree-correction edges are
  arbitrary.
- [`ECSBM.Challenge.le_minCutSize_iff`](Challenge.lean#L230), [`ECSBM.Challenge.minCutSize_eq_zero_iff`](Challenge.lean#L236) and
  [`ECSBM.Challenge.minCutSize_completeGraph`](Challenge.lean#L241) tie the paper's minimum cut size to Mathlib's
  `k`-edge-connectivity and check it on disconnected and complete graphs;
  [`ECSBM.Challenge.Run.exists_clique`](Challenge.lean#L249) shows that runs meeting Theorem 2's hypothesis exist for every
  clustered network.

## Palomar

The project is packaged for the [Palomar](https://palomar-registry.org) registry, though it is not
submitted there: [`Challenge.lean`](Challenge.lean), [`Solution.lean`](Solution.lean) (which
restates the Challenge's theorems and proves them from the library),
[`comparator.json`](comparator.json) and [`formalization.yaml`](formalization.yaml). To run
Comparator locally (it needs [bubblewrap](https://github.com/containers/bubblewrap)):

```sh
lake env lake comparator --config=comparator.json
```

## Audit summary

From [`REPORT.md`](REPORT.md):

- **Errors.** None in the theorems. The description of Step 1 prints `max{k, |N₀|}` for
  `min{k, |N₀|}` (E1).
- **Gaps.** The proof of Theorem 1 claims that a `k`-edge-connected `N₀` has at least `k + 1`
  vertices, which needs two vertices and is not used (E3); its Case 1 claims "exactly `k`"
  neighbours where "at least `k`" is needed, and gives half of the reason (E4); the published
  version uses without proof that the `(k + 1)`-clique is `k`-edge-connected, which its arXiv
  version proves (E8).
- **Missing hypotheses.** Theorem 2's "allowing for any way of initializing Step 1" must mean the
  `k`-edge-connected initializations of Theorem 1, as the text before Theorem 1 says; read
  literally, the theorem is false (Section 4).
- **Proofs.** Every proof follows the paper's; none departs from it.
- **Typos.** E5, E6, E9 (notation) and E10.

## Credits

- Formalized by Claude Opus 5.5 (Anthropic), in Claude Code, at the request of The-Anh Vu-Le,
  following the [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) procedure;
  independent agents reviewed the statements, the proofs and the audit. No person has reviewed the
  proofs yet.
- Made on 7 October 2026: 1.55 hours from the request to the completed audit, with 4 sub-agents,
  at most 2 at once. [`CREDITS.md`](CREDITS.md) gives the procedure, the agents and the effort.

## Related work

From [`REPORT.md`](REPORT.md), Section 10 (search of 7 October 2026):

- Theorem 1's argument was known: it is the edge version of the "expansion lemma", applied once per
  added vertex (Havet's course notes on connectivity, Lemma 5.3; Alvarez-Hamelin and Busch,
  [arXiv:0803.3057](https://arxiv.org/abs/0803.3057), 2008), which the paper does not cite. The
  paper's contribution is a generator built on it, which obtains the guarantee of Theorem 2 by
  construction, with a proof.
- RECCS ([arXiv:2502.02050](https://arxiv.org/abs/2502.02050)), from the same group, reaches the
  same guarantee by repairing an SBM network.
- No erratum or later version of the paper was found. The works that cite it, by the authors and
  their collaborators, use EC-SBM or its networks, or name it for future work; none corrects it.
  Until May 2026 the authors' code chose Step 1's neighbours greedily rather than as the paper
  describes; the theorems hold for every choice.
- No earlier formalization of the paper or its theorems was found. This one uses Mathlib's
  `k`-edge-connectivity (December 2025) and consulted no other formalization.

## What's next

Step 1 gives exactly the desired edge connectivity, not just at least it: the last vertex added
has `k` edges (proved in [`ECSBM/Exactness.lean`](ECSBM/Exactness.lean), beyond the paper), so any
excess in the synthetic clusters comes from the later stages. Started from the clique, it even gives `k`-vertex-connectivity, which would
strengthen Theorem 2 once Mathlib has vertex connectivity. The cut characterization of edge
connectivity and its value on complete graphs, proved here, would fit in Mathlib, with the edge
expansion lemma, which is Theorem 1 for one added vertex. See [`REPORT.md`](REPORT.md),
Section 11.

## Building

```sh
lake exe cache get            # download Mathlib's compiled files
lake build                    # builds the library, the Challenge and the Solution
lake env lean scripts/Audit.lean                       # axioms and dependencies
python3 scripts/route_check.py check docs/paper_routes.tsv --accept docs/route_differences.tsv
python3 scripts/sync_challenge_defs.py --check         # the Challenge's copy of the definitions
python3 scripts/linkify_docs.py                        # update the documents' links to the code
```

The toolchain is Lean `v4.35.0-rc4`, with Mathlib's tag `v4.35.0-rc4`. [`scripts/route_check.py`](scripts/route_check.py)
reads `.lake/route_deps.tsv`, which the audit writes.

## Layout

| Module | Contents |
| --- | --- |
| [`ECSBM/Defs.lean`](ECSBM/Defs.lean) | The definitions the theorems need (copied into [`Challenge.lean`](Challenge.lean)): edge cuts and the minimum cut size, a run of Step 1, a run of EC-SBM |
| [`ECSBM/Terminology.lean`](ECSBM/Terminology.lean) | Section "Terminology": the minimum cut size and Mathlib's `k`-edge-connectivity, cuts and crossing edges, monotonicity |
| [`ECSBM/Clique.lean`](ECSBM/Clique.lean) | The `(k + 1)`-clique is `k`-edge-connected; the minimum cut size of a complete graph |
| [`ECSBM/Theorem1.lean`](ECSBM/Theorem1.lean) | Theorem 1 and its two cases |
| [`ECSBM/CliqueStep1.lean`](ECSBM/CliqueStep1.lean) | Step 1 as the paper runs it: the first `k + 1` vertices form a clique, and the output is `k`-edge-connected (Fig. 3) |
| [`ECSBM/Subnetworks.lean`](ECSBM/Subnetworks.lean) | The clustered and the outlier subnetworks |
| [`ECSBM/Theorem2.lean`](ECSBM/Theorem2.lean) | Theorem 2 and the steps of its proof |
| [`ECSBM/Existence.lean`](ECSBM/Existence.lean) | Runs exist; a `k`-edge-connected graph with two vertices has `k + 1` |
| [`ECSBM/CliqueRun.lean`](ECSBM/CliqueRun.lean) | Theorem 2 for EC-SBM as the paper runs it |
| [`ECSBM/Exactness.lean`](ECSBM/Exactness.lean) | Beyond the paper: Step 1's output has minimum cut size exactly `k` |
| [`Challenge.lean`](Challenge.lean), [`Solution.lean`](Solution.lean) | The statements of record, and their proofs from the library |
| [`scripts/`](scripts) | The audit, the route check, the Challenge's copy of the definitions, the documents' links and tables |
| [`docs/`](docs) | The routes of the paper's proofs, and the reviewed differences (none) |

There is no `External/` directory: the paper's proofs use no result from the literature.

## GitHub configuration

`.github/workflows/lean_action_ci.yml` builds the project on every push and runs the audit, the
route check, and the checks of the Challenge's copy of the definitions, of the links and of the
tables.

## License

Apache-2.0; see [`LICENSE`](LICENSE).
