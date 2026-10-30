# Source and dependency map

The exact formal import graph is [metadata/MODULE_INDEX.json](metadata/MODULE_INDEX.json). Every non-toolchain module in that graph has a packaged source. [metadata/DEPENDENCY_PINS.json](metadata/DEPENDENCY_PINS.json) records repository URLs and complete revisions; source copyright headers and upstream licenses are preserved. Some dependencies use the compatibility patches pinned in OAI-003 on top of their upstream revisions. The module index identifies these versions, and the original patches and relevant upstream baseline files are included in `metadata/upstream_patches/` and `metadata/upstream_baselines/`. Packaged source hashes identify the actual bytes used. The graph describes imports, which can include declarations not used in the final proof.

| Source | Pin or location | Role and evidence boundary |
|---|---|---|
| Lean | 4.34.1; revision `5045d0056413266e57c625dcd7c365b10e377c52` | Toolchain and its standard libraries are external prerequisites. [Release](https://github.com/leanprover/lean4/releases/tag/v4.34.1). |
| OAI-003 | `openai/math`, `adc7f1241b42e322a6451854ab7e4b4c146bf78a` | Required formal sources are under `lean/OAI/`. The original finite-order theorem is among the imported results, with angular-to-finite identification supplied where used. [Pinned repository](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a). |
| OAI-003 mathematical manuscripts | [paper78.tex](references/oai003/paper78.tex), [paper1112.tex](references/oai003/paper1112.tex) | Exact pinned background manuscript bytes; repository paths and hashes are in `metadata/BACKGROUND_SOURCE_PINS.json`. These are not a new standalone paper for the angular 7/8 result. |
| Mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` | Required source modules are included. [Pinned repository](https://github.com/leanprover-community/mathlib4/tree/d13f23b723b8a846827a245b89c10fc7d3f11612). |
| Other formal packages | Full revisions in `metadata/DEPENDENCY_PINS.json` | Required sources, licenses and available original package configurations are included. The original OAI configuration may list additional packages outside this selected import closure. |
| Retained and new angular development | `lean/Angular*.lean` | Exact local source bytes; individual compilation receipts, source hashes and available object hashes are indexed. A single upstream publication revision is not asserted for all these files. |

## Classical literature provenance

The following bibliography identifies the analytic literature recorded in the development's source notes. It is not a blanket claim that all statements in these works were inspected or are invoked by the final proof. The reviewer should trace the exact formal application and its mathematical statement through the supplied sources and pinned manuscripts.

| Reference | Recorded location or statement | Access |
|---|---|---|
| Goldmakher and Louvel, *A quadratic large sieve inequality over number fields* | arXiv:1112.1642v2, Definition 1 and Theorem 1.1 | [Versioned PDF](https://arxiv.org/pdf/1112.1642v2) |
| Dunn and Radziwill, *Bias in cubic Gauss sums: Patterson's conjecture* | arXiv:2109.07463v3; Section 5 and Appendix A; Lemmas 5.3, 5.4 and Proposition 5.1 | [Versioned PDF](https://arxiv.org/pdf/2109.07463v3) |
| Heath-Brown, *Kummer's conjecture for cubic Gauss sums* | Theorem 2 in the author manuscript | [Oxford University Research Archive](https://ora.ox.ac.uk/objects/uuid:16c3966e-61cb-499d-839c-559b3794fcff) |
| NIST DLMF | Equation 10.43.19, K-Bessel Mellin integral | [Equation](https://dlmf.nist.gov/10.43.E19) |

These literature PDFs are linked rather than redistributed. The historical notes record selected inspection of these references, not a complete independent audit of each paper. Original Kubota/Patterson sources were not completely obtained or directly re-inspected in this campaign. Their bibliography and use as provenance should be traced in the supplied manuscripts and formal source route. No new source retrieval or literature audit was performed merely to assemble this ZIP.
