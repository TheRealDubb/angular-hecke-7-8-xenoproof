# Angular Hecke L-functions: 7/8 Zero-Free Region — Xenoproof

**Author: Troy Winarski · Independent researcher**  
**ORCID:** [0009-0004-5956-3825](https://orcid.org/0009-0004-5956-3825)

This repository presents an AI-assisted, Lean-verified zero-free theorem for the unit-compatible angular Hecke L-function family over **Q(sqrt(-3))**, the Eisenstein field.

The strict zero-free region is

**Re(s) > 7/8 = 0.875.**

It holds for every compatible integer angular type, every nonzero finite ideal modulus, primitive and imprimitive presentations, and every real unitary norm twist, with only the genuine principal pole excluded. The boundary line Re(s) = 7/8 is not included. No estimate uniform in unbounded angular order is claimed.

This strengthens the earlier [15/16 angular Hecke xenoproof](https://github.com/TheRealDubb/angular-hecke-15-16-xenoproof), moving the boundary from 0.9375 to 0.875, an improvement of 1/16. It does not claim a Gaussian-field theorem, a bound below 7/8, or the Riemann hypothesis.

The public theorem has no assumed moment estimate, detector bound, zero-free endpoint, conductor bound, or analytic-density premise. See the exact [theorem scope](TARGET_THEOREM.md) and [public Lean source](lean/AngularPhysicalFinalAssembly.lean).

## Verification status

The **repaired public theorem closure** passed:

- a clean source build of **8,213 Lean modules** under pinned Lean 4.34.1 on Windows;
- fresh native Lean-kernel replay of the public proof roots;
- a dependency audit of **129,614 constants**, with no missing, unsafe, or partial proof dependencies;
- an axiom audit permitting only `propext`, `Classical.choice`, and `Quot.sound`; and
- an independent AI-assisted review with **ACCEPT on all five criteria** for the repaired closure: mathematical soundness, statement and scope fidelity, imported-input applicability, coefficient/normalization/uniformity fidelity, and reproducibility.

**The repair history matters.** The *original* review ZIP failed the clean-source reproducibility check because of a stale, unused import route. The repaired package relocates one unused 23/24 corollary to a legacy module and removes 16 obsolete modules from the public import closure. The public 7/8 theorem sources and retained continuation declarations were preserved. The original ZIP remains rejected for reproducibility; the **ACCEPT** verdict applies to the separately repaired package.

This is an AI-assisted mathematical audit and native Lean verification record, **not independent human peer review**. An independent kernel implementation, Linux replay, official compiler-binary provenance comparison, and independent buildability of the excluded legacy modules are not claimed. Packaging verified source and evidence integrity without repeating the full build.

## Repository evidence

- [Exact theorem statement and pole conventions](TARGET_THEOREM.md)
- [Public nonvanishing theorem in Lean](lean/AngularPhysicalFinalAssembly.lean)
- [Statement comparison and ideal-series identification](lean/AngularPhysicalPublicStatementCheck.lean)
- [Both norm-twist conventions and shifted poles](lean/AngularPhysicalNormTwistNonvanishing.lean)
- [Proof route and dependency map](PROOF_DOSSIER.md)
- [Verification scope and limitations](VERIFICATION_STATUS.md)
- [Independent final audit](audit/ANGULAR_HECKE_7_8_FINAL_AUDIT.txt)
- [Reproducibility repair report](audit/ANGULAR_HECKE_7_8_REPAIR_REPORT.txt)
- [Clean-build verification receipt](evidence/independent_repair/clean_build/VERIFICATION_RESULT.json)
- [Fresh kernel-replay receipt](evidence/independent_repair/clean_build/KERNEL_REPLAY.json)
- [Source preservation check](evidence/independent_repair/SOURCE_PRESERVATION.json)
- [Reproduction instructions](REPRODUCTION.md)
- [Release assets and hashes](RELEASE_ASSETS.json)

The released source includes the **8,213-module public import closure** and associated audit tools and records. The larger source, review, and reproduction archives are **GitHub release assets**, separate from the tracked repository. Read [REPRODUCTION.md](REPRODUCTION.md) before attempting a local rebuild; the complete build targets the *repaired public closure*, not every archived legacy file.

## Release provenance

The frozen release tag is **[`v7-8-2026-10-30`](https://github.com/TheRealDubb/angular-hecke-7-8-xenoproof/releases/tag/v7-8-2026-10-30)**.

**Frozen commit:** `79830bf6a346a6742fde1ace977a8bb805e638e7`

The release page preserves the original verified source and its six uploaded assets, including the Git bundle, source ZIP, full audit evidence, repaired reproducibility archive, and `SHA256SUMS`. The historical original ZIP's failed-reproducibility verdict is not overwritten.

This README may evolve later without altering the frozen commit, tag, proof objects, or release evidence.

The previous [23/24 theorem package](https://github.com/TheRealDubb/angular-hecke-23-24) and [15/16 theorem package](https://github.com/TheRealDubb/angular-hecke-15-16-xenoproof) remain separate records.

## Xenoproof / Xenotheorem

A **xenoproof** is a mathematically verified proof whose correctness can be checked independently, while its essential strategy and conceptual structure are not yet adequately understood by human mathematicians.

The term describes the present epistemic status of the proof, **not** its origin, length, or use of AI.

A **xenotheorem** is a theorem for which the only currently known proof is a xenoproof. Such a classification is provisional: a xenoproof may cease to qualify after successful humanization, and a xenotheorem may cease to qualify when a sufficiently human-understood proof is developed or identified.

This 7/8 result is **provisionally described as a xenotheorem** because the author is not aware of an independently human-understood proof of this exact theorem. This terminology is intended to distinguish formal mathematical correctness from human mathematical understanding, without diminishing either.

## Research provenance

This work builds on the [OpenAI Family 003 mathematical development](https://github.com/openai/math), with exact upstream pins and source notices preserved in the repository. The extension, formalization, reviews, and packaging were developed with substantial AI assistance under the author's research direction. See [source notices](NOTICE.md). No upstream endorsement or independent human acceptance is implied.
