# Verification evidence and limits

The [final original audit](audit/ANGULAR_HECKE_7_8_FINAL_AUDIT.txt) accepted
mathematics, scope, imported applicability, and coefficients/normalization/uniformity,
but rejected reproducibility of the original package. Its earliest source failure
was `AngularSieveDensity.lean:21` (also line 34), outside the public proof closure.

The [repair report](audit/ANGULAR_HECKE_7_8_REPAIR_REPORT.txt) accepts all five
criteria for the separately repaired public closure. It records 8,213 clean-built
source modules, fresh native-kernel replay, 20,519 artifact-part checks, a census
of 129,614 public proof dependencies, and standard axiom type checks.
See [VERIFICATION_RESULT.json](evidence/independent_repair/clean_build/VERIFICATION_RESULT.json),
[kernel replay](evidence/independent_repair/clean_build/KERNEL_REPLAY.json), and
[source preservation](evidence/independent_repair/SOURCE_PRESERVATION.json).

The repair preserves all original declaration text, relocating only an unused
23/24 corollary to `AngularNormTwistSeedContinuation`. Sixteen former imports leave
the public closure. Their source is retained for provenance; building every file
in `lean/` is not the certified build target. Use the two roots in the module index.

The report discloses a failed import-removal attempt and its correction. Its 8,211
successful fresh compilations were reused only after checking unchanged inputs,
dependencies, compiler recipes, objects and logs; no author caches were reused.
Full receipts, logs, baseline metadata and failed-attempt evidence are preserved
in the exact repaired ZIP listed in RELEASE_ASSETS.json. Historical absolute paths
in those records describe the original host; they are not portable build inputs.

The trusted boundary includes the pinned local Lean toolchain and its standard
libraries. No external kernel, Linux replay, official binary-byte provenance,
buildability of excluded legacy files, or exhaustive manual review of every
foundation is claimed. The 2026-10-30 packaging checks validate bytes and build
plan only; they do not constitute another proof replay or another mathematical audit.
