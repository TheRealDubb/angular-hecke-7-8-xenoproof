# Eisenstein angular Hecke L functions at seven eighths

This release presents the angular Hecke nonvanishing theorem over
\(K=\mathbb Q(\sqrt{-3})\): the continued L-function is nonzero for
\(\operatorname{Re}(s)>7/8\), with the principal pole excluded. It includes all
integer angular orders and nonzero finite ideal moduli subject to global-unit
compatibility, primitive and imprimitive presentations, and real unitary norm
twists. The boundary line itself is not included. Estimates are taken at fixed
finite angular caps; uniform estimates over unbounded angular order are not claimed.

Read the [exact statement and scope](TARGET_THEOREM.md), the
[proof route](PROOF_DOSSIER.md), and the
[public theorem source](lean/AngularPhysicalFinalAssembly.lean).
The [statement comparison](lean/AngularPhysicalPublicStatementCheck.lean) checks
the actual continued ideal L-function. The
[norm-twist theorem](lean/AngularPhysicalNormTwistNonvanishing.lean) includes both
twist sign conventions and their shifted pole exceptions.

## Verification status

The supplied independent repair report records a successful clean build of the
8,213-module public source closure, a fresh native Lean kernel replay of both
public roots, and a public proof dependency census of 129,614 constants with no
unsafe or partial constants and only `propext`, `Classical.choice`, and `Quot.sound`.
Their standard types were checked separately. The repaired copy received ACCEPT
on all five review criteria. These are the supplied review findings and receipts;
this release preparation checked their integrity and source agreement without
repeating the full build or kernel replay.

The original cold-review source package failed reproducibility because an unused
legacy import introduced stale declarations. The repair separates one unused
23/24 corollary into a legacy module. The public theorem sources and retained
continuation declarations are unchanged. The 16 excluded legacy source modules
and the moved corollary are archived but are not certified independently buildable.
See [verification details](VERIFICATION_STATUS.md) and the
[repair report](audit/ANGULAR_HECKE_7_8_REPAIR_REPORT.txt).

## Contents and reproduction

- `lean/`: supplied Lean sources, including the indexed public dependency closure.
- `metadata/`: exact dependency pins, source graph, resources, and provenance.
- `tools/`: the repaired source-build, import-audit, replay and axiom-check tools.
- `audit/` and `evidence/`: review reports and selected summary receipts.
- `references/` and `licenses/`: pinned background manuscripts and source notices.
- [Release assets](RELEASE_ASSETS.json): the unchanged repaired evidence archive
  and the earlier audit evidence, including full logs and per-module receipts.

Run `python -B verify_package.py --assets PATH_TO_RELEASE_ASSETS` for integrity,
and follow [REPRODUCTION.md](REPRODUCTION.md) for an optional full build.
The build uses Python's standard library and the pinned Lean 4.34.1 toolchain.
There is no new automatic CI success claim. The receipts record Windows execution;
Linux execution, a separate kernel implementation and official runtime binary-byte
provenance remain outside the verified scope.

This is the Eisenstein theorem. It does not establish a Gaussian-field theorem,
a result below 7/8, or the Riemann hypothesis. The background TeX manuscripts are
OAI-003 sources, not a newly authored standalone paper for this extension.
