ANGULAR HECKE 7/8 - SEPARATE REPRODUCIBILITY REPAIR

This copy preserves the theorem and mathematical argument of the supplied
2026-10-28 packet. The original archive is unchanged. See REPAIR_RECORD.json
and evidence/independent_repair/SOURCE_PRESERVATION.json for exact comparisons.

The only change to an original Lean source file is a module split:
AngularNormTwistContinuation no longer imports AngularSeedNonvanishing.
Its unused physical_seed_all_norm_twists corollary is preserved verbatim in
the new AngularNormTwistSeedContinuation module, together with that dependency.
All other declaration text is unchanged. The three public theorem/statement
source files are byte-identical to the originals.

The same two public roots now have a closure of 8,213 packaged source modules
plus 191 directly referenced toolchain modules. Sixteen old source modules,
including AngularSieveDensity and AngularPhysicalSieveEnergy, leave that
closure. Those files, and the moved legacy corollary, remain preserved for
provenance; this release does not certify their independent compilation.
The exact excluded list is in REPAIR_RECORD.json.

The original author records and original narrative documents remain historical
records. New evidence in evidence/independent_repair and the final repair report
states what was actually rebuilt and replayed. Original metadata is retained in
evidence/independent_repair/baseline_metadata. The root MODULE_INDEX and manifest
describe this repaired copy. Do not use the historical author setup files or
author runner for the clean build.

REPRODUCTION

Obtain the independently installed Lean 4.34.1 toolchain at the revision in
metadata/DEPENDENCY_PINS.json. Python uses its standard library only. Substitute
paths for the executable arguments and choose separate empty/new BUILD and
IMPORT_CHECK directories outside this packet. The -B flag prevents Python
from adding bytecode-cache files to the source packet.
From this packet root:

  python tools/verify_manifest.py
  python tools/rebuild_from_source.py --plan
  python -B tools/audit_source_imports.py --lean PATH_TO_LEAN --build-dir IMPORT_CHECK
  python -B tools/clean_build.py --lean PATH_TO_LEAN --build-dir BUILD --jobs 3
  python -B tools/replay_clean_build.py --lean PATH_TO_LEAN --checker PATH_TO_LEANCHECKER --build-dir BUILD

The clean builder constructs every non-toolchain dependency from these sources.
LEAN_PATH is replaced by BUILD/objects; no author cached setup or object is
admitted. Independent library modules may compile concurrently. The larger OAI
and angular modules are serialized to limit memory use. Each invocation gets a
source/dependency/output-hashed receipt and log. Resuming the same build checks
its exact identity and artifact hashes; a new BUILD directory starts from zero.

The replay driver first verifies every source, receipt, direct dependency
fingerprint, object part, and compilation log. It compiles a no-declaration
harness importing both public roots, then uses leanchecker --fresh to replay
the combined imported environment into a new kernel environment. This is Lean's
native kernel, not an independently implemented external kernel.

The source/import audit uses Lean's own header parser for every indexed source.
The independent run first caught an auditor script error: a CRLF-only removal
left an LF-terminated obsolete import in place. The corrected source removes
that line. The failed attempt's raw receipts and logs are retained separately;
its source and index snapshots were reconstructed to their recorded hashes
after a late evidence copy. The 8,211 successful fresh compilations were reused
only after validating unchanged source/import records, direct dependencies,
compiler/recipe, artifacts and logs. Explicit reuse receipts preserve links to
the original compilation receipts. No author cached objects were reused.

Optional public-proof dependency/axiom checks use only the clean object tree:

  Set LEAN_PATH to the absolute BUILD/objects directory in your shell.
  PATH_TO_LEAN --run tools/PublicClosureCensus.lean
  PATH_TO_LEAN tools/StandardAxiomTypes.lean

The first command rejects missing, unsafe, partial, or unexpected-axiom proof
dependencies. The second checks the types of propext, Classical.choice, and
Quot.sound against their standard formulations.

Compiled objects and the Lean runtime are not included in the source ZIP.
The independently generated receipts, logs and successful final status are
included in evidence/independent_repair/clean_build. Cross-platform execution and
an official byte-level comparison of the local runtime are separate checks.
