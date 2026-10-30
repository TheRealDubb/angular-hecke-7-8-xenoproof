# Reproducing the public source closure

Use Python 3.10 or later and the exact Lean version and revision in
[metadata/DEPENDENCY_PINS.json](metadata/DEPENDENCY_PINS.json). Obtain the toolchain
separately. No toolchain binaries or compiled object caches are included.

From the repository root, first perform these inexpensive checks:

```powershell
python -B verify_package.py --assets ..\release-assets
python -B tools/rebuild_from_source.py --plan
```

For a full reproduction, substitute executable paths below. Choose new build
directories outside the repository. These steps take substantial time and memory:

```powershell
python -B tools/audit_source_imports.py --lean PATH_TO_LEAN --build-dir ..\import-check
python -B tools/clean_build.py --lean PATH_TO_LEAN --build-dir ..\clean-build --jobs 1
python -B tools/replay_clean_build.py --lean PATH_TO_LEAN --checker PATH_TO_LEANCHECKER --build-dir ..\clean-build
```

The clean builder replaces LEAN_PATH and builds the indexed closure. A new build
does not use historical author setup files or receipts. The replay verifies its
own outputs and checks both public roots, the proof census, and standard axiom types.
The copied scripts are unchanged from the reviewed repair. Their recorded Windows
run used three scheduled workers; one is shown here to limit memory pressure.

The repository contains every source and resource required by the build plan.
For the original complete evidence, extract the repaired ZIP from the release
assets and run its original `tools/verify_manifest.py`. Its `REPAIR_README.txt`
governs the repair; older narrative documents in that archive retain explicitly
historical status. The curated repository uses `verify_package.py` and its own
manifest. Integrity checks are not mathematical verification.
