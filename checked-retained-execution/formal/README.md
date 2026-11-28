# Paper 6 Lean sources and replay

The directories below contain the complete source bytes of both verified Lean variants and their official endpoint audit sources. Main has 3,136 project modules. Binary J6 has 1,483. They share 1,479 byte-identical modules, stored once. The only module present in both variants with different bytes is `NativeProbeRing`. `manifest.json` selects the correct source layer for each variant and pins every source by SHA-256. It also records imports, ordered named axiom queries, endpoint declarations and the binary same-run checks.

[Browse all modules by name](module-index/README.md) · [Shared sources](sources/shared/) · [Main sources](sources/main/) · [Binary sources](sources/binary/) · [Main endpoint checks](checks/main/R119ReplayEndpointAudit.lean) · [Binary endpoint checks](checks/binary/R119ReplayEndpointAudit.lean)

## Verify and reconstruct

Run these commands from this directory with Python 3.11 or later. A stand-alone copy is also available in the [downloadable archive](Paper6_R119_Lean.zip). On Windows, `py -3 -B replay.py` is equivalent.

```sh
python3 -B replay.py verify
python3 -B replay.py export main exported-main
python3 -B replay.py export binary exported-binary
```

The main plan preserves historical alternative modules, including `J6R111KeptOwnerFlowGenerated` and `J6R111KeptOwnerFlowSelected`. They compile separately and a joint import of those two modules conflicts on `currentCol`. Reproduce the main plan by compiling modules according to their actual imports, followed by the prescribed endpoint audit. The separate audit of all main declarations uses import groups. A separate maintainer check reported that the binary variant's 1,483 project modules can be jointly imported. The replay procedure uses its prescribed endpoint audit for acceptance.

## Replay from empty project object directories

Install Git and Lean 4.24.0, pinned to commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`. An Elan installation uses the bundled `lean-toolchain`. Mathlib is pinned to `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`, and `pins.json` lists every external package revision. These commands use new output directories.

```sh
python3 -B replay.py setup mathlib
python3 -B replay.py replay main rebuilt-main --mathlib mathlib --jobs 2
python3 -B replay.py replay binary rebuilt-binary --mathlib mathlib --jobs 2
```

`setup` fetches the exact Mathlib commit and uses its Lake cache for external dependency objects. Use `setup mathlib --build-deps` to build the external dependencies instead. An existing locked Lake package directory can be supplied to `replay` with `--package-dir PATH`. Use `--lean PATH` and, for setup, `--lake PATH` to select explicit executables. Keep the two project outputs separate. The script accepts external library objects from the pinned dependency directories and generates every project object anew in its own output directory.

A full replay compiles each project source with `-j 1 -DwarningAsError=true`, verifies the ordered `#print axioms` names from that source, and admits only `propext`, `Classical.choice` and `Quot.sound`. It then runs the exact official audit source, which checks fully qualified names and module ownership. Binary also checks, for both general and fixed source precision, that the count and step bound project from the same named computation. Output includes the plan, per-module logs and receipts, the endpoint log and a summary with exit status. The assessment covers the probes listed in the sources and endpoint plans.

For a shorter check, use the actual dependency-closure entry:

```sh
python3 -B replay.py replay main smoke-main --mathlib mathlib --target J2R119ProbabilityBridge --jobs 1
python3 -B replay.py replay binary smoke-binary --mathlib mathlib --target NativeProbeRing --jobs 1
```

Target mode reports its limited module scope and omits the complete endpoint audit. This release was self-tested on Windows by verifying both source maps and executing these two closure replays with the pinned external dependency objects. The main test recompiled five modules and checked 25 named axiom reports. The binary test recompiled two modules. Dependency acquisition and a fresh full-project replay are reproduction paths provided by the script. The package preparation used the existing pinned external dependencies and did not run those longer paths.

## Verification evidence

`evidence/summary.json` records the final verification and original receipt hashes. The final verification was incremental. It checked the inherited source, object, log and receipt provenance, rebuilt the changed leaf modules, and then ran all prescribed endpoint checks over each resulting variant. The main route checked 11,810 per-module axiom reports and 36 endpoint reports. The binary route checked 5,505 per-module reports, 35 endpoint reports and two same-run checks.

`evidence/main/` and `evidence/binary/` contain the final raw endpoint logs, the raw leaf recompilation logs, and a path-independent per-module index with the original receipt, source, object and log hashes and named axiom results. The small tests use separate output directories. `evidence/self-test.json` records their actual scope. No compiled project objects or private machine paths are shipped.
