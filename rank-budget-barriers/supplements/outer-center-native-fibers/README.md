# Native outer-center fibers

For the original and four-clone cubic triangle-replacement constructions, the checked result produces two isolated factor switches. Each switch changes one terminal factor from 1 to 0, preserves the other, and changes the actual model count from 1 to 0. For each witness, the original Appendix D child reads agree across all selected outer centers, groups and legal modes at the native register precision. The observation is the legal **zero local probe** at each selected nonzero center; it does not cover nonzero local probes, interior centers, MAIN, or acquisition time. The verified outer window can include a center of every retained level under the stated width guard.

Endpoints: [factor witnesses](lean/P5OuterCenterFactorReadouts.lean), [uncloned root](lean/P5OuterCenterRootExact.lean), [cloned root](lean/P5OuterCenterCloneRoot.lean), [original address binding](lean/P5OuterCenterPacketAddress.lean). The separate [MAIN schedule lemma](lean/P5EditorialSchedule.lean) bounds the printed ambient tuple box under its retained-row hypothesis. The source and log checks are in [audit](audit/).

Replay against the previously checked Paper 5 C17 and Section 8 supplement objects and the pinned Mathlib dependencies, with the Section 8 objects ahead of C17 in the import path. The recorded legacy reference is commit `8e4dc6406471869332fa103c5f4339baa26d8ae6`; the original version of this paper and its formalization remain unchanged.

## Reproduction

Use Lean 4.24.0 (`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`), Mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`, and the matching prebuilt original proof objects and package imports. Run `./replay.ps1 -Lean <lean> -BaseLeanPath <ordered import directories>` with PowerShell 7. The script recompiles this supplement in a new directory, with warnings treated as errors. It does not rebuild the legacy baseline. See `audit/` and `SHA256SUMS.txt` for the original evidence and delivered-file hashes.
