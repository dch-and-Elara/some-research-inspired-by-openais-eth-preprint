# Exact joint acquisition from supplied plans

The [native scalar identity](lean/P6JointActualPartitions.lean) and [pool-to-receiver bridge](lean/P6JointPhysicalPool.lean) compare an exact joint evaluation with the same R119 singleton receipt, including its (10M)-bit projection. The [arithmetic bound](lean/P6JointPool.lean) assumes supplied, checked table contraction plans and precomputed weights. It includes neither a compiler from arbitrary graph decompositions nor a bit-time bound for the printed routine. No division by group partition values is required.

The [diagonal-page theorem](lean/P6ActualDiagonalSource.lean) proves a lower bound on ordinary factor support in an actual diagonal packet at nonzero original binary probes, under the stated layout, load and precision guards. It rules out a small-width directly tabulated representation at that page, not every exact evaluation algorithm. [Replay records](audit/) cover the 18 modules of the two new overlays against the unchanged R119 main objects.

## Reproduction

Use Lean 4.24.0 (`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`), Mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`, and the matching prebuilt original proof objects and package imports. Run `./replay.ps1 -Lean <lean> -BaseLeanPath <ordered import directories>` with PowerShell 7. The script recompiles this supplement in a new directory, with warnings treated as errors. It does not rebuild the legacy baseline. See `audit/` and `SHA256SUMS.txt` for the original evidence and delivered-file hashes.
