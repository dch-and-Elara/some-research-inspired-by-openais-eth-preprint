# Same-layout erasure and recovery

The [main theorem](lean/P6JointWorld.lean) constructs one legal, sign-independent layout on the original four-clone cubic host. It preserves the original ordered-cell collision certificate. On that same layout and literal file for each sign input, every nonzero printed center, legal mode and original probe gives zero projected to a common low precision. At the extreme odd center, the fixed public prefix of (N(10M+1)) completed addresses, projected to (10M) bits, recovers all pin signs. The register precision is sufficient for both projections. The result retains the original root bounds, monic polynomial with irreducible mod-2 residue, and positive inlet parameters. The [finite cap estimate](lean/P6JointCalibrated.lean) records the guard-count losses explicitly.

The high route requires distinct matched first-side rows, not distinct last-side column vertices. Distinct physical ports are still preserved. The theorem does not claim individually cheap completed probes or address MAIN. This [33-module replay](audit/replay.json) recompiled the full new proof overlay against the unchanged R119 main objects; it is not a new whole-project replay of R119.

## Reproduction

Use Lean 4.24.0 (`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`), Mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`, and the matching prebuilt original proof objects and package imports. Run `./replay.ps1 -Lean <lean> -BaseLeanPath <ordered import directories>` with PowerShell 7. The script recompiles this supplement in a new directory, with warnings treated as errors. It does not rebuild the legacy baseline. See `audit/` and `SHA256SUMS.txt` for the original evidence and delivered-file hashes.
