# Verification

Lean 4.28.0 checked the formalization on Windows. The [toolchain pin](lean-toolchain) and [Lake manifest](lake-manifest.json) specify the versions, including Mathlib commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.

For the release run, a fresh project directory contained the release sources and no locally compiled project modules. The pinned dependency packages and their Mathlib cache were supplied from the installation on the same machine. Lake compiled the project modules through [the default library entry point](BooleanCube.lean).

* [Build log](verification/build.log)
* [Lean version](verification/toolchain.log)
* [Complete axiom reports](verification/axioms.log)
* [SHA-256 hashes of checked sources](verification/source-sha256.txt)

The [audit file](Audit.lean) requests the dependencies of 76 declarations, including Theorems A, B and C, both inequalities in (5), the unrestricted square and bilinear certificates, and their finite row-count bounds. The verification script checks the number of reports and the dependencies against the allowed set `propext`, `Classical.choice`, `Quot.sound`. It also scans project sources for proof placeholders and new axiom declarations.

Run the commands in the [README](README.md) with the pinned Lean toolchain. On PowerShell the build, source scan, axiom check and source hashing can be repeated together using `./verify.ps1 -LogDirectory ./audit-runs`. The PDF can be rebuilt with `tectonic paper.tex` in the [paper directory](paper/).
