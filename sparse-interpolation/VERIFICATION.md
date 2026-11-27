# Verification

The independent release replay compiled all 47 paper modules from the sources in [formal](formal/) in a new object directory. Lean 4.24.0 (commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`) treated warnings as errors. The replay checked the pinned dependency revisions, used compiled Mathlib dependencies, and checked the names and axiom sets for all 132 source-level requests. The reported axioms were `propext`, `Classical.choice` and `Quot.sound`. Each module’s source SHA-256, compiler status and axiom output appear in the [replay log](verification/lean-replay.txt). See the [replay instructions](README.md#reproduce-the-checks) and [release hashes](SHA256SUMS.txt).

The frozen manuscript also has a [single uninterrupted clean replay](verification/frozen-replay.txt) with the same 47 modules and 132 checks. Its original log SHA-256 is `db553de16eae27afd8df68ce016f6046e85b548897d7c5a547aaf455e87788e3`. The public copy normalizes line endings and omits the local dependency-cache path.

The independent release run resumed in its original, initially empty object directory after the Windows console failed to encode a mathematical symbol. The continuation checked the 39 recorded successful modules, source hashes, dependency closure and axiom reports, and compiled the remaining eight from source. The complete named axiom outputs were compared with the frozen replay. The release replay script writes UTF-8 for new runs.

| Manuscript result | Lean declaration |
| --- | --- |
| Theorem 1.1, worst-case prefix for each fixed ring and step | [GrenetPaper.four_t_worst_case](formal/GrenetPaper.lean) |
| Theorem 1.2, sharp threshold for each rational normalized start | [GrenetRational.rational_ratio_exact_manuscript](formal/RationalFinal.lean) |
| Theorem 1.2, least sufficient prefix | [GrenetRational.rational_ratio_least](formal/RationalFinal.lean) |

The [claim index](COVERAGE.md) maps the supporting results and mathematical appendix to individual declarations. The PDF, TeX and 47 Lean sources match the frozen research manuscript and project by SHA-256. The [Python regression](verification/check_rational.py) checks small determinants and explicit collisions by exact arithmetic. Its [output](verification/rational-check.json) is recorded separately.
