# Optimal Degrees for Local Polynomial Reconstruction on the Boolean Cube

Chuhang Ding (Peking University)

[PDF](paper/paper.pdf) · [LaTeX source](paper/paper.tex) · [AI disclosure](../AI_DISCLOSURE.md)

[Lean source](BooleanCube/) · [Theorem index](FORMALIZATION_SCOPE.md) · [Verification record](VERIFICATION.md) · [Supplement coverage](supplements/COVERAGE.md)

Run from this directory:

~~~sh
lake exe cache get
lake build
lake env lean Audit.lean
~~~

On Windows, run ./verify.ps1 -LogDirectory ./audit-runs to record the build and axiom audit.
