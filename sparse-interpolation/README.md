# Sharp sample bounds for sparse interpolation on prescribed arithmetic progressions

How many consecutive exact evaluations distinguish all univariate polynomials with at most $t$ terms and no degree bound? Fix a nonzero commutative ring with identity whose additive group is torsion-free, and a step $b$ that is a non-zero-divisor. Starting at any $a$, the first $4t$ evaluations at $a+ib$ suffice. Starting at $a=-(2t-1)b$ in that same ring, even $4t-1$ evaluations can agree for two different polynomials.

For a rational normalized start $z$ (meaning $Ba=Ab$ and $z=A/B$ for integers $A,B$ with $B>0$), the paper gives the exact threshold for that particular progression. If $2z$ is not an integer, it is $2t$. Otherwise it is the first prefix containing $2t$ strictly positive or $2t$ strictly negative normalized nodes. At $t=2$, the starts $z=-7/3,-5/2,-3$ give thresholds $4,7,8$, respectively. These results address the uniqueness question in Grenet’s Open Problem 10.2 under the stated ring and step hypotheses. [Original question](https://arxiv.org/html/2511.11267v3#S10.SS1)

[Full paper (PDF)](paper/Grenet.pdf) · [LaTeX](paper/Grenet.tex) · [Lean claim index](COVERAGE.md) · [Verification record](VERIFICATION.md)

## Reproduce the checks

With Elan and Git installed, run these commands from the **formal** directory. The toolchain and dependency revisions are pinned there.

```sh
lake exe cache get
lake build
lake env lean FinalAudit.lean
```

To rebuild every paper module in a fresh directory, capture all its named axiom checks and reject unexpected axioms, run the following from the same directory with Python 3. The output directory must be new.

```sh
python ../verification/replay.py ../replay-objects
```

The exact-arithmetic regression uses only Python’s standard library. Run it with `python ../verification/check_rational.py`. Appendix B of the paper describes the use of AI in the derivation, formalization and drafting.
