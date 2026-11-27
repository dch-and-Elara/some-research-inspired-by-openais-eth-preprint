# Paper 3: isolated, source-faithful follow-up

Base: public commit 95ad3fb52aeac8376ba835b76987ef5f9d6156d6 of
dch-and-Elara/some-research-inspired-by-openais-eth-preprint.
No public or frozen source was modified. replay.py checks the exact pinned
source manifest, every source listed in it, and the real dependency revisions
before compiling. The Lean toolchain is 4.24.0, commit
797c613eb9b6d4ec95db23e3e00af9ac6657f24b.

## Closed: Proposition 5, original whole-array Walsh choice

Paper 3, printed TeX L554–L576:
https://github.com/dch-and-Elara/some-research-inspired-by-openais-eth-preprint/blob/95ad3fb52aeac8376ba835b76987ef5f9d6156d6/reconstruction-studies/papers/paper_ternary_codes.tex#L554-L576

- P3WalshGeometry.lean gives an equivalence from assignments on the active
  physical slots to the actual fibre of the unordered-pair key; it proves
  that known inputs are exactly the opposite orientation on an active
  coordinate, and that the entire fibre is known at a genuinely inactive
  coordinate. The sum is reindexed through this actual finite equivalence.
- P3WalshAssembly.lean defines printedC as the actual constant row for each
  one-inactive orbit and the constant and actual full-parity Walsh rows on
  the all-active orbit. There are no rows on the smaller orbits.
- printedP is zero between distinct physical orbits; on each small orbit it
  is exactly the identity times the printed active-root gate and applies
  the printed 0 intercept exception only off the diagonal. On a
  one-inactive orbit the band is [1,h]; on the all-active orbit it is
  [1,h-1]. It uses the existing exact Walsh multipliers, not affine duality
  to choose a possibly different P.
- original_Walsh_attains takes q≥2 and the same distinct nonzero rational
  labels as in §5. It proves Orbitwise printedC, actual full-array
  PairedCondition for printedP (entrywise degree q−2, P(0)=I, exact
  physical side information for every output u, slot t, and input z), and
  exact rank 2q+2. The old affine method remains a second, independent
  proof of the numbered theorem.

Fresh strict receipt: audit_walsh_release_a/summary.json (2 modules / 13 checks),
SHA-256 b642a6ccacee7da457e849ad3c7d98d96640f48f4511a1d6bbc02dcf5e85786a.
Source SHA-256: geometry cbe81320fee07a20dcd7a1711e8c3fcc212a3bf259005f606715fbdbaca6456c;
assembly d22b50516c388dffa81696081f6115eab080ebe65d9f1010cd89871df649ce3a.
Only Lean standard dependencies (propext, Classical.choice, Quot.sound).

