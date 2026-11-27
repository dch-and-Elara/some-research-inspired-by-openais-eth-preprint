"""Independent small determinant checks and exact threshold-minus-one witnesses."""
from fractions import Fraction
from itertools import combinations
from rational_prefix import minimum_prefix
import json


def det(matrix):
    a = [row[:] for row in matrix]
    prev, sign = 1, 1
    for j in range(len(a)-1):
        p = next((s for s in range(j,len(a)) if a[s][j]),None)
        if p is None:
            return 0
        if p!=j:
            a[p],a[j]=a[j],a[p]
            sign=-sign
        pivot = a[j][j]
        for i in range(j+1,len(a)):
            for h in range(j+1,len(a)):
                num = a[i][h]*pivot-a[i][j]*a[j][h]
                assert num % prev == 0
                a[i][h] = num//prev
        prev=pivot
    return sign*a[-1][-1]


def mult(f,g):
    h = [Fraction(0)]*(len(f)+len(g)-1)
    for i,u in enumerate(f):
        for j,v in enumerate(g):
            h[i+j] += u*v
    return h


def check():
    starts = sorted({Fraction(a,b) for a in range(-15,11) for b in range(1,9)})
    determinants, witnesses = 0,0
    for z in starts:
        for t in (1,2,3):
            k = 2*t
            s = minimum_prefix(z,1,t)
            points = [z+i for i in range(s)]
            old = points[:-1]
            if len(old)<k:
                f=[1]
                for v in old:
                    f=mult(f,[-v,1])
            else:
                f=[0,1]
                for v in sorted({abs(r) for r in old if r}):
                    f=mult(f,[-v*v,0,1])
            assert 0 < sum(c!=0 for c in f) <= k
            assert all(sum(c*v**j for j,c in enumerate(f))==0 for v in old)
            witnesses+=1
            if s==k:
                nodes=points
            else:
                nodes=next(xs[:k] for xs in ([r for r in points if r<0],[r for r in points if r>0]) if len(xs)>=k)
            values = [int(v*z.denominator) for v in nodes]
            for E in combinations(range(k+4),k):
                assert det([[v**e for e in E] for v in values])
                determinants+=1
    grid = [Fraction(a, b) for a in range(-70, 31) for b in range(1, 15)]
    boundary_checks = 0
    for z in grid:
        for t in range(1, 9):
            length = minimum_prefix(z, 1, t)
            assert length == minimum_prefix(-3 * z, -3, t)
            assert (length == 4 * t) == (z == -(2 * t - 1))
            boundary_checks += 1

    exceptional = [Fraction(0), Fraction(-1, 2), Fraction(-1), Fraction(-3, 2)]
    one_term = {str(z): minimum_prefix(z, 1, 1) for z in exceptional}
    assert list(one_term.values()) == [3, 3, 4, 2]
    t2_starts = [Fraction(-7, 3), Fraction(-5, 4), Fraction(-5, 2), Fraction(-3)]
    two_term = {str(z): minimum_prefix(z, 1, 2) for z in t2_starts}
    assert list(two_term.values()) == [4, 4, 7, 8]

    return dict(rational_starts=len(starts), threshold_minus_one_witnesses=witnesses,
                nonzero_determinants=determinants, scale_and_worst_start_pairs=boundary_checks,
                t1_examples=one_term, t2_examples=two_term)


if __name__=="__main__":
    print(json.dumps(check(),indent=2))
