"""Evaluate the two parameterizations directly, with no floating-point quantities."""
from collections import Counter
from math import isqrt

def sizes(n):
    original = [[(i, True)] for i in range(1,n+1)]
    guarded = [[(0, False), *cl] for cl in original]
    guarded += [[(0, True), (i, False)] for i in range(1,n+1)]
    degree = Counter(var for cl in guarded for var,_ in cl)
    occurrences = sum(map(len,guarded))
    tree_edges = sum(max(0, d-3) for d in degree.values())
    qh = occurrences + tree_edges
    sh = len(degree) + len(guarded)
    assert (sh,qh) == (3*n+1,6*n-3)
    m = 2*qh
    b=(m+1).bit_length()  # ceil(log2(m+2))
    lam=524288*b
    length=1 << (8*b)
    M=1 << lam
    sp=M-length*m+length*sh
    sl=M-length*m+length*qh
    assert (sp-1).bit_length() == (sl-1).bit_length() == lam
    denom=isqrt(lam)
    diff=(sl+denom-1)//denom - (sp+denom-1)//denom
    assert diff>0
    return (n,sh,qh,m,lam,denom,sl-sp,diff)
print("variables,source_native_size,subdivision_vertices,half_wires,lambda,isqrt_lambda,size_delta,cutoff_delta")
for n in (2,3,4,8,16):
    print(*sizes(n),sep=",")
