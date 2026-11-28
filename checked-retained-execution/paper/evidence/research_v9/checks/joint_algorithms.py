#!/usr/bin/env python3
"""Exact finite checks for J1--J6. Only the Python standard library is required."""
from collections import Counter, defaultdict, deque
from fractions import Fraction as F
from itertools import combinations, product
import json
from math import factorial, prod
from pathlib import Path
from random import Random

OUT = Path(__file__).with_suffix(".json")


def words(n):
    return product((0, 1), repeat=n)


def add_term(target, key, value):
    target[key] = target.get(key, 0) + value


def auxiliary_rows(a, d, low=1, length=2):
    """Build V f(W) on the actual swap orbit, then apply the printed mismatch factors."""
    q = len(a)
    differing = [i for i in range(q) if a[i] != d[i]]
    full = (1 << len(differing)) - 1
    powers = {0: F(1)}
    f = {}
    for degree in range(length):
        for mask, value in powers.items():
            add_term(f, mask, (-1) ** low * (-2) ** degree * value)
        nxt = {}
        for mask, value in powers.items():
            add_term(nxt, mask, F(len(differing), 2) * value - (low + degree) * value)
            for j in range(len(differing)):
                add_term(nxt, mask ^ (1 << j), -value / 2)
        powers = {k: v / (degree + 1) for k, v in nxt.items() if v}
    result = {}
    for previous, coefficient in f.items():
        mask = previous ^ full
        y, h = list(a), list(d)
        for j, idx in enumerate(differing):
            if mask & (1 << j):
                y[idx], h[idx] = h[idx], y[idx]
        phi = [F(1)]
        for i in range(q):
            if y[i] != d[i]:
                phi = [x + z for x, z in zip(phi + [0], [0] + [-v / (i + 1) for v in phi])]
        phi[0] -= 1
        result[tuple(y), tuple(h)] = [coefficient * v for v in phi]
    polynomial = result.setdefault((a, d), [F(0)])
    polynomial[0] += 1
    return {k: v for k, v in result.items() if any(v)}


def value_and_derivative(polynomial, t):
    return (sum(v * t ** i for i, v in enumerate(polynomial)),
            sum(i * v * t ** (i - 1) for i, v in enumerate(polynomial) if i))


def main_geometry_and_derivatives():
    diagonals, checked = 0, 0
    for q in (2, 3, 4):
        for a in words(q):
            for d in words(q):
                rows = auxiliary_rows(a, d)
                checked += 1
                assert all(c[0] == int(key == (a, d)) for key, c in rows.items())
                if a == d:
                    assert rows == {(a, d): [F(1)]}
                    # The weight-zero tensor factor is a singleton indicator.
                    assert sum(all((v, v) == (x, y) for v, x, y in zip(a, ab, cd))
                               for ab in words(q) for cd in words(q)) == 1
                    diagonals += 1
    u = ((0, 0, 0), (1, 1, 1))
    y = ((1, 0, 1), (0, 1, 0))
    # Two copies, each with a unary pin at u and a positive witness unary at y.
    local_rows = [auxiliary_rows(*k) for k in (u, y)]
    vectors = [[value_and_derivative(row.get(addr, [0]), 1) for addr in (u, y)]
               for row in local_rows]
    theta, witness = [sum(v for v, _ in row) for row in vectors]
    assert theta not in (0, 1) and witness
    recovered = []
    for sign in words(2):
        pin = [theta if s else 1 - theta for s in sign]
        base = prod(pin) * witness ** 2
        solutions = []
        for slot in range(2):
            # Use its witness variable as direction. The two selected equations are diagonal.
            d, dw = vectors[0][1][1], vectors[1][1][1]
            fs = [pin[0], witness, pin[1], witness]
            derivative = [F(0)] * 4
            derivative[2 * slot] = d if sign[slot] else -d
            derivative[2 * slot + 1] = dw
            h = sum(dp * prod(fs[:j] + fs[j + 1:]) for j, dp in enumerate(derivative))
            rhs = h / base - dw / witness + d / (1 - theta)
            solutions.append(rhs / (d / (theta * (1 - theta))))
        assert tuple(solutions) == sign
        recovered.append(list(map(int, solutions)))
    return {"auxiliary_orbits_rows": checked, "diagonal_cells": diagonals,
            "test_theta": str(theta), "exact_derivative_decodings": recovered}


def cylinder_checks():
    # Directed K4 ports are the vertices of its triangle replacement.
    nodes = [(i, j) for i in range(4) for j in range(4) if i != j]
    inside = [(a, b) for a, b in combinations(nodes, 2) if a[0] == b[0]]
    outside = [(a, (a[1], a[0])) for a in nodes if a[0] < a[1]]
    edges = inside + outside
    h = []
    for v in nodes:
        if 0 in v or any(set((v, u)) in map(set, edges) for u in h):
            continue
        h.append(v)
    assert len(h) >= 2
    labels = {v: (i % 2, (i + 1) % 2) for i, v in enumerate(h)}
    patterns = list(words(len(h)))
    groups = [[j for j, v in enumerate(h) if labels[v][t] == g] for t in range(2) for g in (0, 1)]
    cylinders = []
    for group in groups + [list(range(len(h)))]:
        for pattern in words(len(group)):
            hit = {w for w in patterns if tuple(w[i] for i in group) == pattern}
            assert len(hit) == 2 ** (len(h) - len(group))
            cylinders.append(hit)
    tried = 0
    for length in range(min(len(patterns), 3) + 1):
        for reads in combinations(cylinders, length):
            union = set().union(*reads)
            assert len(union) <= sum(map(len, reads))
            if len(union) < len(patterns):
                pattern = next(w for w in patterns if w not in union)
                s = dict(zip(h, pattern))
                value = lambda ee: int(all(s.get(u, 1) or s.get(v, 1) for u, v in ee))
                assert [value(inside), value(outside), value(edges)] == [1, 1, 1]
                s[(0, 1)] = s[(0, 2)] = 0
                assert [value(inside), value(outside), value(edges)] == [0, 1, 0]
            tried += 1
    # Conditional binomial means and variances by exhaustive independent labels of two candidates.
    label_words = list(words(2))
    data = []
    for row in product(label_words, repeat=4):
        count = sum(row[2*j] == row[2*j+1] and row[2*j][0] == 0 for j in range(2))
        data.append(count)
    mu = F(sum(data), len(data))
    var = sum((v - mu) ** 2 for v in data) / len(data)
    assert mu == F(1, 4) and var == 2 * F(1, 8) * F(7, 8)
    return {"graph_vertices":len(nodes), "independent_candidate_vertices":len(h),
            "support_cylinder_unions":tried, "binomial_mean":str(mu), "binomial_variance":str(var)}


def shift(packets, t):
    pairs = {}
    for packet in packets:
        for pos, x in enumerate(packet):
            if x is not None and 0 <= pos + t < len(packet) and packet[pos + t] is not None:
                pairs[x] = packet[pos + t]
    assert len(set(pairs.values())) == len(pairs)
    return pairs


def coeff(length, t):
    return (-1 if t % 2 else 1) * F(factorial(length+t)*factorial(length-1-t),
                                     factorial(length)*factorial(length-1))


def residue(x, q):
    v = F(x)
    return v.numerator * pow(v.denominator, -1, q) % q


def tensor(ids, table):
    return (tuple(ids), dict(zip(words(len(ids)), table)))


def table_value(vertices, assignment):
    return prod(data[tuple(assignment[i] for i in ports)] for ports, data in vertices)


def row_mle(vertices, pair, assign, c, mod):
    out = 1
    for ports, data in vertices:
        args = [c * assign[pair[i]] if i in pair else 0 for i in ports]
        total = sum(v * prod(arg if bit else 1-arg for arg, bit in zip(args, w))
                    for w, v in data.items())
        out = out * total % mod
    return out


def direct_distribution(rows, cols, pair, features, c, mod):
    """Independent literal X,Y sum, including all unmatched Boolean ports."""
    rids = [i for ports, _ in rows for i in ports]
    cids = [i for ports, _ in cols for i in ports]
    row_inputs = [(w, table_value(rows, dict(zip(rids, w)))) for w in words(len(rids))]
    out = Counter()
    for x in words(len(cids)):
        assign = dict(zip(cids, x))
        weight = table_value(cols, assign)
        args = [c * assign[pair[i]] if i in pair else 0 for i in rids]
        val = sum(wt * prod(z if bit else 1-z for bit, z in zip(w, args))
                  for w, wt in row_inputs)
        index = tuple(sum(w * assign[i] for i, w in feat.items()) for feat in features)
        out[index] = (out[index] + weight * val) % mod
    return {k:v for k,v in out.items() if v}


def fused_distribution(rows, cols, pair, features, c, mod, xor=False):
    mids = list(pair.values())
    out = Counter()
    for matched in words(len(mids)):
        assigned = dict(zip(mids, matched))
        wr = row_mle(rows, pair, assigned, c, mod)
        dist = {tuple(0 for _ in features): 1}
        for ids, tab in cols:
            nxt = Counter()
            for bits, weight in tab.items():
                if any(i in assigned and b != assigned[i] for i,b in zip(ids,bits)):
                    continue
                delta = [sum(f.get(i,0)*b for i,b in zip(ids,bits)) for f in features]
                for prev, entry in dist.items():
                    key = tuple((e+d)%2 if xor else e+d for e,d in zip(prev,delta))
                    nxt[key] = (nxt[key] + weight*entry) % mod
            dist = nxt
        for key, weight in dist.items():
            out[key] = (out[key] + wr*weight) % mod
    return {k:v for k,v in out.items() if v}


def contraction_checks():
    rng = Random(107)
    rows = [tensor((0,3),(0,1,1,1)), tensor((1,2,4),(1,0,0,0,0,0,0,1)),
            tensor((),(3,))]
    cols = [tensor((0,1),(1,0,0,1)), tensor((2,4),(0,3,2,1)),
            tensor((3,),(1,2)),tensor((),(5,))]
    trials = 0
    for h in range(7):
        slots = [0,1,2,3,4,None,None,None]
        rng.shuffle(slots)
        packets = [slots[:4],slots[4:]]
        for t in (-3,-1,1,3):
            pair = shift(packets,t)
            assert len(pair) <= 2*(4-abs(t))
            for mod in (2,128,8192):
                c = residue(coeff(4,t),mod)
                assert direct_distribution(rows,cols,pair,[],c,mod) == fused_distribution(
                    rows,cols,pair,[],c,mod)
                trials += 1
    # Two actual mixed-source tiles in one child of two opposite-symbol packets.
    # At i=0 row group g takes odd positions; columns of g take even positions.
    all_packets = [list(range(8)),list(range(8,16))]
    ri = [1,3,5,7,9,11,13,15]
    ci = [0,2,4,6,8,10,12,14]
    rows = [tensor(ri[j:j+2], [rng.randrange(4) for _ in range(4)]) for j in (0,2,4,6)]
    cols = [tensor((ci[j],ci[j+4]), [rng.randrange(4) for _ in range(4)]) for j in range(4)]
    # Deterministic terms keep odd parities present while preserving sign cancellation in kernels.
    cols[0] = tensor((ci[0],ci[4]),(1,0,1,1))
    powers = range(3)
    features = [{8*tile+2*j:j**b for j in range(4)} for tile in range(2) for b in powers]
    mod = 8192
    pair = {x:y for x,y in shift(all_packets,-7).items() if x in ri and y in ci}
    c = residue(coeff(8,-7),mod)
    direct = direct_distribution(rows,cols,pair,features,c,mod)
    fused = fused_distribution(rows,cols,pair,features,c,mod)
    assert direct == fused and fused
    parity_features = [features[j] for j in (0,1,3,4)]
    parity = fused_distribution(rows,cols,pair,parity_features,c%2,2,xor=True)
    compressed = Counter()
    for key,v in direct.items():
        feat = tuple(key[j]%2 for j in (0,1,3,4))
        compressed[feat] = (compressed[feat] + v)%2
    assert parity == {k:v for k,v in compressed.items() if v}
    # Second instance deliberately has mixed nonzero parity values.
    rows2 = [tensor((i,), (1,1)) for i in ri]
    cols2 = [tensor((i,), (0,1) if j in (0,1,5) else (1,0)) for j,i in enumerate(ci)]
    parity2 = fused_distribution(rows2,cols2,pair,parity_features,c%2,2,xor=True)
    assert parity2
    nonzero = 0
    for pr, rr, cc in [(parity,rows,cols), (parity2,rows2,cols2)]:
        truth = direct_distribution(rr,cc,pair,parity_features,c%2,2)
        # Superset zeta transform of exact XOR-pattern weights.
        arr = [pr.get(tuple((i>>j)&1 for j in range(4)),0) for i in range(16)]
        for j in range(4):
            for i in range(16):
                if not i & (1<<j):
                    arr[i] ^= arr[i|(1<<j)]
        for mask,val in enumerate(arr):
            expected = sum(weight*prod(key[j]%2 for j in range(4) if mask&(1<<j))
                           for key,weight in truth.items()) % 2
            assert val == expected
            nonzero += val
    mixes = 0
    for beta in product(range(3),repeat=6):
        a = sum(weight*prod(pow(k,ex,mod) for k,ex in zip(key,beta))
                for key,weight in direct.items())%mod
        b = sum(weight*prod(pow(k,ex,mod) for k,ex in zip(key,beta))
                for key,weight in fused.items())%mod
        assert a == b
        mixes += 1
    return {"literal_root_sums":trials,"high_precision_mixed_moments":mixes,
            "matched_columns":len(pair),"nonzero_high_precision_profiles":len(fused),
            "parity_moments_verified":32,"nonzero_parity_moments":nonzero}


def physical(cnf):
    occurrences = defaultdict(list)
    rows = []
    edge = 0
    for clause in cnf:
        ids = []
        for literal in clause:
            ids.append(2*edge)
            occurrences[abs(literal)].append(2*edge+1)
            edge += 1
        rows.append(tensor(ids,[int(any(bit == (lit>0) for bit,lit in zip(w,clause)))
                                for w in words(len(ids))]))
    for ids in occurrences.values():
        assert len(ids) <= 3
        rows.append(tensor(ids, [int(len(set(w)) <= 1) for w in words(len(ids))]))
    return rows, {j: j//2 for j in range(2*edge)}


def graph_for_test(cnf, length, balanced):
    base, original_owner = physical(cnf)
    m = len(original_owner)
    planted_q = m // 2
    rows, owner = [], {}
    packets = [[j*m+i for j in range(length)] for i in range(m)]
    for j in range(length):
        rows.extend((tuple(j*m+i for i in ids), tab) for ids,tab in base)
        owner.update({j*m+i:j*planted_q+z for i,z in original_owner.items()})
    next_port, next_col = len(owner), length*planted_q
    initial_cols = next_col
    negative = set()
    cells = defaultdict(deque)
    hpad = length * m + length
    label_count = length if balanced else 1
    for a in range(label_count):
        for b in range(label_count):
            n = (hpad - (length*m if (a,b) == (0,0) else 0))//2 if balanced else length
            for _ in range(n):
                rows.extend([tensor((next_port,), (1,0)), tensor((next_port+1,), (1,1))])
                negative.add(next_port)
                for i in (next_port,next_port+1):
                    cells[a,b].append(i)
                    owner[i] = next_col
                next_port += 2
                next_col += 1
    if balanced:
        a = length.bit_length()-1
        cell_templates = defaultdict(list)
        for left in range(length):
            for right in range(length):
                template = tuple(tuple(sorted(((left>>j)&1,(right>>j)&1))) for j in range(a))
                cell_templates[template].append((left,right))
        for template, ordered in cell_templates.items():
            total = sum(len(cells[key]) for key in ordered)
            assert total % length == 0
            for _ in range(total//length):
                packet = []
                for slot in range(length):
                    left = sum(pair[(slot>>i)&1]<<i for i,pair in enumerate(template))
                    right = sum(pair[1-((slot>>i)&1)]<<i for i,pair in enumerate(template))
                    packet.append(cells[left,right].popleft())
                packets.append(packet)
        assert next_port == hpad * length ** 2 and not any(cells.values())
    else:
        pad = list(cells[0,0])
        packets.extend(pad[i:i+length] for i in range(0,len(pad),length))
    assert sorted(i for p in packets for i in p) == list(range(next_port))
    return rows, owner, packets, initial_cols, negative


def components_contraction(rows, owner, pairs, c):
    """Independent full shifted contraction by connected components, without layer grouping."""
    roots = {v:v for v in owner.values()}
    def root(v):
        while roots[v] != v:
            v, roots[v] = roots[v], roots[roots[v]]
        return v
    factors = []
    scalar = F(1)
    for ids, tab in rows:
        reached = [owner[pairs[i]] if i in pairs else None for i in ids]
        scope = tuple(sorted(set(reached) - {None}))
        entry = {}
        for bits in words(len(scope)):
            assign = dict(zip(scope,bits))
            args = [0 if i is None else c*assign[i] for i in reached]
            entry[bits] = sum(wt*prod(arg if b else 1-arg for arg,b in zip(args,y))
                              for y,wt in tab.items())
        if scope:
            for x in scope[1:]:
                roots[root(x)] = root(scope[0])
            factors.append((scope,entry))
        else:
            scalar *= entry[()]
    groups, fgroups = defaultdict(list), defaultdict(list)
    for v in roots:
        groups[root(v)].append(v)
    for scope,tab in factors:
        fgroups[root(scope[0])].append((scope,tab))
    for k, ids in groups.items():
        scalar *= sum(table_value(fgroups[k],dict(zip(ids,bits))) for bits in words(len(ids)))
    return scalar,max(map(len,groups.values()),default=0)


def independent_single_layer(cnf, c):
    rows, own = physical(cnf)
    ports = sorted(own)
    ywords = [(bits,table_value(rows,dict(zip(ports,bits)))) for bits in words(len(ports))]
    total = F(0)
    for xb in words(len(ports)//2):
        vals = [c*xb[own[i]] for i in ports]
        total += sum(weight*prod(z if q else 1-z for z,q in zip(vals,y))
                     for y,weight in ywords if weight)
    return total


def exact_odd_root(value, degree):
    assert degree%2
    def integer(n):
        if n < 0:
            return -integer(-n)
        lo, hi = 0, 1 << ((n.bit_length()+degree-1)//degree)
        while lo <= hi:
            mid = (lo+hi)//2
            power = mid**degree
            if power == n:
                return mid
            if power < n:
                lo = mid+1
            else:
                hi = mid-1
        raise AssertionError("expected a perfect power")
    return F(integer(value.numerator), integer(value.denominator))


def cnf_counts(cnf,n):
    return sum(all(any(bool(bits[abs(lit)-1]) == (lit>0) for lit in clause)
                   for clause in cnf) for bits in words(n))


def uniform_reduction_checks():
    rng = Random(703)
    for n in range(1,5):
        for _ in range(15):
            cnf = [tuple((1 if rng.randrange(2) else -1)*v
                         for v in rng.sample(range(1,n+1),rng.randint(1,min(3,n))))
                   for _ in range(rng.randint(1,7))]
            guarded = [(-(n+1),)+clause for clause in cnf]+[(n+1,-i-1) for i in range(n)]
            assert cnf_counts(guarded,n+1) == 1+cnf_counts(cnf,n)
            assert all(any(l<0 for l in clause) for clause in guarded)
    results = []
    for cnf,length,balanced in [([(-1,-2)],4,True), ([(-1,-2)],16,False),
                                ([(-1,2),(-1,-2)],32,False)]:
        rows,owner,packets,first_pad,negative = graph_for_test(cnf,length,balanced)
        m = sum(2*len(clause) for clause in cnf)
        ts = [1,3] if balanced else list(range(1,2*m+2,2))
        nodes, observed = [], []
        maxbits = maxcomp = 0
        for t in ts:
            c = coeff(length,t)
            assert c < 0 and c.denominator%2
            pairs = shift(packets,t)
            actual,width = components_contraction(rows,owner,pairs,c)
            maxcomp = max(maxcomp,width)
            reached = Counter(owner[y] for x,y in pairs.items() if x in negative)
            padding = prod(1 + (1-c)**reached[i] for i in set(owner.values()) if i>=first_pad)
            assert padding > 0
            mult = padding * (1 << (t*(m//2)))
            independent = independent_single_layer(cnf,c)
            assert actual == mult * independent**(length-t)
            pcheck = len(owner)*(3+t*length.bit_length())+3
            modulus = 1<<pcheck
            cleared = (residue(actual,modulus)*pow(c.denominator,len(owner),modulus))%modulus
            if cleared >= modulus//2:
                cleared -= modulus
            decoded = F(cleared,c.denominator**len(owner))
            assert decoded == actual
            got = exact_odd_root(decoded/mult,length-t)
            assert got == independent
            nodes.append(c)
            observed.append(got)
            maxbits = max(maxbits,actual.numerator.bit_length(),actual.denominator.bit_length())
        target = cnf_counts(cnf,2)
        if len(ts) == m+1:
            val = sum(v*prod((1-xj)/(xi-xj) for j,xj in enumerate(nodes) if i!=j)
                      for i,(xi,v) in enumerate(zip(nodes,observed)))
            assert val == target
        results.append({"clause_set":cnf,"L":length,"balanced_toy":balanced,
                        "actual_wires":len(owner),"odd_grid_nodes":len(ts),"max_component":maxcomp,
                        "max_bits_in_exact_fraction":maxbits,"target_models":target,
                        "full_interpolation":len(ts)==m+1,
                        "negative_samples":sum(v<0 for v in observed)})
    for degree in (1,3,9):
        for v in (F(-11,7),F(0),F(5,3)):
            assert exact_odd_root(v**degree,degree) == v
    schedules = []
    for m in (4,16,70,508):
        b = (m+1).bit_length()
        lam = 4*b*131072
        length, u = 1<<(8*b), 4*b
        arr = length**12
        M = 1<<lam
        load = M//arr
        s = M - length*(m-m//2)
        assert s.bit_length() == lam and M == arr*load and load%(2*length)==0
        assert load > length*m and length>2*m+1
        # Integer upper bound for ceil(s^.9), avoiding fractional floating-point powers.
        dupper = (1<<((9*lam+9)//10))+1
        assert M>=2*arr**2*dupper and M>=length*arr and 2*length<=1<<(9*lam//10)
        pt_lower = 24*M*length//u
        assert M*(3+(2*m+1)*(8*b+1))+1 < pt_lower
        schedules.append({"planted_wires":m,"lambda":lam,"L":length,"native_bit_bound":True})
    return {"guarded_formula_comparisons":60,"actual_shifted_clause_networks":results,
            "exact_odd_root_sign_tests":9,"printed_parameter_arithmetic":schedules}



def nonconstant_outer_check():
    # Literal four-clone CNF on the triangle replacement of K4.
    nodes = [(i,j) for i in range(4) for j in range(4) if i!=j]
    graph_edges = [(a,b) for a,b in combinations(nodes,2) if a[0] == b[0] or a == b[::-1]]
    vid = {v:i for i,v in enumerate(nodes)}
    def literal(v,j):
        return 1+4*vid[v]+j
    def endpoint_formula(positive):
        used = Counter()
        clauses = [(literal(v,0) if v in positive else -literal(v,0),) for v in nodes]
        for a,b in graph_edges:
            used[a] += 1
            used[b] += 1
            clauses.append((literal(a,used[a]),literal(b,used[b])))
        clauses.extend([(-literal(v,j),literal(v,(j+1)%4)) for v in nodes for j in range(4)])
        return clauses
    old_vertices, subdivision = physical(endpoint_formula(set()))
    m = len(subdivision)
    length = 32
    assert m == 288 and m%length == 0
    packet_count = m//length
    old_owner = {port:j for j,(ids,_) in enumerate(old_vertices) for port in ids}
    pins = {old_vertices[j][0][0]:v for j,v in enumerate(nodes)}
    row_used, col_used, matched_wires = set(), set(), []
    def add_match(edge):
        if subdivision[edge] in row_used or old_owner[edge] in col_used:
            return False
        row_used.add(subdivision[edge])
        col_used.add(old_owner[edge])
        matched_wires.append(edge)
        return True
    for p in list(pins)[:3]:
        assert add_match(p)
    for p in sorted(subdivision):
        if p not in pins:
            add_match(p)
        if len(matched_wires) == 2*packet_count:
            break
    assert len(matched_wires) == 2*packet_count
    endings = matched_wires[:packet_count]
    starts = matched_wires[packet_count:]
    middle = deque(sorted(set(subdivision)-set(matched_wires)))
    packets = [[starts[k]]+[middle.popleft() for _ in range(length-2)]+[endings[k]]
               for k in range(packet_count)]
    assert not middle
    t = length-1
    pairs = shift(packets,t)
    qualifying = {pins[y] for y in pairs.values() if y in pins}
    assert len(qualifying) == 3
    rows = [tensor((2*j,2*j+1),(1,0,0,1)) for j in range(m//2)]
    mod = 1<<2048
    c = coeff(length,t)
    assert c.denominator == 1
    values = {}
    for bits in words(3):
        pos = set(v for v,b in zip(sorted(qualifying),bits) if b)
        cols,_ = physical(endpoint_formula(pos))
        uniform = fused_distribution(rows,cols,pairs,[],residue(c,mod),mod)
        val = uniform.get((),0)
        if not bits.count(1):
            baseline = val
        assert val == baseline*(1-int(c))**sum(bits) and 0 < val < mod
        values[sum(bits)] = val
    return {"actual_four_clone_wires":m,"toy_packet_L":length,"shift_pairs":len(pairs),
            "independently_varied_matched_pins":len(qualifying),"tested_sign_words":8,
            "distinct_native_positive_values":len(set(values.values())),
            "value_bit_lengths_by_weight":[values[k].bit_length() for k in range(4)]}


def main():
    data = {"main_source_rows_and_derivatives":main_geometry_and_derivatives(),
            "support_and_witnesses":cylinder_checks(),"D_contraction":contraction_checks(),
            "physical_uniform_reduction":uniform_reduction_checks(),
            "nonconstant_outer_register":nonconstant_outer_check()}
    OUT.write_text(json.dumps(data,indent=2,sort_keys=True)+"\n")
    print(json.dumps(data,sort_keys=True))


if __name__ == "__main__":
    main()
