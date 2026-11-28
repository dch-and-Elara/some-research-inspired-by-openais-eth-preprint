#!/usr/bin/env python3
"""Finite independent exercises for A1--A5. Uses only the Python standard library."""
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, product
from math import prod
import json


def bit_words(d):
    return product((0, 1), repeat=d)


def kernel(length, t, delta):
    grid = range(-length, length)
    return Fraction(prod(t-q for q in grid if q != delta),
                    prod(-q for q in grid if q != 0))


def cauchy_checks():
    tests = 0
    for length in (2, 4, 8, 16):
        for delta in range(1-length, length):
            assert kernel(length, -1, delta) == (-1 if delta == -1 else 0)
            tests += 1
    return tests


def spin_weight(y, argument):
    return argument if y else 1 - argument


def signed_row_value(table, arguments):
    return sum(table[y] * prod(spin_weight(b, x) for b, x in zip(y, arguments))
               for y in bit_words(len(arguments)))


def binary_factors():
    checks = 0
    for d in (1, 2, 3):
        xs = list(bit_words(d))
        for word in bit_words(len(xs)):
            f = dict(zip(xs, word))
            table = {y+z: f[tuple(a*b for a, b in zip(y, z))]
                     for y in xs for z in xs}
            for x in xs:
                assert signed_row_value(table, tuple(-a for a in x)+(-1,)*d) == f[x]
                checks += 1
    return checks


def template_slots(r, a, load):
    """Print all complete ordered classes using the source's orientation rule."""
    length = 1 << a
    assert load % length == 0
    cell_count = Counter()
    even_pairs = defaultdict(list)
    packets = []
    symbol_pairs = list(combinations(range(r), 2)) + [(x, x) for x in range(r)]
    for template in product(symbol_pairs, repeat=a):
        distinct = sum(x != y for x, y in template)
        for _ in range(load * (1 << distinct) // length):
            pid = len(packets)
            labels = []
            for x in range(length):
                oriented = [pair if not (x >> j & 1) else pair[::-1]
                            for j, pair in enumerate(template)]
                row, col = zip(*oriented)
                pair = (row, col)
                labels.append(pair)
                cell_count[pair] += 1
            for y in range(0, length, 2):
                if labels[y] == labels[y+1]:
                    even_pairs[labels[y]].append((pid, y))
            packets.append(labels)
    assert len(cell_count) == r**(2*a)
    assert set(cell_count.values()) == {load}
    return packets, even_pairs


def data_layout(scopes, col_ids, r=2, a=3):
    """Build all physical wires, including unary filler endpoints."""
    length = 1 << a
    def label(idx):
        high = tuple((idx//(r**j)) % r for j in range(a-1))
        return (0,) + high
    row_labels = [label(j) for j in range(len(scopes))]
    col_labels = {name: label(3*j+1) for j, name in enumerate(col_ids)}
    needed = Counter((row_labels[i], col_labels[v]) for i, row in enumerate(scopes) for v in row)
    max_cell = max(needed.values())
    load = length*((2*max_cell+length-1)//length)
    packets, pairs = template_slots(r, a, load)
    # Column None denotes its own private zero pin. Row None denotes
    # its own private all-ones dummy. Repeated None IDs are not vertices.
    columns = {(pid, x): None for pid in range(len(packets)) for x in range(length)}
    rows = {pos: None for pos in columns}
    row_ports = [[] for _ in scopes]
    for rid, scope in enumerate(scopes):
        for v in scope:
            cell = (row_labels[rid], col_labels[v])
            pid, y = pairs[cell].pop()
            assert packets[pid][y] == packets[pid][y+1] == cell
            assert rows[pid, y] is None and columns[pid, y+1] is None
            columns[pid, y] = v
            rows[pid, y+1] = rid
            row_ports[rid].append((pid, y+1))
    for scope, positions in zip(scopes, row_ports):
        assert [columns[pid, x-1] for pid, x in positions] == list(scope)
        assert all(columns[pos] is None for pos in positions)
    return columns, row_ports, len(columns), load


def mask_table(d, f):
    return {x: int(f(*x)) for x in bit_words(d)}


def eval_slot(columns, row_ports, row_tables, free_columns, pinned, t, length=8):
    c = kernel(length, t, t)
    assert c.denominator == 1
    c = int(c)
    total = 0
    for choices in bit_words(len(free_columns)):
        assignment = dict(zip(free_columns, choices))
        assignment.update(pinned)
        assignment[None] = 0
        term = 1
        for positions, table in zip(row_ports, row_tables):
            arguments = tuple(c*assignment[columns.get((p, x+t))] for p, x in positions)
            term *= signed_row_value(table, arguments)
        total += term
    return total


def independent_sets(vertex_count, edges, mask):
    return sum(not any(mask >> j & 1 and bits[u] and bits[v]
                       for j, (u, v) in enumerate(edges)) for bits in bit_words(vertex_count))


def check_packed_cubic_graphs():
    edge_lists = {
        "K4": (4, list(combinations(range(4), 2))),
        "K3_3": (6, list(product(range(3), range(3, 6)))),
        "triangular_prism": (6, [(0,1),(0,2),(1,2),(3,4),(3,5),(4,5),(0,3),(1,4),(2,5)]),
    }
    nand = mask_table(2, lambda x, y: not (x and y))
    one = mask_table(2, lambda x, y: True)
    result = {}
    for name, (n, scopes) in edge_lists.items():
        values = list(range(n))
        columns, row_ports, wire_count, load = data_layout(scopes, values)
        full = (1 << len(scopes))-1
        masks = range(full+1) if name == "K4" else [0, 1, full//3, full]
        for mask in masks:
            rows = [nand if mask >> j & 1 else one for j in range(len(scopes))]
            assert eval_slot(columns, row_ports, rows, values, {}, -1) == independent_sets(n, scopes, mask)
        assert eval_slot(columns, row_ports, [nand]*len(scopes), values, {}, 0) == 2**n
        result[name] = dict(masks=len(masks), physical_wires=wire_count, load_per_ordered_cell=load,
                            full_shifted_count=independent_sets(n, scopes, full), full_origin=2**n)
    return result


def check_fixed_host(n=3):
    edges = list(combinations(range(n), 2))
    occurrence = {(j, v): ("o", j, v) for j, e in enumerate(edges) for v in e}
    free = list(occurrence.values())
    scopes = [tuple(occurrence[j, v] for v in e) for j, e in enumerate(edges)]
    pins = {}
    equality = mask_table(4, lambda y1, y2, z1, z2: (y1*z1) == (y2*z2))
    for v in range(n):
        sequence = [occurrence[j, v] for j, e in enumerate(edges) if v in e]
        for left, right in zip(sequence, sequence[1:]):
            extra = [("p", len(scopes), h) for h in range(2)]
            pins.update({p: 1 for p in extra})
            scopes.append((left, right, *extra))
    columns, ports, wire_count, load = data_layout(scopes, free+list(pins))
    nand = mask_table(2, lambda x, y: not (x and y))
    one = mask_table(2, lambda x, y: True)
    counts = []
    for mask in range(1 << len(edges)):
        rows = [nand if mask >> j & 1 else one for j in range(len(edges))]
        rows += [equality]*(len(scopes)-len(edges))
        shifted = eval_slot(columns, ports, rows, free, pins, -1)
        origin = eval_slot(columns, ports, rows, free, pins, 0)
        assert shifted == independent_sets(n, edges, mask)
        assert origin == 2**len(free)
        counts.append(shifted)
    return dict(vertices=n, fixed_physical_wires=wire_count, load_per_ordered_cell=load,
                switched_graphs=len(counts), origin=2**len(free), shifted_counts=counts)


def edge_cover_check(edges, permute):
    """Literal read-once CNF compiler, then independent factor elimination."""
    verts = sorted(set(v for edge in edges for v in edge))
    inc = {v: [j for j, e in enumerate(edges) if v in e] for v in verts}
    hard_clauses = []
    for v in verts:
        ids = [("e", j) for j in inc[v]]
        if len(ids) % 2:
            ids.append(("a", v))
            hard_clauses.append((True, [("a", v)]))
        hard_clauses.append((False, ids))
    desired = defaultdict(list)
    for ci, (_, ids) in enumerate(hard_clauses):
        for port, logical in enumerate(ids):
            desired[logical].append((ci, port))
    assert all(len(ends) == 2 for ends in desired.values())

    # A wire is (old row, port, subdivision column). Compile each literal
    # with its own variable, hence its own all-ones leaf and subdivision.
    r, a = 2, 2
    L = 1 << a
    old = []
    wires = []
    wire_class = []
    ncols = 0
    def add_clause(positive, d, cell):
        nonlocal ncols
        rid = len(old)
        old.append(mask_table(d, lambda *y: any(y) if positive else not all(y)))
        wire_ids = []
        subdivs = []
        for port in range(d):
            col = ncols
            ncols += 1
            subdivs.append(col)
            leaf = len(old)
            old.append({(0,): 1, (1,): 1})
            wire_ids.append((len(wires), len(wires)+1))
            wires.extend(((rid, port, col), (leaf, 0, col)))
            wire_class.extend((cell, cell))
        return wire_ids, subdivs

    zero_word = (0,)*a
    diag = (zero_word, zero_word)
    hard_wires = []
    for positive, ids in hard_clauses:
        ww, _ = add_clause(positive, len(ids), diag)
        hard_wires.append([w for w, _ in ww])
    carrier = {}
    known = set()
    for key in desired:
        ww, cc = add_clause(False, 1, diag)
        carrier[key] = ww[0]
        known.add(cc[0])
    M0 = len(wires)
    load = L*((M0+L-1)//L)
    packets, pairs = template_slots(r, a, load)
    word_list = list(product(range(r), repeat=a))
    for cell in product(word_list, repeat=2):
        copies = (load-(M0 if cell == diag else 0))//2
        for _ in range(copies):
            add_clause(False, 1, cell)
    at = {}
    used = set()
    for key, ends in desired.items():
        for j, (ci, port) in enumerate(ends):
            pid, x = pairs[diag].pop()
            even, odd = carrier[key][j], hard_wires[ci][port]
            at[pid, x] = even
            at[pid, x+1] = odd
            used.update((even, odd))
    avail = defaultdict(list)
    for w, cell in enumerate(wire_class):
        if w not in used:
            avail[cell].append(w)
    if permute:
        for values in avail.values():
            values.reverse()
    for pid, cells in enumerate(packets):
        for x, cell in enumerate(cells):
            if (pid, x) not in at:
                at[pid, x] = avail[cell].pop()
    assert all(not values for values in avail.values())
    assert len(set(at.values())) == len(wires) == load*r**(2*a)

    def factors(t):
        coefficient = kernel(L, t, t)
        args = [{} for _ in old]
        for (pid, x), w in at.items():
            rid, port, _ = wires[w]
            target = at.get((pid, x+t))
            args[rid][port] = wires[target][2] if target is not None else None
        ff = []
        for rid, table in enumerate(old):
            variables = tuple(sorted(set(args[rid].values())-{None}))
            fields = {}
            for word in bit_words(len(variables)):
                assignment = dict(zip(variables, word))
                assignment[None] = 0
                aa = [coefficient*assignment[args[rid][i]] for i in range(len(args[rid]))]
                fields[word] = int(signed_row_value(table, aa))
            ff.append((variables, fields))
        return ff, args

    def elim(factors):
        for x in range(ncols):
            incident = [f for f in factors if x in f[0]]
            factors = [f for f in factors if x not in f[0]]
            scope = tuple(sorted(set().union(*(f[0] for f in incident))-{x}))
            table = {}
            for word in bit_words(len(scope)):
                bits = dict(zip(scope, word))
                val = 0
                for bitval in (0, 1):
                    bits[x] = bitval
                    val += prod(f[1][tuple(bits[v] for v in f[0])] for f in incident)
                table[word] = val
            factors.append((scope, table))
        return prod(table[()] for _, table in factors)

    fshift, args = factors(-1)
    shifted = elim(fshift)
    orig, _ = factors(0)
    origin = elim(orig)
    expected_origin = prod(2**len(ids)-1 for _, ids in hard_clauses)
    assert origin == expected_origin
    degrees = Counter()
    for table, row in zip(old, args):
        if table == {(0,): 1, (1,): 0} and row[0] is not None:
            degrees[row[0]] += 1
    normal = prod(1+2**degrees[c] for c in set(range(ncols))-known)
    assert all(degrees[c] == 0 for c in known)
    exact = sum(all(any(bits[j] for j in inc[v]) for v in verts) for bits in bit_words(len(edges)))
    assert shifted == normal*exact
    return dict(physical_wires=len(wires), planted_physical_wires=M0, physical_origin=origin,
                factor_bit_length=normal.bit_length(), shifted_bit_length=shifted.bit_length(),
                recovered_exact_edge_covers=exact)


def physical_cnf_checks():
    graphs = {
        "triangle": [(0, 1), (1, 2), (0, 2)],
        "two_by_three": list(product(range(2), range(2, 5))),
        "three_vertex_path": [(0, 1), (1, 2)],
    }
    return {name: [edge_cover_check(edges, variant) for variant in (False, True)]
            for name, edges in graphs.items()}


def witness_check():
    # Compare coefficient expansion against a row-local coefficient
    # convolution, with different real source moments and signed coefficients.
    p = 5
    modulus = 1 << p
    factors = [(1, -3, 2), (-2, 1, -1), (3, 4, -5), (-1, -2, 3)]
    row_count = len(factors)
    queries = 0
    accepted_witnesses = 0
    for bits in bit_words(row_count):
        rows = [[a if y else 1-a, b if y else -b, c if y else -c]
                for y, (a, b, c) in zip(bits, factors)]
        coefficients = {(0, 0): 1}
        for row in rows:
            nxt = Counter()
            for (e0, e1), value in coefficients.items():
                for j, coeff in enumerate(row):
                    nxt[e0+(j==1), e1+(j==2)] += value*coeff
            coefficients = nxt
        witnesses = Counter()
        for choices in product(range(3), repeat=row_count):
            alpha = (choices.count(1), choices.count(2))
            raw = prod(row[j] for row, j in zip(rows, choices)) * 3**alpha[0] * 2**alpha[1]
            w = raw % modulus
            witnesses[alpha] += sum(d < w for d in range(modulus))
        for alpha, value in coefficients.items():
            expected = value * 3**alpha[0] * 2**alpha[1]
            assert witnesses[alpha] % modulus == expected % modulus
            queries += 1
        accepted_witnesses += sum(witnesses.values())
    return dict(coefficient_checks=queries, modular_accepting_paths=accepted_witnesses)


def main():
    print(json.dumps(dict(
        cauchy_displacements=cauchy_checks(),
        exhaustively_checked_truth_table_inputs=binary_factors(),
        packed_cubic_graphs=check_packed_cubic_graphs(),
        fixed_public_host=check_fixed_host(),
        physical_read_once_CNFs=physical_cnf_checks(),
        weighted_oracle_exercise=witness_check(),
        scope="Toy packings have r=2, a=3, L=8. The written proof gives the active r=64 parameters."
    ), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
