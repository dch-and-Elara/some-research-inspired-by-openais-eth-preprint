"""Exact finite exercises for the physical source clauses and support arguments."""

from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, product
import json


def cycle_order(slots, forbidden):
    """Keep the two copies from any one original clause apart."""
    paired = {slot for pair in forbidden for slot in pair}
    loose = [slot for slot in slots if slot not in paired]
    if not forbidden:
        return slots
    if len(forbidden) == 1:
        a, b = forbidden[0]
        assert len(loose) >= 2
        return [a, loose[0], b, *loose[1:]]
    return [*(a for a, _ in forbidden), *loose, *(b for _, b in forbidden)]


def source_formula(n, edges, triples, availability, edge_requests, triple_requests):
    clauses = []
    slots = defaultdict(list)
    forbidden = defaultdict(list)
    next_slot = 1

    def append_clause(*literals):
        nonlocal next_slot
        pos_in_clause = defaultdict(list)
        signed = []
        for name, positive in literals:
            slots[name].append(next_slot)
            pos_in_clause[name].append(next_slot)
            signed.append(next_slot if positive else -next_slot)
            next_slot += 1
        for name, positions in pos_in_clause.items():
            if len(positions) > 1:
                assert len(positions) == 2
                forbidden[name].append(tuple(positions))
        clauses.append(tuple(signed))

    for v in range(n):
        append_clause((v, False), (v, availability >> v & 1))
    for e, (u, v) in enumerate(edges):
        append_clause((u, False), (v, False))
        append_clause((u, True), (v, True), (u, edge_requests >> e & 1))
    for d, (i, j, k) in enumerate(triples):
        y = n + d
        append_clause((i, False), (y, True))
        append_clause((j, False), (y, True))
        append_clause((i, True), (j, True), (y, False))
        append_clause((y, True), (k, True), (k, triple_requests >> d & 1))
    copied = next_slot - 1
    for name, positions in slots.items():
        order = cycle_order(positions, forbidden[name])
        for i, item in enumerate(order):
            clauses.append((-item, order[(i + 1) % len(order)]))
    clauses.append((next_slot, next_slot + 1))
    return copied + 2, tuple(clauses)


def physical_count(clauses, n):
    """Generic #DPLL including isolated free variables after simplification."""
    def assign(residual, literal):
        return tuple(
            tuple(other for other in clause if other != -literal)
            for clause in residual
            if literal not in clause
        )

    def count(residual, free):
        while residual:
            smallest = min(residual, key=len)
            if not smallest:
                return 0
            literal = smallest[0]
            if len(smallest) > 1:
                return count(assign(residual, literal), free - 1) + count(
                    assign(residual, -literal), free - 1
                )
            residual = assign(residual, literal)
            free -= 1
        return 1 << free

    return count(clauses, n)


def independent_sets(n, edges):
    return [
        subset for subset in range(1 << n)
        if all(not (subset >> u & subset >> v & 1) for u, v in edges)
    ]


def graph_count(sets, edge_masks, triple_masks, availability, edge_requests, triple_requests):
    def meets(subset, masks, requests):
        return all(
            not (requests >> i & 1) or subset & mask for i, mask in enumerate(masks)
        )

    return 3 * sum(
        not (subset & ~availability)
        and meets(subset, edge_masks, edge_requests)
        and meets(subset, triple_masks, triple_requests)
        for subset in sets
    )


def mask(items):
    return sum(1 << i for i in items)


def check_source(n, edges, triples):
    sets = independent_sets(n, edges)
    edge_masks = list(map(mask, edges))
    triple_masks = list(map(mask, triples))
    copied = 2 * n + 5 * len(edges) + 10 * len(triples)
    counts = set()
    reference = None
    tested = 0
    for availability, ed, tr in product(
        range(1 << n), range(1 << len(edges)), range(1 << len(triples))
    ):
        physical_n, formula = source_formula(n, edges, triples, availability, ed, tr)
        assert physical_n == copied + 2
        assert len(formula) == copied + n + 2 * len(edges) + 4 * len(triples) + 1
        assert sum(map(len, formula)) == 3 * copied + 2
        scopes = tuple(tuple(map(abs, clause)) for clause in formula)
        if reference is None:
            reference = scopes
        assert scopes == reference
        degree = Counter(v for scope in scopes for v in scope)
        assert list(sorted(degree.values())) == [1, 1] + [3] * copied
        assert all(len(set(scope)) == len(scope) >= 2 for scope in scopes)
        clause_sets = list(map(frozenset, formula))
        assert all(
            not (a <= b or b <= a) for a, b in combinations(clause_sets, 2)
        )
        found = physical_count(formula, physical_n)
        expect = graph_count(sets, edge_masks, triple_masks, availability, ed, tr)
        assert found == expect and (found == 0 or found >= 3)
        counts.add(found)
        tested += 1
    return {
        "logical_vertices": n, "edges": len(edges), "triples": len(triples),
        "physical_variables": copied + 2, "source_words": tested,
        "counts": sorted(counts),
    }


def parity_rank(rows):
    basis = {}
    for row in rows:
        bits = sum((value & 1) << i for i, value in enumerate(row))
        while bits:
            pivot = bits.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = bits
                break
            bits ^= basis[pivot]
    return len(basis)


def check_terminal(m):
    n = 2 * m
    edges = [(v, v + m) for v in range(m)]
    sets = independent_sets(n, edges)
    masks = list(map(mask, edges))
    matrices = [[], [], []]
    for left in range(1 << m):
        rows = [[], [], []]
        for right in range(1 << m):
            state = left | right << m
            active = graph_count(sets, masks, [], state, (1 << m) - 1, 0)
            inactive = graph_count(sets, masks, [], state, 0, 0)
            pair_counts = [(left >> i & 1) + (right >> i & 1) for i in range(m)]
            product_active = product_inactive = 3
            for value in pair_counts:
                product_active *= value
                product_inactive *= 1 + value
            assert active == product_active and inactive == product_inactive
            for row, value in zip(rows, [active, bool(active), inactive]):
                row.append(value)
        for matrix, row in zip(matrices, rows):
            matrix.append(row)
    ranks = [parity_rank(matrix) for matrix in matrices]
    assert ranks == [1 << m] * 3
    return ranks


def check_support(n, edges):
    all_vertices = (1 << n) - 1
    sets = independent_sets(n, edges)
    h = min(
        Fraction(sum(bool(cut >> u & 1) != bool(cut >> v & 1) for u, v in edges),
                 min(cut.bit_count(), n - cut.bit_count()))
        for cut in range(1, all_vertices)
    )
    degree = Counter(v for edge in edges for v in edge)
    d = max(degree.values())
    assert min(degree.values()) >= 1
    delta = Fraction(1, 1 + 2 ** d)
    no_cross = overlap = exclusions = restrictions = 0
    for s, t in product(range(1 << n), repeat=2):
        if any(
            (s >> u & t >> v & 1) or (s >> v & t >> u & 1)
            for u, v in edges
        ):
            continue
        no_cross += 1
        overlap += bool(s & t)
        assert (all_vertices ^ (s | t)).bit_count() >= (
            h * min(s.bit_count(), t.bit_count()) / d ** 2
        )
    for statuses in product((-1, 0, 1), repeat=n):
        free = [i for i, status in enumerate(statuses) if status == -1]
        fixed_ones = mask(i for i, val in enumerate(statuses) if val == 1)
        subsets = [mask(free[i] for i in range(len(free)) if a >> i & 1)
                   for a in range(1 << len(free))]
        values = [3 * sum(not (a & ~(fixed_ones | u)) for a in sets) for u in subsets]
        for i in range(len(free)):
            for a in range(len(subsets)):
                if a >> i & 1:
                    values[a] -= values[a ^ (1 << i)]
        assert all(val >= 0 and (val > 0) == (a in sets) for a, val in zip(subsets, values))
        restrictions += 1
    for deleted in range(1 << n):
        free_sets = [a for a in sets if not a & deleted]
        for omitted in range(1 << n):
            if omitted & deleted:
                continue
            avoid = sum(not (a & omitted) for a in free_sets)
            assert Fraction(avoid, len(free_sets)) <= (1 - delta) ** omitted.bit_count()
            exclusions += 1
    return {
        "vertices": n, "expansion": str(h), "max_degree": d,
        "no_cross_pairs": no_cross, "overlapping_no_cross_pairs": overlap,
        "subcube_supports": restrictions, "conditional_avoidance_checks": exclusions,
    }


def main():
    fixtures = [
        (2, [(0, 1)], []),
        (3, [(0, 1), (1, 2), (2, 0)], [(0, 1, 2)]),
        (4, [(0, 1), (1, 2), (2, 3)], [(0, 1, 2)]),
        (4, [(0, 2), (1, 3)], []),
    ]
    source = [check_source(*fixture) for fixture in fixtures]
    support_edges = [(i, (i + 1) % 6) for i in range(6)] + [(0, 3), (1, 4), (2, 5)]
    report = {
        "source": source,
        "source_words_total": sum(entry["source_words"] for entry in source),
        "terminal_ranks_count_decision_inactive": [check_terminal(m) for m in range(1, 4)],
        "support": check_support(6, support_edges),
    }
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
