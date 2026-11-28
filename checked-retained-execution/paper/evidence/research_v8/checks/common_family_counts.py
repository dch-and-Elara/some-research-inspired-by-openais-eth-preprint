"""Exact checks for the caterpillar terminal counts and cubic physical CNFs."""

from collections import Counter
from fractions import Fraction
import json

from stronger_family import physical_count


def caterpillar(k):
    leaves = range(k + 1, 2 * (k + 1))
    return [(j, j + 1) for j in range(k)] + list(zip(range(k + 1), leaves))


def cubic_completion(k):
    """Use a cycle with antipodal chords as a finite test core."""
    d = 2 * k + 4
    start = 2 * (k + 1)

    def core(index, half):
        return start + 2 * index + half

    edges = caterpillar(k)
    edges.extend((core(i, 0), core((i + 1) % d, 0)) for i in range(d))
    edges.extend((core(i, 1), core(i + d // 2, 1)) for i in range(d // 2))
    edges.extend((core(i, 0), core(i, 1)) for i in range(d))
    deficits = [leaf for leaf in range(k + 1, 2 * (k + 1)) for _ in range(2)]
    deficits.extend([0, k])
    edges.extend((v, core(i, 1)) for i, v in enumerate(deficits))
    order = start + 2 * d
    assert order == 6 * k + 10
    assert len({tuple(sorted(edge)) for edge in edges}) == len(edges)
    assert all(u != v for u, v in edges)
    assert Counter(v for edge in edges for v in edge) == {v: 3 for v in range(order)}
    return order, edges


def enabled(k, word, last):
    spine = (1 << k) - 1
    return spine | (int(last) << k) | ((1 + (word << 1)) << (k + 1))


def shortened_cnf(order, edges, switches):
    """Allocate the literal ports of each binary clause before adding cycles."""
    clauses = []
    graph_ports = []
    for vertex in range(order):
        ports = [5 * vertex + j + 1 for j in range(5)]
        sign = 1 if (switches >> vertex) & 1 else -1
        clauses.append((-ports[0], sign * ports[2]))
        clauses.extend((-v, ports[(i + 1) % 5]) for i, v in enumerate(ports))
        graph_ports.append([ports[1], ports[3], ports[4]])
    for u, v in edges:
        clauses.append((-graph_ports[u].pop(), -graph_ports[v].pop()))
    assert all(not ports for ports in graph_ports)
    clauses.append((5 * order + 1, 5 * order + 2))
    assert 2 * len(clauses) == 15 * order + 2
    return tuple(clauses)


def physical_check(k, word, last):
    order, edges = cubic_completion(k)
    clauses = shortened_cnf(order, edges, enabled(k, word, last))
    return physical_count(clauses, 5 * order + 2)


def count_check(k):
    order = 2 * (k + 1)
    edges = [(1 << u) | (1 << v) for u, v in caterpillar(k)]
    independent = [s for s in range(1 << order) if all(s & e != e for e in edges)]
    pairs = set()
    counts = set()
    for word in range(1 << k):
        a, b = 2, 1
        for j in range(k):
            a, b = (1 + ((word >> j) & 1)) * (a + b), a
        answers = []
        for last in (False, True):
            free = enabled(k, word, last)
            value = 3 * sum((s & ~free) == 0 for s in independent)
            assert value == 3 * (a + (b if last else 0))
            if k <= 3:
                assert physical_check(k, word, last) == value
            answers.append(value)
        pairs.add(tuple(answers))
        counts.update(answers)
    assert len(pairs) == 1 << k
    assert len(counts) ** 2 >= len(pairs)
    return {
        "k": k,
        "cubic_vertices": 6 * k + 10,
        "distinct_count_pairs": len(pairs),
        "distinct_counts_on_tested_words": len(counts),
        "physical_formula_evaluations": 2 ** (k + 1) if k <= 3 else 0,
    }


def exact_expansion(order, edges):
    best = None
    edge_masks = [(1 << u) | (1 << v) for u, v in edges]
    for side in range(1, 1 << (order - 1)):
        boundary = sum((side & edge).bit_count() == 1 for edge in edge_masks)
        size = side.bit_count()
        ratio = Fraction(boundary, min(size, order - size))
        if best is None or ratio < best:
            best = ratio
    return best


def main():
    order, edges = cubic_completion(1)
    d = 6
    core_edges = [(i, (i + 1) % d) for i in range(d)]
    core_edges.extend((i, i + d // 2) for i in range(d // 2))
    base = exact_expansion(d, core_edges)
    completed = exact_expansion(order, edges)
    bound = base / (4 * (base + 4))
    assert completed >= bound
    results = {
        "tests": [count_check(k) for k in range(1, 8)],
        "finite_expansion": {
            "core": str(base),
            "cubic_completion": str(completed),
            "proved_general_lower_bound_for_this_core": str(bound),
        },
    }
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
