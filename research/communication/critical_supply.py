#!/usr/bin/env python3
"""Exact finite checks for critical-transition supply certificates.

Run from the repository root with python3 research/communication/critical_supply.py.
Cardinalities and certificate validity are checked with integers/rationals. SciPy
only proposes fractional packings; its floating-point optimum is not a proof.
The sampled circuits/layouts are not claimed to be minimal or asymptotically hard.
"""

from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, product
from math import acos, log2, pi, sqrt
from pathlib import Path
from random import Random
import json
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))
from check_algorithms import Gate, Network


def project(row, scope):
    return tuple(row[i] for i in scope)


def packing_certificate(d, constraints):
    """Return rational feasible weights, repairing any numerical LP error."""
    if not constraints:
        return []
    import numpy as np
    from scipy.optimize import linprog

    incidence = np.zeros((d, len(constraints)))
    deficits = []
    for j, (scope, allowed) in enumerate(constraints):
        incidence[list(scope), j] = 1
        deficits.append(len(scope) - log2(len(allowed)))
    result = linprog(-np.array(deficits), A_ub=incidence,
                     b_ub=np.ones(d), bounds=(0, None), method="highs")
    assert result.success, result.message
    weights = [max(Fraction(0), Fraction(float(w)).limit_denominator(1024))
               for w in result.x]
    loads = [sum(w for w, (scope, _) in zip(weights, constraints) if i in scope)
             for i in range(d)]
    scale = max([Fraction(1)] + loads)
    return [w / scale for w in weights]


def check_certificate(rows, d, constraints, weights):
    """Check all hypotheses and the integer-power cardinality inequality."""
    from math import lcm

    assert len(constraints) == len(weights)
    assert rows and all(len(row) == d for row in rows)
    assert all(w >= 0 for w in weights)
    for scope, allowed in constraints:
        assert scope and len(set(scope)) == len(scope)
        assert all(0 <= i < d for i in scope)
        assert {project(row, scope) for row in rows} <= allowed
        assert 0 < len(allowed) <= 2 ** len(scope)
    assert all(sum(w for w, (scope, _) in zip(weights, constraints) if i in scope) <= 1
               for i in range(d))
    denominator = lcm(*(w.denominator for w in weights)) if weights else 1
    numerators = [int(denominator * w) for w in weights]
    free_exponent = denominator * d - sum(
        z * len(scope) for z, (scope, _) in zip(numerators, constraints))
    assert free_exponent >= 0
    upper = 2 ** free_exponent
    for z, (_, allowed) in zip(numerators, constraints):
        upper *= len(allowed) ** z
    assert len(rows) ** denominator <= upper
    return d - sum(float(w) * (len(scope) - log2(len(allowed)))
                   for w, (scope, allowed) in zip(weights, constraints))


def projected_gate_constraints(n, gates, out, signals):
    """Relations valid for every accepting trace, with hidden ports eliminated.

    Each gate is inspected independently; hidden signals of different gates
    are not required to agree. This relaxation is deliberately tested below.
    """
    index = {wire: i for i, wire in enumerate(signals)}
    found = {}
    for j, gate in enumerate(gates):
        output = n + j
        ports = sorted(set(gate.args) | {output})
        visible = [wire for wire in ports if wire in index]
        if not visible:
            continue
        arguments = sorted(set(gate.args))
        allowed = set()
        for bits in product((0, 1), repeat=len(arguments)):
            values = dict(zip(arguments, bits))
            values[output] = gate.apply([values[a] for a in gate.args])
            allowed.add(tuple(values[wire] for wire in visible))
        scope = tuple(index[wire] for wire in visible)
        if len(allowed) < 2 ** len(scope):
            found[scope, frozenset(allowed)] = (scope, allowed)
    if out in index:
        scope = (index[out],)
        found[scope, frozenset({(1,)})] = (scope, {(1,)})
    return list(found.values())


def connected_gate_blocks(n, gates, max_size):
    adjacency = {j: set() for j in range(len(gates))}
    for j, gate in enumerate(gates):
        for wire in gate.args:
            if wire >= n:
                adjacency[j].add(wire - n)
                adjacency[wire - n].add(j)
    for size in range(1, min(max_size, len(gates)) + 1):
        for block in combinations(range(len(gates)), size):
            seen, todo = set(), [block[0]]
            while todo:
                j = todo.pop()
                if j not in seen:
                    seen.add(j)
                    todo.extend((adjacency[j] & set(block)) - seen)
            if seen == set(block):
                yield block


def projected_block_constraints(n, gates, out, signals, max_size):
    """Compose gates inside a block before eliminating its hidden ports."""
    index = {wire: i for i, wire in enumerate(signals)}
    found = {}
    for block in connected_gate_blocks(n, gates, max_size):
        outputs = {n + j for j in block}
        external = sorted({a for j in block for a in gates[j].args} - outputs)
        visible = sorted((outputs | set(external)) & set(signals))
        if not visible:
            continue
        allowed = set()
        for bits in product((0, 1), repeat=len(external)):
            values = dict(zip(external, bits))
            for j in block:
                values[n + j] = gates[j].apply([values[a] for a in gates[j].args])
            allowed.add(tuple(values[wire] for wire in visible))
        scope = tuple(index[wire] for wire in visible)
        if len(allowed) < 2 ** len(scope):
            found[scope, frozenset(allowed)] = (scope, allowed)
    if out in index:
        scope = (index[out],)
        found[scope, frozenset({(1,)})] = (scope, {(1,)})
    return list(found.values())


def affine_forms(n, gates):
    """Treat nonlinear outputs as formal free bits; preserve affine equations."""
    forms = [(1 << i, 0) for i in range(n)]
    next_atom = n
    for gate in gates:
        assert isinstance(gate.op, int) and len(gate.args) == 2
        table = [gate.apply(bits) for bits in ((0, 0), (1, 0), (0, 1), (1, 1))]
        if table[0] ^ table[1] ^ table[2] ^ table[3]:
            forms.append((1 << next_atom, 0))
            next_atom += 1
        else:
            mask, offset = 0, table[0]
            for coefficient, argument in zip((table[1] ^ table[0], table[2] ^ table[0]), gate.args):
                if coefficient:
                    other_mask, other_offset = forms[argument]
                    mask ^= other_mask
                    offset ^= other_offset
            forms.append((mask, offset))
    return forms


def binary_rank(rows):
    pivots = {}
    for row in rows:
        while row:
            bit = row.bit_length() - 1
            if bit not in pivots:
                pivots[bit] = row
                break
            row ^= pivots[bit]
    return len(pivots)


def affine_bound_bits(forms, signals, out=None):
    rows = [forms[wire][0] for wire in signals]
    if out is not None and forms[out][0]:
        return binary_rank(rows + [forms[out][0]]) - 1
    return binary_rank(rows)


def affine_code(forms, signals, out):
    """Coordinates for the visible affine image, conditional on output=1.

    A signal outside the physical boundary is also reconstructed when its
    affine form belongs to this span. This preserves long affine dependencies.
    """
    pivots, basis = {}, []

    def reduce(mask):
        coefficient = 0
        while mask:
            bit = mask.bit_length() - 1
            if bit not in pivots:
                break
            row, code = pivots[bit]
            mask ^= row
            coefficient ^= code
        return mask, coefficient

    def add(mask):
        remainder, coefficient = reduce(mask)
        if remainder:
            coefficient ^= 1 << len(basis)
            basis.append(mask)
            pivots[remainder.bit_length() - 1] = remainder, coefficient

    known_output = bool(forms[out][0])
    if known_output:
        add(forms[out][0])
    for wire in signals:
        add(forms[wire][0])
    expressions = {}
    for wire, (mask, offset) in enumerate(forms):
        remainder, coefficient = reduce(mask)
        if remainder:
            continue
        if known_output:
            offset ^= (coefficient & 1) & (1 ^ forms[out][1])
            coefficient >>= 1
        expressions[wire] = coefficient, offset
    return basis[1:] if known_output else basis, expressions


def quotient_gate_constraints(n, gates, expressions, dimension):
    """Impose gate relations after affine elimination, in shared code coordinates."""
    found = {}
    for j, gate in enumerate(gates):
        output = n + j
        ports = sorted(set(gate.args) | {output})
        available = [wire for wire in ports if wire in expressions]
        if not available:
            continue
        arguments = sorted(set(gate.args))
        port_allowed = set()
        for bits in product((0, 1), repeat=len(arguments)):
            values = dict(zip(arguments, bits))
            values[output] = gate.apply([values[a] for a in gate.args])
            port_allowed.add(tuple(values[wire] for wire in available))
        used_mask = 0
        for wire in available:
            used_mask |= expressions[wire][0]
        scope = tuple(i for i in range(dimension) if used_mask >> i & 1)
        allowed = set()
        for bits in product((0, 1), repeat=len(scope)):
            code = sum(bit << i for bit, i in zip(bits, scope))
            observed = tuple((code & expressions[wire][0]).bit_count() % 2
                             ^ expressions[wire][1] for wire in available)
            if observed in port_allowed:
                allowed.add(bits)
        assert allowed, "The affine relaxation and gate constraints reject every code."
        if len(allowed) < 2 ** len(scope):
            found[scope, frozenset(allowed)] = scope, allowed
    return list(found.values())


def trace_atoms(n, gates, values):
    bits = list(values[:n])
    for j, gate in enumerate(gates):
        if sum(gate.apply(p) for p in product((0, 1), repeat=2)) % 2:
            bits.append(values[n + j])
    return sum(bit << i for i, bit in enumerate(bits))


def quotient_certificate(n, gates, out, signals, rows, forms):
    basis, expressions = affine_code(forms, signals, out)
    assert len(basis) == affine_bound_bits(forms, signals, out)
    code_rows = set()
    for values in rows:
        atoms = trace_atoms(n, gates, values)
        assert all((atoms & mask).bit_count() % 2 ^ offset == values[wire]
                   for wire, (mask, offset) in enumerate(forms))
        code = tuple((atoms & mask).bit_count() % 2 for mask in basis)
        packed = sum(bit << i for i, bit in enumerate(code))
        assert all((packed & expressions[wire][0]).bit_count() % 2
                   ^ expressions[wire][1] == values[wire] for wire in signals)
        code_rows.add(code)
    assert len(code_rows) == len({project(values, signals) for values in rows})
    constraints = quotient_gate_constraints(n, gates, expressions, len(basis))
    return check_certificate(code_rows, len(basis), constraints,
                             packing_certificate(len(basis), constraints))


def check_small_relations():
    """Every nonempty relation on three bits and several fractional packings."""
    cube = list(product((0, 1), repeat=3))
    scopes = [(0, 1), (0, 2), (1, 2)]
    packings = [tuple(Fraction(x, 2) for x in p)
                for p in product(range(3), repeat=3)
                if all(sum(p[j] for j, scope in enumerate(scopes) if i in scope) <= 2
                       for i in range(3))]
    checked = 0
    for mask in range(1, 2 ** len(cube)):
        rows = {row for j, row in enumerate(cube) if (mask >> j) & 1}
        constraints = [(scope, {project(row, scope) for row in rows}) for scope in scopes]
        for weights in packings:
            check_certificate(rows, 3, constraints, weights)
            checked += 1
    return checked


def check_structural_examples():
    k = 6
    pair = {(0, 0), (1, 0), (1, 1)}
    rows = {tuple(bit for p in choices for bit in p)
            for choices in product(pair, repeat=k)}
    constraints = [((2 * i, 2 * i + 1), pair) for i in range(k)]
    exponent = check_certificate(rows, 2 * k, constraints, [Fraction(1)] * k)
    assert len(rows) == 3 ** k

    # Shared-selector implications cannot each be charged at full weight.
    selector_rows = {(0,) + (0,) * k} | {(1,) + x for x in product((0, 1), repeat=k)}
    selector_constraints = [((0, i + 1), pair) for i in range(k)]
    weights = packing_certificate(k + 1, selector_constraints)
    selector_exponent = check_certificate(selector_rows, k + 1, selector_constraints, weights)
    assert sum(weights) <= 1
    naive_upper = 2 ** (k + 1) * Fraction(3, 4) ** k
    assert len(selector_rows) > naive_upper

    # A minimal two-gate parity-of-three module. Its hidden intermediate
    # removes every nontrivial single-gate relation on the four visible ports.
    gates = [Gate(6, (0, 1)), Gate(6, (3, 2))]
    visible = (0, 1, 2, 4)
    parity_rows = {x + (x[0] ^ x[1] ^ x[2],) for x in product((0, 1), repeat=3)}
    # No output constraint: the module feeds an arbitrary continuation.
    local = projected_gate_constraints(3, gates, -1, visible)
    assert local == []
    assert len(parity_rows) == 8
    for size in range(1, 4):
        for scope in combinations(range(4), size):
            assert len({project(row, scope) for row in parity_rows}) == 2 ** size
    block_constraint = [(tuple(range(4)), parity_rows)]
    assert check_certificate(parity_rows, 4, block_constraint, [Fraction(1)]) == 3
    assert projected_block_constraints(3, gates, -1, visible, 2) == block_constraint
    bounded_block_failures = []
    for budget in range(1, 7):
        n = budget + 2
        chain = [Gate(6, (0, 1))]
        for i in range(2, n):
            chain.append(Gate(6, (n + len(chain) - 1, i)))
        out = n + len(chain) - 1
        signals = tuple(range(n)) + (out,)
        assert len(chain) == n - 1 == budget + 1
        assert projected_block_constraints(n, chain, -1, signals, budget) == []
        global_constraints = projected_block_constraints(n, chain, -1, signals, budget + 1)
        assert len(global_constraints) == 1
        assert len(global_constraints[0][1]) == 2 ** n
        assert affine_bound_bits(affine_forms(n, chain), signals) == n
        bounded_block_failures.append({"block_budget": budget, "module_gates": len(chain),
                                       "raw_and_local_bits": n + 1, "affine_bound_bits": n})
    return {
        "disjoint_implications": {"pairs": k, "patterns": len(rows), "bound_bits": exponent},
        "shared_selector": {"patterns": len(selector_rows),
                            "invalid_unweighted_bound": str(naive_upper),
                            "certified_bound_bits": selector_exponent,
                            "packing_weight": str(sum(weights))},
        "hidden_xor_module": {"visible_bits": 4, "patterns": len(parity_rows),
                              "single_gate_bound_bits": 4, "two_gate_bound_bits": 3,
                              "all_proper_projections_full": True},
        "bounded_block_obstructions": bounded_block_failures,
    }


def analyze_trace(n, gates, out, net, order, cache):
    full_rows = []
    for x in product((0, 1), repeat=n):
        values = list(x)
        for gate in gates:
            values.append(gate.evaluate(values))
        if values[out]:
            full_rows.append((x, values))
    if len(full_rows) < 2:
        return None
    cuts, revealed, seen = [set()], [set()], set()
    for vertex in order:
        seen.add(vertex)
        cuts.append({net.edges[e][2] for e, (a, b, _) in enumerate(net.edges)
                     if (a in seen) != (b in seen)})
        now = set(revealed[-1])
        if vertex[0] == "wire" and vertex[1] < n:
            now.add(vertex[1])
        revealed.append(now)
    # Frontier.Network.sweep has a final step revealing unused coordinates.
    cuts.append(set())
    revealed.append(set(range(n)))
    messages = [[project(values, sorted(cut)) for _, values in full_rows] for cut in cuts]
    pasts, futures = [], []
    for t, msg in enumerate(messages):
        before, after = defaultdict(set), defaultdict(set)
        for q, (x, _) in zip(msg, full_rows):
            before[q].add(project(x, sorted(revealed[t])))
            after[q].add(project(x, sorted(set(range(n)) - revealed[t])))
        pasts.append(before)
        futures.append(after)
    for i in range(len(full_rows)):
        sizes = [len(pasts[t][messages[t][i]]) for t in range(len(cuts))]
        assert all(a <= b for a, b in zip(sizes, sizes[1:]))
        assert sizes[0] == 1 and sizes[-1] == len(full_rows)
    threshold = min(3, len(full_rows))
    charge_times = [next(t for t in range(1, len(cuts))
                         if len(pasts[t][messages[t][i]]) >= threshold)
                    for i in range(len(full_rows))]
    critical_load = 0
    critical_count = 0
    checks = 0
    peak_local_gain = 0.0
    peak_combined_gain = 0.0
    peak_quotient_gain = 0.0
    strict_block_improvements = 0
    strict_quotient_improvements = 0
    forms = affine_forms(n, gates)
    for t in range(len(cuts) - 1):
        newly = sorted(revealed[t + 1] - revealed[t])
        transitions = defaultdict(list)
        for i, (x, _) in enumerate(full_rows):
            transitions[messages[t][i], messages[t + 1][i], project(x, newly)].append(i)
        for (q, r, _), indices in transitions.items():
            capacity = len(pasts[t][q]) * len(futures[t + 1][r])
            assert len(indices) == capacity
            critical = len(pasts[t][q]) < threshold <= len(pasts[t + 1][r])
            assert all((charge_times[i] == t + 1) == critical for i in indices)
            if critical:
                critical_load += capacity
                critical_count += 1
        signals = tuple(sorted(cuts[t] | cuts[t + 1] | set(newly)))
        if signals not in cache:
            constraints = projected_gate_constraints(n, gates, out, signals)
            weights = packing_certificate(len(signals), constraints)
            rows = {project(values, signals) for _, values in full_rows}
            bound = check_certificate(rows, len(signals), constraints, weights)
            blocks = projected_block_constraints(n, gates, out, signals, 2)
            block_bound = check_certificate(rows, len(signals), blocks,
                                            packing_certificate(len(signals), blocks))
            rank_bound = affine_bound_bits(forms, signals, out)
            assert len(rows) <= 2 ** rank_bound
            quotient_bound = min(quotient_certificate(n, gates, out, candidate,
                                                      [values for _, values in full_rows], forms)
                                 for candidate in (signals, tuple(reversed(signals))))
            # Different upper bounds are combined by minimum, never by adding
            # their savings, which could charge the same relation twice.
            cache[signals] = bound, block_bound, rank_bound, quotient_bound
        bound, block_bound, rank_bound, quotient_bound = cache[signals]
        peak_local_gain = max(peak_local_gain, len(signals) - bound)
        peak_combined_gain = max(peak_combined_gain, len(signals) - min(bound, block_bound, rank_bound))
        peak_quotient_gain = max(peak_quotient_gain, len(signals) - quotient_bound)
        strict_block_improvements += block_bound < bound - 1e-8
        strict_quotient_improvements += quotient_bound < min(bound, block_bound, rank_bound) - 1e-8
        checks += len(transitions)
    assert critical_load == len(full_rows)
    return {"transition_checks": checks, "critical_transitions": critical_count,
            "accepting_inputs": len(full_rows), "max_local_gain_bits": peak_local_gain,
            "max_combined_gain_bits": peak_combined_gain,
            "max_quotient_gain_bits": peak_quotient_gain,
            "steps_with_strict_block_improvement": strict_block_improvements,
            "steps_with_strict_quotient_improvement": strict_quotient_improvements}


def check_compiled_traces():
    rng = Random(20261010)
    answers = []
    # These are correctness tests, not evidence for a universal coefficient.
    for _ in range(12):
        n = 4
        gates = [Gate(rng.choice((6, 8, 14, 1, 7, 9)), tuple(rng.sample(range(n + i), 2)))
                 for i in range(7)]
        out = n + len(gates) - 1
        net = Network(n, gates, [(out, True)])
        cache = {}
        for _ in range(5):
            order = list(net.vertices)
            rng.shuffle(order)
            result = analyze_trace(n, gates, out, net, order, cache)
            if result is not None:
                answers.append(result)
    return {"layouts_checked": len(answers),
            "transition_product_equalities": sum(a["transition_checks"] for a in answers),
            "critical_cut_equalities": len(answers),
            "largest_local_saving_bits": max(a["max_local_gain_bits"] for a in answers),
            "largest_combined_saving_bits": max(a["max_combined_gain_bits"] for a in answers),
            "largest_quotient_saving_bits": max(a["max_quotient_gain_bits"] for a in answers),
            "steps_with_strict_block_improvement": sum(a["steps_with_strict_block_improvement"]
                                                       for a in answers),
            "steps_with_strict_quotient_improvement": sum(a["steps_with_strict_quotient_improvement"]
                                                          for a in answers),
            "scope": "sampled layouts; exhaustive inputs; circuits not minimized; no coefficient evidence"}


def terminal_core(net):
    """An executable terminal compression; no choice of an optimal layout."""
    blocks = [{v} for v in net.vertices]
    while True:
        owner = {v: i for i, block in enumerate(blocks) for v in block}
        arcs = [(owner[a], owner[b], wire) for a, b, wire in net.edges if owner[a] != owner[b]]
        degrees = Counter(i for a, b, _ in arcs for i in (a, b))
        multiplicity = Counter(tuple(sorted((a, b))) for a, b, _ in arcs)
        merge = next(((a, b) for (a, b), count in sorted(multiplicity.items())
                      if degrees[a] + degrees[b] - 2 * count <= 3), None)
        if merge is None:
            return blocks, arcs
        a, b = merge
        blocks[a] |= blocks[b]
        del blocks[b]


def unary_cut_rank(arcs, marked, values, cut):
    crossing = [(a, b, wire) for a, b, wire in arcs if (a in cut) != (b in cut)]
    rows = {tuple(row[wire] for _, _, wire in crossing) for row in values}
    equations = []
    proposed_forest_deficit = 0
    all_stars_nonconstant = True
    for vertex in marked:
        scope = [i for i, (a, b, _) in enumerate(crossing) if vertex in (a, b)]
        patterns = sorted({project(row, scope) for row in rows})
        assert len(patterns) <= 2
        if not scope:
            continue
        proposed_forest_deficit += len(scope) - 1
        if len(patterns) == 1:
            all_stars_nonconstant = False
            equations.extend(1 << i for i in scope)
            continue
        varying = [j for j in range(len(scope)) if patterns[0][j] != patterns[1][j]]
        assert varying
        pivot = scope[varying[0]]
        for j, coordinate in enumerate(scope):
            if j not in varying:
                equations.append(1 << coordinate)
                all_stars_nonconstant = False
            elif coordinate != pivot:
                equations.append((1 << pivot) ^ (1 << coordinate))
    deficit = binary_rank(equations)
    assert len(rows) <= 2 ** (len(crossing) - deficit)
    if all_stars_nonconstant:
        assert deficit == proposed_forest_deficit
    return len(crossing), deficit, all_stars_nonconstant


def check_typed_cores():
    rng = Random(10102026)
    cores, cuts, forest_equalities = 0, 0, 0
    largest_deficit, largest_core = 0, 0
    for _ in range(36):
        n = 6
        gates = [Gate(6, (0, 1))]
        for j in range(1, 24):
            previous = n + j - 1
            other = j % n if j < n else rng.randrange(previous)
            gates.append(Gate(rng.choice((6, 8, 14, 1, 7, 9)), (previous, other)))
        out = n + len(gates) - 1
        net = Network(n, gates, [(out, True)])
        blocks, arcs = terminal_core(net)
        h = len(blocks)
        if h <= 1:
            continue
        cores += 1
        largest_core = max(largest_core, h)
        r = n - net.unread
        s = sum(v[0] == "wire" and v[1] >= n for v in net.vertices)
        assert len(net.edges) - len(net.vertices) == s - r
        assert h <= 2 * (s - r)
        degrees = Counter(i for a, b, _ in arcs for i in (a, b))
        assert all(degrees[v] == 3 for v in range(h))
        assert len({tuple(sorted((a, b))) for a, b, _ in arcs}) == len(arcs)
        incoming = Counter(b for _, b, _ in arcs)
        reads = [sum(v[0] == "wire" and v[1] < n for v in block) for block in blocks]
        generators = [incoming[v] + reads[v] for v in range(h)]
        assert all(g >= 1 for g in generators)
        assert sum(generators) == len(arcs) + r
        marked = {v for v in range(h) if generators[v] == 1}
        assert 2 * len(marked) >= h - 2 * r
        # Independent forest check: adding an edge must always join components.
        parent = {v: v for v in marked}

        def root(v):
            while parent[v] != v:
                v = parent[v]
            return v

        for a, b, _ in arcs:
            if a in marked and b in marked:
                ra, rb = root(a), root(b)
                assert ra != rb
                parent[ra] = rb
        values = []
        for x in product((0, 1), repeat=n):
            row = list(x)
            for gate in gates:
                row.append(gate.evaluate(row))
            values.append(row)
        # Check the two-pattern block bound on the whole port set first.
        for v in marked:
            ports = [wire for a, b, wire in arcs if v in (a, b)]
            assert len({project(row, ports) for row in values}) <= 2
        for _ in range(24):
            cut = {v for v in range(h) if rng.randrange(2)}
            _, deficit, forest_exact = unary_cut_rank(arcs, marked, values, cut)
            cuts += 1
            forest_equalities += forest_exact
            largest_deficit = max(largest_deficit, deficit)
    assert cores > 0 and cuts > 0
    return {"cores_checked": cores, "cuts_checked": cuts,
            "nonconstant_forest_rank_equalities": forest_equalities,
            "largest_core_vertices": largest_core,
            "largest_unary_constraint_rank": largest_deficit,
            "scope": "exact truth tables and sampled cuts; no layout or Gaussian gain theorem"}


def check_reflection_obstruction():
    """Exact obstruction to a Gaussian gain lemma from star data alone.

    If central unit vectors have pairwise inner product r, reflect the other
    two vectors across each incident vector: f_ij=2r*e_i-e_j. All four stars
    still have correlation r, but at zero every median vertex has at most one
    opposite neighbor. This need not be a distance-kernel law on a finite graph.
    """
    checked = 0
    for r in (Fraction(3, 4), Fraction(19, 20), Fraction(99, 100)):
        a = 2 * r
        # Exact covariance identities for equicorrelated central coordinates.
        assert a * a + 1 - 2 * a * r == 1
        assert a - r == r
        assert a * a - 2 * a * r + r == r
        for scores in product((-5, -3, -1, 1, 3, 5), repeat=3):
            neighbors = [(scores[i],) + tuple(a * scores[i] - scores[j]
                                               for j in range(3) if j != i)
                         for i in range(3)]
            if any(value == 0 for triple in neighbors for value in triple):
                continue
            center = sorted(scores)[1] < 0
            colors = [sorted(triple)[1] < 0 for triple in neighbors]
            assert sum(color != center for color in colors) <= 1
            # Sum of the four other scores at edge i is 4r times its score.
            for i in range(3):
                assert sum(scores[j] for j in range(3) if j != i) + sum(neighbors[i][1:]) == 4 * r * scores[i]
            checked += 1
    return {"exact_score_checks": checked, "maximum_possible_cut_degree": 1,
            "unary_saving_at_zero": 0,
            "scope": "counterexample to star-correlation/wave-identity relaxation; not a finite circuit counterexample"}


def main():
    coefficient = 3 / pi * acos((1 + 2 * sqrt(2)) / 4)
    gap = coefficient - 0.25
    print(json.dumps({
        "fractional_projection_checks": check_small_relations(),
        "examples": check_structural_examples(),
        "compiled_traces": check_compiled_traces(),
        "typed_cores": check_typed_cores(),
        "reflection_obstruction": check_reflection_obstruction(),
        "quarter_target": {"baseline": coefficient, "needed_saving_per_surplus_gate": gap,
                           "needed_implication_weight_per_surplus_gate": gap / log2(4 / 3)},
        "status": "finite verification of paper deductions; universal structural supply theorem open",
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
