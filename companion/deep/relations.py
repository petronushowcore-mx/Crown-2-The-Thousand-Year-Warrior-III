"""Exact finite relations and explicit dependency contracts. Standard library only."""
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations, product


@dataclass(frozen=True)
class Relation:
    name: str
    scope: tuple
    rows: tuple


def validate(domains, relations):
    if not domains or any(not isinstance(k, str) or not k for k in domains):
        raise ValueError('nonempty named carrier required')
    for values in domains.values():
        if not values or len(set(values)) != len(values) or any(type(x) is not int for x in values):
            raise ValueError('distinct integer values required')
    names = set()
    for relation in relations:
        if not relation.name or relation.name in names:
            raise ValueError('duplicate or empty relation name')
        names.add(relation.name)
        if len(set(relation.scope)) != len(relation.scope) or not set(relation.scope) <= set(domains):
            raise ValueError('invalid relation scope')
        if len(set(relation.rows)) != len(relation.rows):
            raise ValueError('duplicate relation row')
        for row in relation.rows:
            if len(row) != len(relation.scope) or any(type(x) is not int or x not in domains[k] for k, x in zip(relation.scope, row)):
                raise ValueError('ill-typed relation row')


def solve(domains, relations):
    """Natural join, with unmentioned variables expanded at the end."""
    validate(domains, relations)
    partials = [dict()]
    for relation in sorted(relations, key=lambda r: (len(r.rows), r.name)):
        following = []
        for partial in partials:
            for row in sorted(relation.rows):
                incoming = dict(zip(relation.scope, row))
                if all(k not in partial or partial[k] == value for k, value in incoming.items()):
                    following.append(dict(partial, **incoming))
        partials = following
    names = tuple(sorted(domains))
    answers = set()
    for partial in partials:
        missing = tuple(k for k in names if k not in partial)
        for values in product(*(sorted(domains[k]) for k in missing)):
            total = dict(partial, **dict(zip(missing, values)))
            answers.add(tuple(total[k] for k in names))
    return tuple(sorted(answers))


def enumerate_solutions(domains, relations):
    """Independent oracle: enumerate complete assignments; no partial join."""
    validate(domains, relations)
    names = tuple(sorted(domains))
    positions = {k: i for i, k in enumerate(names)}
    allowed = [(tuple(positions[k] for k in r.scope), set(r.rows)) for r in relations]
    answers = []
    for values in product(*(sorted(domains[k]) for k in names)):
        if all(tuple(values[i] for i in indices) in rows for indices, rows in allowed):
            answers.append(values)
    return tuple(answers)


def project(rows, indices):
    return tuple(sorted({tuple(row[i] for i in indices) for row in rows}))


def minimal_conflicts(domains, relations):
    """Inclusion-minimal inconsistent subsets; no minimum-cardinality claim."""
    conflicts = []
    for size in range(1, len(relations) + 1):
        for indices in combinations(range(len(relations)), size):
            chosen = frozenset(indices)
            if any(previous <= chosen for previous in conflicts):
                continue
            if not solve(domains, tuple(relations[i] for i in indices)):
                conflicts.append(chosen)
    return tuple(tuple(sorted(c)) for c in conflicts)


def decoder(observation, verdict):
    if len(observation) != len(verdict):
        raise ValueError('different carriers')
    values = {}
    for o, q in zip(observation, verdict):
        if o in values and values[o] != q:
            return None
        values[o] = q
    return values


def decoder_by_enumeration(observation, verdict):
    """Enumerate functions on observed values; do not inspect fibre pairs."""
    if len(observation) != len(verdict):
        raise ValueError('different carriers')
    observations = sorted(set(observation))
    values = sorted(set(verdict))
    for outputs in product(values, repeat=len(observations)):
        f = dict(zip(observations, outputs))
        if tuple(f[x] for x in observation) == tuple(verdict):
            return f
    return None


def refines(finer, coarser):
    if len(finer) != len(coarser):
        raise ValueError('different carriers')
    return all(finer[i] != finer[j] or coarser[i] == coarser[j]
               for i in range(len(finer)) for j in range(len(finer)))


def strict_refines(finer, coarser):
    return refines(finer, coarser) and not refines(coarser, finer)


def partitions(size):
    """Canonical restricted-growth strings: each set partition exactly once."""
    if size < 0:
        raise ValueError('negative carrier size')
    if size == 0:
        yield ()
        return
    def extend(prefix):
        if len(prefix) == size:
            yield prefix
        else:
            for value in range(max(prefix) + 2):
                yield from extend(prefix + (value,))
    yield from extend((0,))


def dot(a, b):
    if len(a) != len(b):
        raise ValueError('vector dimensions differ')
    return sum((Fraction(x) * Fraction(y) for x, y in zip(a, b)), Fraction(0))


def rank(matrix, width=None):
    """Exact rational Gaussian elimination."""
    width = len(matrix[0]) if matrix and width is None else (width or 0)
    if any(len(row) != width for row in matrix):
        raise ValueError('ragged matrix')
    rows = [[Fraction(x) for x in row] for row in matrix]
    pivot = 0
    for column in range(width):
        candidate = next((i for i in range(pivot, len(rows)) if rows[i][column]), None)
        if candidate is None:
            continue
        rows[pivot], rows[candidate] = rows[candidate], rows[pivot]
        divisor = rows[pivot][column]
        rows[pivot] = [x / divisor for x in rows[pivot]]
        for i in range(len(rows)):
            if i != pivot:
                scale = rows[i][column]
                rows[i] = [x - scale * y for x, y in zip(rows[i], rows[pivot])]
        pivot += 1
        if pivot == len(rows):
            break
    return pivot


def kernel_basis(row):
    """Basis of one rational functional's kernel, including the zero map."""
    n = len(row)
    pivot = next((i for i, value in enumerate(row) if value), None)
    basis = []
    for i in range(n):
        if i == pivot:
            continue
        vector = [Fraction(0)] * n
        vector[i] = Fraction(1)
        if pivot is not None:
            vector[pivot] = -Fraction(row[i]) / Fraction(row[pivot])
        basis.append(tuple(vector))
    return tuple(basis)


def kernel_preserved(a, r):
    if len(a) != len(r):
        raise ValueError('functional dimensions differ')
    return all(dot(a, v) == 0 for v in kernel_basis(r))


def step(mode, state, signal):
    if mode not in (0, 1) or state not in (0, 1, 2) or signal not in ('silence', 'request', 'block'):
        raise ValueError('outside automaton class')
    if state < 2:
        return state + 1
    if signal == 'block':
        return 2
    return 0 if signal == 'request' or mode else 2


def recurrent(mode, word):
    """Exact eventual cycle for a nonempty periodically repeated input word."""
    if not word:
        raise ValueError('empty input period')
    seen, states = {}, []
    state, phase = 0, 0
    while (state, phase) not in seen:
        seen[state, phase] = len(states)
        states.append(state)
        state = step(mode, state, word[phase])
        phase = (phase + 1) % len(word)
    return 0 in states[seen[state, phase]:]


def dependency_order(nodes):
    """Structural acyclicity only; this cannot prove a mathematical premise."""
    by_id = {n['id']: n for n in nodes}
    if not nodes or len(by_id) != len(nodes):
        raise ValueError('empty or duplicate dependency population')
    for node in nodes:
        if node['kind'] not in ('assumption', 'theorem', 'hypothesis', 'finite-check'):
            raise ValueError('unknown dependency kind')
        if len(set(node['requires'])) != len(node['requires']) or not set(node['requires']) <= by_id.keys():
            raise ValueError('unknown or duplicate prerequisite')
        if node['kind'] == 'assumption' and node['requires']:
            raise ValueError('assumption has a derived prerequisite')
    finished, active, order = set(), set(), []
    def visit(key):
        if key in active:
            raise ValueError('circular logical dependency: ' + key)
        if key in finished:
            return
        active.add(key)
        for parent in sorted(by_id[key]['requires']):
            visit(parent)
        active.remove(key)
        finished.add(key)
        order.append(key)
    for key in sorted(by_id):
        visit(key)
    return tuple(order)


def conditional_on(nodes, key):
    """Transitive assumptions and hypotheses; not a truth certificate."""
    dependency_order(nodes)
    by_id = {n['id']: n for n in nodes}
    if key not in by_id:
        raise ValueError('unknown claim')
    found = set()
    def visit(k):
        if by_id[k]['kind'] in ('assumption', 'hypothesis'):
            found.add(k)
        for parent in by_id[k]['requires']:
            visit(parent)
    visit(key)
    return tuple(sorted(found))


def lift(edges, mapping, root, path):
    if not path or mapping[root] != path[0]:
        return ()
    paths = [(root,)]
    for target in path[1:]:
        paths = [p + (y,) for p in paths for x, y in sorted(edges)
                 if x == p[-1] and mapping[y] == target]
    return tuple(sorted(paths))


def common_family_transport(source_family, target_family, iota_x, iota_y, admitted):
    """Mirrors section 8.1 on finite families. One operator position with states S and two deployments
    given by injections iota_x, iota_y (dicts S -> point); source_family and target_family are the
    declared families of S-histories the two deployments realise, and admitted is the set of admitted
    S-histories, fixed on the position before transport. The transport b = iota_y o iota_x^-1 acts
    pointwise. Returns the premises of M6 as named booleans and the admitted target histories, rooted in
    the image of a source root, that have no lift."""
    gamma_x = {tuple(iota_x[s] for s in h): tuple(h) for h in source_family}
    gamma_y = {tuple(iota_y[s] for s in h): tuple(h) for h in target_family}
    b = {iota_x[s]: iota_y[s] for s in iota_x}
    c = {point: source for source, point in b.items()}
    forward = {g: tuple(b[p] for p in g) for g in gamma_x}
    backward = {g: tuple(c[p] for p in g) for g in gamma_y}
    admitted = {tuple(h) for h in admitted}
    unlifted = []
    for root in sorted(iota_x.values()):
        for eta, decoded in sorted(gamma_y.items()):
            if not eta or eta[0] != b[root] or decoded not in admitted:
                continue
            lifted = backward[eta]
            if not (lifted in gamma_x and gamma_x[lifted] in admitted and lifted[0] == root and forward[lifted] == eta):
                unlifted.append(eta)
    return dict(
        bijection=(all(forward[g] in gamma_y and backward[forward[g]] == g for g in gamma_x)
                   and all(backward[g] in gamma_x and forward[backward[g]] == g for g in gamma_y)),
        decoding=all(forward[g] in gamma_y and gamma_y[forward[g]] == gamma_x[g] for g in gamma_x),
        admission=all((gamma_x[g] in admitted) == (forward[g] in gamma_y and gamma_y[forward[g]] in admitted)
                      for g in gamma_x),
        initial_square=all(forward[g][0] == b[g[0]] for g in gamma_x if g),
        rooted_lifting=not unlifted,
        unlifted=tuple(unlifted))


def residual_accepts(budget, past, future):
    return sum(past) + sum(future) <= budget


def periodic_events(prefix, period):
    """Recurrence only: infinitely many ones in prefix + period + period + ..."""
    if not period:
        raise ValueError('empty period')
    return any(period)


def lasso_prefix(prefix, period, length):
    """The finite mirror: first `length` letters of prefix + period + period + ..."""
    if not period or type(length) is not int or length < 0:
        raise ValueError('nonempty period and nonnegative length required')
    return tuple(prefix[k] if k < len(prefix) else period[(k - len(prefix)) % len(period)] for k in range(length))


def p_star_periodic(prefix, period):
    """The predicate P* of Mirrors M5 on prefix + period repeated: first letter one, no two
    adjacent ones, infinitely many ones (the recurrence subclaim above)."""
    if not period or any(bit not in (0, 1) for bit in tuple(prefix) + tuple(period)):
        raise ValueError('binary word with nonempty period required')
    # The prefix, one period and one more letter contain every adjacent pair of the
    # infinite word: inside the prefix, at the junction, inside the period and at its wrap.
    word = lasso_prefix(prefix, period, len(prefix) + len(period) + 1)
    first_ok = word[:1] == (1,)
    adjacent_ok = all(not (left and right) for left, right in zip(word, word[1:]))
    return first_ok and adjacent_ok and periodic_events(prefix, period)


def restricted_preservation(a, r, witnesses):
    witnesses = tuple(witnesses)  # read once: a one-shot iterator must not reach the domain empty
    zero = (0,) * len(a)
    if any(dot(a, v) == 0 for v in witnesses):
        raise ValueError('selected vector is not a witness')
    domain = tuple(witnesses) + (zero,)
    return decoder(tuple(dot(r, v) for v in domain),
                   tuple(dot(a, v) != 0 for v in domain)) is not None


def loss_kind(a, r, witnesses):
    """Loss on the supplied selected witnesses W0 only: 'none', 'partial' or 'all-selected-lost'.

    Losing every selected witness is not global destruction of the transported pairing; that
    is the separate case r = 0, in which no a-witness of the whole space survives."""
    witnesses = tuple(witnesses)
    if not witnesses or any(dot(a, v) == 0 for v in witnesses):
        raise ValueError('nonempty witness population required')
    surviving = sum(dot(r, v) != 0 for v in witnesses)
    return 'none' if surviving == len(witnesses) else ('all-selected-lost' if surviving == 0 else 'partial')


def pullback(functional, matrix):
    if len(functional) != len(matrix) or not matrix or len({len(row) for row in matrix}) != 1:
        raise ValueError('pullback type mismatch')
    return tuple(dot(functional, column) for column in zip(*matrix))


def contact_record(wire, bias):
    """Baseline and driven reading of a two-node binary contact."""
    return bias, bias ^ wire


def read_conduction(record):
    baseline, driven = record
    return baseline ^ driven


def interval_defect(left, right):
    """Endpoint mismatch for a constant binary section on an interval."""
    return (right - left) % 2


def foucault_transport(initial, sin_latitude, longitude_turns):
    """The declared closed-form transport law, not a solution of the connection.

    Unwrapped angle in turns, read in the local tangent frame of the parallel, along a
    latitude arc of increasing longitude: a full lap rotates by -sin(latitude) turns.
    Open arcs depend on that frame convention; poles are outside the declared loops."""
    return initial - sin_latitude * longitude_turns


def foucault_readings(angle):
    return angle % 1, angle % Fraction(1, 2)


def shear_step(point, time):
    x, y = point
    return x - time * y, y


def shear_endpoint_counts(start, horizon):
    """Multiplicities under independent equiprobable unit shears."""
    if horizon < 0:
        raise ValueError("negative horizon")
    counts = {start: 1}
    for _ in range(horizon):
        following = {}
        for point, count in counts.items():
            for sign in (-1, 1):
                dest = shear_step(point, sign)
                following[dest] = following.get(dest, 0) + count
        counts = following
    return counts


def paid_shear_step(point, burden, time, cost, cap):
    """An unaffordable step has no successor in the declared account."""
    if cost <= 0:
        raise ValueError("step cost must be positive")
    charged = burden + cost
    if charged > cap:
        return None
    return shear_step(point, time), charged


def strict_retained(before, after):
    """Hint-off after channel against the before channel; it takes no message."""
    return strict_refines(after, before)


def borrowed_reading(before, message):
    """Joint reading (V0, Z) of the before channel and a message on one fixed carrier; not a learner."""
    if len(before) != len(message):
        raise ValueError('different observation carriers')
    return tuple(zip(before, message))


def covector_preservation_pair(functional, first, second):
    """Return (both arrows preserve the fixed covector, their composite preserves it)."""
    eta = tuple(functional)
    dimension = len(eta)
    for matrix in (first, second):
        if not dimension or len(matrix) != dimension or any(len(row) != dimension for row in matrix):
            raise ValueError('expected endomorphisms of the common covector space')
    after_first = pullback(eta, first)
    after_second = pullback(eta, second)
    stepwise = after_first == eta and after_second == eta
    terminal = pullback(after_second, first) == eta
    return stepwise, terminal


def gradient(potential, edges):
    return tuple(Fraction(potential[b]) - Fraction(potential[a]) for a, b in edges)


def circulation(values, edges, path):
    index = {edge: i for i, edge in enumerate(edges)}
    total = Fraction(0)
    for a, b in zip(path, path[1:]):
        if (a, b) in index:
            total += values[index[a, b]]
        elif (b, a) in index:
            total -= values[index[b, a]]
        else:
            raise ValueError('path edge absent')
    return total


def common_preservation(left, right):
    return bool(set(left) & set(right))


def equal_nonempty_preservation(left, right):
    return bool(left) and set(left) == set(right)


def plane_vector(values):
    """Exactly two coordinates of a declared plane; any other shape is outside the class."""
    if type(values) not in (tuple, list) or len(values) != 2:
        raise ValueError('exactly two plane coordinates required')
    return tuple(values)


def diagonal_connection(parameter):
    """Matrix of d + diag(a, b) dt in the declared two-parameter class."""
    pair = plane_vector(parameter)
    return ((pair[0], 0), (0, pair[1]))


def covariant_derivative(matrix, value, derivative):
    """dt-coefficient of v' + A v for a section of the trivial plane bundle over a line."""
    connection = tuple(plane_vector(row) for row in plane_vector(matrix))
    section, rate = plane_vector(value), plane_vector(derivative)
    return tuple(rate[i] + sum(connection[i][j] * section[j] for j in range(2)) for i in range(2))


def cycle_relations(parities):
    if len(parities) < 3 or any(p not in (0,1) for p in parities):
        raise ValueError('binary cycle with at least three nodes required')
    return tuple(Relation(str(i), ('x'+str(i), 'x'+str((i+1)%len(parities))),
                          tuple((a,b) for a,b in product((0,1),repeat=2) if (a+b)%2 == parity))
                 for i,parity in enumerate(parities))


def pairwise_envelope(domains, relation):
    validate(domains, (relation,))
    pair_relations = tuple(Relation('pair-'+str(i)+'-'+str(j), (relation.scope[i],relation.scope[j]),
                                    project(relation.rows,(i,j)))
                           for i,j in combinations(range(len(relation.scope)),2))
    return solve(domains,pair_relations)


def ambiguity_witness(observation, verdict):
    if len(observation) != len(verdict):
        raise ValueError('different carriers')
    for i in range(len(observation)):
        for j in range(i+1,len(observation)):
            if observation[i] == observation[j] and verdict[i] != verdict[j]:
                return (i,j)
    return None


def prefix_reflecting(pairs):
    """Finite, equal-clock bijections; reflect every observed prefix."""
    pairs = tuple(pairs)
    if not pairs or len({x for x, _ in pairs}) != len(pairs) or len({y for _, y in pairs}) != len(pairs):
        raise ValueError('nonempty bijection required')
    lengths = {len(word) for pair in pairs for word in pair}
    if len(lengths) != 1:
        raise ValueError('common finite clock required')
    return all(y[:k] != v[:k] or x[:k] == u[:k]
               for x, y in pairs for u, v in pairs for k in range(next(iter(lengths)) + 1))


def language_derivative(language, prefix):
    return frozenset(word[len(prefix):] for word in language if word[:len(prefix)] == prefix)


def charged_continuations(language, prefix, costs, load, capacity):
    """Residual non-budget constraints are supplied by the original language."""
    if load < 0 or capacity < load or any(value < 0 for value in costs.values()):
        raise ValueError('nonnegative charged model required')
    charged = load + sum(costs[symbol] for symbol in prefix)
    if charged > capacity:
        return frozenset()
    return frozenset(tail for tail in language_derivative(language, prefix)
                     if charged + sum(costs[symbol] for symbol in tail) <= capacity)


def residual_key_sufficient(residuals, keys):
    if len(residuals) != len(keys):
        raise ValueError('different prefix carriers')
    return all(keys[i] != keys[j] or residuals[i] == residuals[j]
               for i in range(len(keys)) for j in range(i))


def mode_trace(mode, signals):
    current, trace = 0, [0]
    for signal in signals:
        current = step(mode, current, signal)
        trace.append(current)
    return tuple(trace)


def delayed_events(delay, count):
    if type(delay) is not int or type(count) is not int or delay < 0 or count < 0:
        raise ValueError('nonnegative integers required')
    return tuple(range(delay, delay + count))


def debit_ledger(debits, budget):
    """Legality in a budget, as Mirrors declares it before M11: step k debits d_k >= 0 from one budget R.

    Returns (legal, events): legal when no prefix overdraws R; events counts the steps
    of positive debit. Unit debits give the event words of M11."""
    debits = tuple(debits)  # read once: validation must not exhaust a one-shot iterator
    if budget < 0 or any(debit < 0 for debit in debits):
        raise ValueError('nonnegative budget and debits required')
    balance, events, legal = budget, 0, True
    for debit in debits:
        if debit > 0:
            events += 1
            balance -= debit
            legal = legal and balance >= 0
    return legal, events


def silence_bounded(events, maximum_gap):
    """Zero-indexed event positions; stopping is allowed, unlike driven completion."""
    events = tuple(events)
    if type(maximum_gap) is not int or maximum_gap < 0:
        raise ValueError('nonnegative integer gap required')
    if any(type(x) is not int or x < 0 for x in events) or tuple(sorted(set(events))) != tuple(events):
        raise ValueError('strictly increasing event positions required')
    return all(b - a <= maximum_gap + 1 for a, b in zip((-1,) + tuple(events), events))


def witness_charge(c, sigmas):
    if c <= 0:
        raise ValueError('positive charge multiplier required')
    return c * sum(abs(sigma) for sigma in sigmas)


def paid_witness_prefix(c, sigmas, budget):
    """M15's law on a finite word: event n debits c|sigma_n| from one budget R, in order.

    Returns (paid, remaining): the events paid before the first unaffordable one and the
    balance left. A zero amplitude costs nothing."""
    if c <= 0 or budget < 0:
        raise ValueError('positive multiplier and nonnegative budget required')
    remaining, paid = budget, 0
    for sigma in sigmas:
        debit = c * abs(sigma)
        if debit > remaining:
            break
        remaining -= debit
        paid += 1
    return paid, remaining


def driven_events(events, budget, maximum_gap):
    """At each start/restart with budget left, an event must occur in its window."""
    events = tuple(events)
    if type(budget) is not int or budget < 0 or type(maximum_gap) is not int or maximum_gap < 0:
        raise ValueError('nonnegative integer budget and gap required')
    if any(type(x) is not int or x < 0 for x in events) or tuple(sorted(set(events))) != tuple(events):
        raise ValueError('strictly increasing event positions required')
    if len(events) > budget:
        return False
    for spent, position in enumerate((-1,) + tuple(events)):
        if spent < budget and not any(position < event <= position + maximum_gap + 1 for event in events):
            return False
    return True


def frontier_debit(initial, ratio, return_index):
    if initial <= 0 or not 0 < ratio < 1 or type(return_index) is not int or return_index < 0:
        raise ValueError('positive frontier, contracting ratio, nonnegative index required')
    return initial * ratio ** return_index * (1 - ratio)


def simplex_boundary(simplex):
    """Ordinary oriented boundary; vertices have zero boundary."""
    if not simplex or len(set(simplex)) != len(simplex):
        raise ValueError('nonempty simplex with distinct vertices required')
    if len(simplex) == 1:
        return {}
    return {simplex[:i] + simplex[i+1:]: (-1) ** i for i in range(len(simplex))}


def selected_trace_equal(left, right, reading):
    if len(left) != len(right):
        return False
    return tuple(reading[state] for state in left) == tuple(reading[state] for state in right)
