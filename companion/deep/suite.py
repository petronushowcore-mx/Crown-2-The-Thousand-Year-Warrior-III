"""Deterministic finite families for the three works and their composition.

The result certifies the declared finite population, never an empirical hypothesis.
No providers, network, randomness, float arithmetic or assert statements are used.
"""
import argparse
import copy
import hashlib
import json
import sys
from fractions import Fraction
from itertools import combinations, permutations, product
from pathlib import Path

import relations as model

PROFILE = 'quick'
OBSERVATIONS = 0
EXPECTED_TEETH = 41
WORKS = ('mirrors', 'warrior', 'body')


def check(condition, witness=None):
    global OBSERVATIONS
    OBSERVATIONS += 1
    if not condition:
        raise AssertionError(repr(witness))


def rejected(call):
    try:
        call()
    except ValueError:
        return True
    return False


def subsets(values):
    values = tuple(values)
    for mask in range(1 << len(values)):
        yield tuple(v for i, v in enumerate(values) if mask & (1 << i))


def binary_relation(name, a, b, mask):
    return model.Relation(name, (a, b), tuple(row for i, row in enumerate(product((0, 1), repeat=2)) if mask & (1 << i)))


def blocks(values):
    """Independent connected-components representation of an observation."""
    remaining, answer = set(range(len(values))), []
    while remaining:
        first = min(remaining)
        component = {i for i in remaining if values[i] == values[first]}
        answer.append(frozenset(component))
        remaining -= component
    return tuple(answer)


def lasso_walk(prefix, period):
    """Independent walk of the lasso graph of prefix + period repeated.

    Returns the letters of the visited nodes, each node once, and the index at which the
    walk re-enters its cycle."""
    letters, seen = [], {}
    node = ('prefix', 0) if prefix else ('period', 0)
    while node not in seen:
        seen[node] = len(letters)
        part, index = node
        letters.append(prefix[index] if part == 'prefix' else period[index])
        if part == 'prefix' and index + 1 < len(prefix):
            node = ('prefix', index + 1)
        elif part == 'prefix':
            node = ('period', 0)
        else:
            node = ('period', (index + 1) % len(period))
    return tuple(letters), seen[node]


def lasso_letters(prefix, period, length):
    """First letters of the infinite word, read by going round the cycle of the walk."""
    letters, entry = lasso_walk(prefix, period)
    cycle = letters[entry:]
    return tuple(letters[k] if k < len(letters) else cycle[(k - len(letters)) % len(cycle)] for k in range(length))


def lasso_p_star(prefix, period):
    """P* along every edge of the lasso graph, the closing edge of its cycle included."""
    letters, entry = lasso_walk(prefix, period)
    edges = tuple(zip(letters, letters[1:])) + ((letters[-1], letters[entry]),)
    return letters[0] == 1 and (1, 1) not in edges and 1 in letters[entry:]


def m11_witness(silence, word, prefix_length, budget):
    """Mirrors M11 for one pair of finite event words under unit debits and budget N:
    equal readings on prefix_length steps, both legal, the spending word admitted
    (exactly N events) and silence not."""
    silent_legal, silent_events = model.debit_ledger(silence, budget)
    word_legal, word_events = model.debit_ledger(word, budget)
    return (word[:prefix_length] == silence[:prefix_length] and silent_legal and word_legal
            and silent_events != budget and word_events == budget)


def stepwise_payment(c, sigmas, budget):
    """Independent balances for M15: debit each event in order, stop at the first unaffordable."""
    balance, balances = budget, [budget]
    for sigma in sigmas:
        charge = c * sigma if sigma >= 0 else c * -sigma
        if charge > balance:
            break
        balance -= charge
        balances.append(balance)
    return balances


def mat_apply(matrix, vector):
    return tuple(matrix[i][0] * vector[0] + matrix[i][1] * vector[1] for i in range(2))


def mat_mul(left, right):
    return tuple(tuple(left[i][0] * right[0][j] + left[i][1] * right[1][j] for j in range(2)) for i in range(2))


def mat_inverse(matrix):
    (p, q), (r, s) = matrix
    determinant = Fraction(p * s - q * r)
    return ((s / determinant, -q / determinant), (-r / determinant, p / determinant))


def t_G01_join_complete_assignments():
    width = 4 if PROFILE == 'full' else 3
    names = tuple('abcd'[:width])
    domains = {name: (0, 1) for name in names}
    relation_count = width - 1
    for masks in product(range(16), repeat=relation_count):
        relations = tuple(binary_relation(str(i), names[i], names[i+1], mask) for i, mask in enumerate(masks))
        actual = model.solve(domains, relations)
        expected = model.enumerate_solutions(domains, relations)
        check(actual == expected, (masks, actual, expected))
    check(len(model.solve(domains, ())) == 2 ** width, 'free variables')
    check(model.solve(domains, (model.Relation('false', (), ()),)) == (), 'nullary false')
    check(len(model.solve(domains, (model.Relation('true', (), ((),)),))) == 2 ** width, 'nullary true')


def t_G02_global_obstruction():
    domains = dict(x=(0,1), y=(0,1), z=(0,1))
    triangle = (binary_relation('xy', 'x', 'y', 9), binary_relation('yz', 'y', 'z', 9), binary_relation('xz', 'x', 'z', 6))
    check(all(model.solve(domains, pair) for pair in combinations(triangle, 2)), 'each pair has a witness')
    check(not model.solve(domains, triangle), 'no shared witness')
    check(model.minimal_conflicts(domains, triangle) == ((0,1,2),), 'minimal triangle conflict')
    empty = model.Relation('empty', ('x',), ())
    check(model.minimal_conflicts(domains, triangle + (empty,)) == ((3,), (0,1,2)), 'all minimal conflicts')
    honest = triangle[:2] + (binary_relation('xz', 'x', 'z', 9),)
    check(len(model.solve(domains, honest)) == 2, 'consistent cycle')


def t_G03_types_and_population():
    good = model.Relation('r', ('x',), ((0,), (1,)))
    model.validate({'x': (0,1)}, (good,))
    bad = [({}, ()), ({'x': ()}, ()), ({'x': (0,0)}, ()),
           ({'x': (0,1)}, (good, good)),
           ({'x': (0,1)}, (model.Relation('r', ('y',), ((0,),)),)),
           ({'x': (0,1)}, (model.Relation('r', ('x',), ((2,),)),)),
           ({'x': (0,1)}, (model.Relation('r', ('x','x'), ((0,0),)),))]
    for domains, relations in bad:
        check(rejected(lambda: model.validate(domains, relations)), (domains, relations))


def t_G04_proof_dependencies():
    nodes = [dict(id='domain',kind='assumption',requires=[]),
             dict(id='criterion',kind='theorem',requires=['domain']),
             dict(id='physical-reading',kind='hypothesis',requires=['domain']),
             dict(id='application',kind='finite-check',requires=['criterion','physical-reading'])]
    check(model.dependency_order(nodes) == ('domain','criterion','physical-reading','application'))
    check(model.conditional_on(nodes, 'application') == ('domain','physical-reading'), 'hypothesis remains visible')
    for bad in ([], nodes + [nodes[0]], [dict(id='a',kind='theorem',requires=['missing'])],
                [dict(id='a',kind='theorem',requires=['b']),dict(id='b',kind='theorem',requires=['a'])]):
        check(rejected(lambda: model.dependency_order(bad)), bad)
    for order in permutations(nodes):
        check(model.dependency_order(order) == model.dependency_order(nodes), 'declaration-order invariance')


def t_G05_projection_and_composition():
    # A history is transferred to a witness and a readout. The verdict is not an edge label.
    domains = dict(h=(0,1,2), w=(0,1), r=(0,1), q=(0,1))
    hw = model.Relation('history-witness', ('h','w'), ((0,0),(1,1),(2,0)))
    wq = model.Relation('witness-verdict', ('w','q'), ((0,0),(1,1)))
    hidden = model.Relation('history-readout', ('h','r'), ((0,0),(1,0),(2,0)))
    informative = model.Relation('history-readout', ('h','r'), ((0,0),(1,1),(2,0)))
    for readout, expected in ((hidden,False),(informative,True)):
        rows = model.solve(domains,(hw,wq,readout))
        check(rows == model.enumerate_solutions(domains,(hw,wq,readout)))
        # Column order h,q,r,w is canonical, not insertion order.
        qr = model.project(rows,(1,2))
        observation, verdict = tuple(row[1] for row in qr), tuple(row[0] for row in qr)
        check((model.decoder(observation,verdict) is not None) == expected, (qr, expected))
        for order in permutations((hw,wq,readout)):
            check(model.solve(dict(reversed(list(domains.items()))),order) == rows)
        # A bijective rename of variable names cannot change the assignment relation.
        rename = dict(h='v3',w='v0',r='v2',q='v1')
        renamed = tuple(model.Relation(r.name,tuple(rename[k] for k in r.scope),r.rows) for r in (hw,wq,readout))
        changed = model.solve({rename[k]:v for k,v in domains.items()},renamed)
        restored = tuple(sorted((r[3],r[1],r[2],r[0]) for r in changed))
        check(restored == rows, 'node rename')


def t_M01_fibres_and_decoders():
    maximum = 6 if PROFILE == 'full' else 4
    relabel = {0: 5, 1: 0, 2: 3}  # a bijective renaming of the observed values
    for size in range(1,maximum+1):
        for observation in product(range(3),repeat=size):
            renamed = tuple(relabel[x] for x in observation)
            for verdict in product(range(2),repeat=size):
                a = model.decoder(observation,verdict)
                b = model.decoder_by_enumeration(observation,verdict)
                check((a is None) == (b is None),(observation,verdict,a,b))
                if a is not None:
                    check(tuple(a[x] for x in observation) == verdict)
                # Consistently renamed observation labels keep existence and the recovered verdict.
                c = model.decoder(renamed,verdict)
                check((c is None) == (a is None),('renamed labels',observation,verdict))
                if c is not None:
                    check(tuple(c[x] for x in renamed) == verdict,('renamed labels',observation,verdict))
    # Merging two labels is not a renaming: it can mix a fibre that was homogeneous.
    check(model.decoder((0,1),(0,1)) is not None and model.decoder((0,0),(0,1)) is None, 'merged labels')
    check(rejected(lambda:model.decoder((0,),(0,1))), 'carrier mismatch')


def t_G07_higher_order_relations():
    domains = dict(x=(0,1),y=(0,1),z=(0,1))
    complete = tuple(product((0,1),repeat=3))
    for rows in subsets(complete):
        relation = model.Relation('ternary',('x','y','z'),rows)
        envelope = model.pairwise_envelope(domains,relation)
        expected = tuple(v for v in complete if all(any((v[i],v[j]) == (r[i],r[j]) for r in rows) for i,j in combinations(range(3),2)))
        check(envelope == expected, rows)
        check(set(rows) <= set(envelope), rows)
        check(model.solve(domains,(relation,)) == rows, 'ternary relation retained')
    parity = tuple(r for r in complete if sum(r)%2 == 0)
    check(len(model.pairwise_envelope(domains,model.Relation('parity',('x','y','z'),parity))) == 8)
    check(len(parity) == 4, 'pairwise projections lose the three-node constraint')
    # Arbitrary arity: parity is invisible to every one-coordinate deletion.
    for width in range(3,(9 if PROFILE == 'full' else 5)+1):
        rows = tuple(r for r in product((0,1),repeat=width) if sum(r)%2 == 0)
        for missing in range(width):
            indices = tuple(i for i in range(width) if i != missing)
            check(len(model.project(rows,indices)) == 2**(width-1), (width,missing))


def t_G08_joint_reading_and_counterexample():
    states = tuple(product((0,1),repeat=2))
    first,second = tuple(r[0] for r in states),tuple(r[1] for r in states)
    for verdict in product((0,1),repeat=4):
        for observation in (first,second,states,(0,0,0,0)):
            witness = model.ambiguity_witness(observation,verdict)
            expected = next(((i,j) for i,j in combinations(range(4),2) if observation[i]==observation[j] and verdict[i]!=verdict[j]), None)
            check(witness == expected, (observation,verdict))
            check((witness is None) == (model.decoder_by_enumeration(observation,verdict) is not None))
            if witness is not None:
                i,j = witness
                check(observation[i] == observation[j] and verdict[i] != verdict[j], witness)
    xor = (0,1,1,0)
    check(model.ambiguity_witness(first,xor) is not None and model.ambiguity_witness(second,xor) is not None)
    check(model.ambiguity_witness(states,xor) is None, 'joint reading recovers what neither marginal recovers')
    check(rejected(lambda:model.ambiguity_witness((0,),(0,1))), 'carrier mismatch')


def t_M02_rooted_path_lifting():
    size = 3 if PROFILE == 'full' else 2
    horizon = 3 if PROFILE == 'full' else 2
    all_edges = tuple(product(range(size),repeat=2))
    for edges in subsets(all_edges):
        edge_set = set(edges)
        for mapping in product(range(2),repeat=size):
            for length in range(1,horizon+2):
                # Enumerated source paths form an independent complete reference table.
                table = {}
                for path in product(range(size),repeat=length):
                    if all(pair in edge_set for pair in zip(path,path[1:])):
                        target = tuple(mapping[x] for x in path)
                        table.setdefault((path[0],target),[]).append(path)
                for root in range(size):
                    for target in product(range(2),repeat=length):
                        check(model.lift(edges,mapping,root,target) == tuple(table.get((root,target),())),(edges,mapping,root,target))


def t_M03_residual_and_budget():
    maximum = 6 if PROFILE == 'full' else 3
    for budget in range(0,maximum+1):
        for past in product(range(3),repeat=3):
            for future in product(range(3),repeat=3):
                remaining = budget
                for debit in past + future:
                    remaining -= debit
                check(model.residual_accepts(budget,past,future) == (remaining >= 0),(budget,past,future))
    # Same current visible state is deliberately absent from the retained cost coordinate.
    check(model.residual_accepts(4,(1,),(2,)))
    check(not model.residual_accepts(4,(3,),(2,)))


def t_M04_periodic_history_boundary():
    maximum = 9 if PROFILE == 'full' else 5
    for length in range(1,maximum+1):
        for period in product((0,1),repeat=length):
            # Recurrence subclaim: the repeated tail alone decides infinitely many ones.
            recurring = {i for i in range(length) if period[i] == 1}
            for prefix in ((0,), (1,), (1,0,1)):
                check(model.periodic_events(prefix,period) == bool(recurring),(prefix,period))
            # P* against an independent walk of the lasso graph: first letter, prefix/tail
            # junction, adjacency inside the period and across its wrap.
            for prefix in ((), (0,), (1,), (1,0), (1,1), (0,1,0)):
                verdict = lasso_p_star(prefix,period)
                check(model.p_star_periodic(prefix,period) == verdict,('P*',prefix,period))
                horizon = len(prefix) + 3*length
                reading = model.lasso_prefix(prefix,period,horizon)
                check(reading == lasso_letters(prefix,period,horizon),('reading',prefix,period))
                # One complete period absorbed into the prefix: the same word and verdict.
                absorbed = tuple(prefix) + period
                check(model.lasso_prefix(absorbed,period,horizon) == reading,('absorbed',prefix,period))
                check(model.p_star_periodic(absorbed,period) == verdict,('absorbed',prefix,period))
                # A rotated tail represents the same word only with the prefix adjustment.
                adjusted = (tuple(prefix) + period[:1], period[1:] + period[:1])
                check(model.lasso_prefix(*adjusted,horizon) == reading,('rotated',prefix,period))
                check(model.p_star_periodic(*adjusted) == verdict,('rotated',prefix,period))
    # Without the adjustment a rotation changes the word, here from admitted to rejected.
    check(model.p_star_periodic((1,),(0,1)) and not model.p_star_periodic((1,),(1,0)), 'unadjusted rotation')
    for depth in range(0,maximum*10):
        # An arbitrarily selected finite depth can be shared before two different tails.
        prefix = (0,) * depth
        check(not model.periodic_events(prefix,(0,)))
        check(model.periodic_events(prefix,(1,)))
    # The pair of M5 with one common prefix: 10...0 then silence, against the same prefix
    # then a separated alternating tail. Their readings agree through one letter past the
    # prefix; their P* verdicts differ. No finite sweep establishes the topology theorem.
    for depth in range(1,maximum*10):
        common = (1,) + (0,) * (depth-1)
        stopped, continued = (common,(0,)), (common,(0,1))
        for size in (depth, depth+1):
            check(model.lasso_prefix(*stopped,size) == model.lasso_prefix(*continued,size)
                  == lasso_letters(*stopped,size),('M5 common prefix',depth,size))
        check(model.lasso_prefix(*stopped,depth+2) != model.lasso_prefix(*continued,depth+2),('M5 tails',depth))
        check(not model.p_star_periodic(*stopped) and model.p_star_periodic(*continued),('M5 verdicts',depth))


def t_M05_full_restart_automaton():
    alphabet = ('silence','request','block')
    table = {0: {'silence':(1,2,2),'request':(1,2,0),'block':(1,2,2)},
             1: {'silence':(1,2,0),'request':(1,2,0),'block':(1,2,2)}}
    for mode,state,signal in product((0,1),range(3),alphabet):
        check(model.step(mode,state,signal) == table[mode][signal][state],(mode,state,signal))
    for length in range(1,(7 if PROFILE == 'full' else 4)+1):
        for word in product(alphabet,repeat=length):
            for mode in (0,1):
                # 3*length product states: after that bound the trajectory is on its cycle.
                state, tail = 0, []
                for time in range(6*length):
                    state = table[mode][word[time % length]][state]
                    if time >= 3*length:
                        tail.append(state)
                check(model.recurrent(mode,word) == (0 in tail),(mode,word,tail))
    check(model.recurrent(1,('silence',)) and not model.recurrent(0,('silence',)))
    check(model.recurrent(0,('request',)) and not model.recurrent(1,('block',)))


def t_W01_linear_transfer():
    maximum = 5 if PROFILE == 'full' else 3
    for dimension in range(1,maximum+1):
        vectors = tuple(product((-1,0,1),repeat=dimension))
        for a in vectors:
            if not any(a):
                continue
            for r in vectors:
                expected = model.rank((a,r)) == model.rank((r,))
                check(model.kernel_preserved(a,r) == expected,(a,r))
                # Denominator changes exercise exact rational rather than float arithmetic.
                if dimension < 4:
                    ar = tuple(Fraction(x,7) for x in a)
                    rr = tuple(Fraction(x,11) for x in r)
                    check(model.kernel_preserved(ar,rr) == expected,(ar,rr))


def t_W02_restricted_witness_domains():
    vectors = tuple(product((-1,0,1),repeat=2))
    for a in vectors:
        if not any(a):
            continue
        witnesses = tuple(v for v in vectors if sum(a[i]*v[i] for i in range(2)) != 0)
        for domain in subsets(witnesses):
            for r in vectors:
                no_loss = all(sum(r[i]*v[i] for i in range(2)) != 0 for v in domain)
                check(model.restricted_preservation(a,r,domain) == no_loss,(a,r,domain))
    check(model.restricted_preservation((1,0),(0,1),((1,1),)))
    check(not model.restricted_preservation((1,0),(0,1),iter(((1,0),(1,1)))), 'a one-shot iterator of W0 is read once')
    check(not model.kernel_preserved((1,0),(0,1)), 'restricted does not imply global')


def t_W03_partial_and_total_loss():
    a = (1,0)
    # Losing every selected witness is relative to W0; global destruction is the case r = 0.
    # Here r = (-2,-1) loses the selected (1,-2) while the a-witness (1,0) survives.
    grid = tuple(v for v in product(range(-2,3),repeat=2) if v[0] != 0)  # every a-witness of the grid
    check(model.loss_kind(a,(-2,-1),((1,-2),)) == 'all-selected-lost','selected witness lost')
    check(model.loss_kind(a,(-2,-1),grid) == 'partial','another a-witness survives: not global')
    for r in product(range(-2,3),repeat=2):
        # On this grid a nonzero r keeps some a-witness, so all are lost exactly when r = 0.
        check((model.loss_kind(a,r,grid) == 'all-selected-lost') == (r == (0,0)),('global loss',r))
    population = ((1,-2),(1,-1),(1,0),(1,1),(1,2))
    for witnesses in subsets(population):
        if not witnesses:
            check(rejected(lambda:model.loss_kind(a,(1,0),witnesses)))
            continue
        for r in product(range(-2,3),repeat=2):
            values = [r[0]*v[0] + r[1]*v[1] for v in witnesses]
            expected = 'all-selected-lost' if all(x==0 for x in values) else ('none' if all(x!=0 for x in values) else 'partial')
            actual = model.loss_kind(a,r,witnesses)
            check(actual == expected,(r,witnesses,values))
            check(model.loss_kind(a,r,tuple(reversed(witnesses))) == actual,('permuted W0',r,witnesses))


def t_W04_composed_pullbacks():
    values = (-1,0,1) if PROFILE == 'full' else (0,1)
    matrices = tuple((r[:2],r[2:]) for r in product(values,repeat=4))
    for first,second in product(matrices,repeat=2):
        composed = tuple(tuple(sum(second[i][k]*first[k][j] for k in range(2)) for j in range(2)) for i in range(2))
        for functional in ((1,0),(0,1),(1,-1)):
            sequential = model.pullback(model.pullback(functional,second),first)
            direct = tuple(sum(functional[i]*second[i][k]*first[k][j] for i in range(2) for k in range(2)) for j in range(2))
            check(sequential == direct,(functional,first,second))
            check(model.pullback(functional,composed) == direct)


def t_G09_stepwise_and_terminal_preservation():
    verdicts = model.covector_preservation_pair

    def image(matrix, vector):
        x, y = vector
        return tuple(row[0] * x + row[1] * y for row in matrix)

    def reading(eta, vector):
        return eta[0] * vector[0] + eta[1] * vector[1]

    identity = ((1, 0), (0, 1))
    swap = ((0, 1), (1, 0))
    # The second fixture is the first in the basis change P=((1,1),(1,2)):
    # eta' = eta P^-1, v' = Pv and T' = P T P^-1.
    for eta, vector, arrow in (((1, 0), (1, 0), swap),
                               ((2, -1), (1, 1), ((1, 0), (3, -1)))):
        middle = image(arrow, vector)
        readings = tuple(reading(eta, v) for v in (vector, middle, image(arrow, middle)))
        check(readings == (1, 0, 1), (eta, vector, arrow, readings))
        check(verdicts(eta, arrow, arrow) == (False, True), ('compensation', eta, arrow))
        check(verdicts(eta, identity, identity) == (True, True), ('preserving pair', eta))

    # A projection can hide the second arrow's defect on its reachable image.
    projection, shear = ((1, 0), (0, 0)), ((1, 1), (0, 1))
    check(verdicts((1, 0), projection, shear) == (False, True), 'global second arrow')
    values = (-1, 0, 1) if PROFILE == 'full' else (0, 1)
    matrices = tuple((row[:2], row[2:]) for row in product(values, repeat=4))
    basis = ((1, 0), (0, 1))
    for first, second in product(matrices, repeat=2):
        for eta in ((1, 0), (0, 1), (1, -1)):
            # Independent oracle acts forward on a spanning set of column vectors.
            local = all(reading(eta, image(arrow, v)) == reading(eta, v)
                        for arrow in (first, second) for v in basis)
            end = all(reading(eta, image(second, image(first, v))) == reading(eta, v)
                      for v in basis)
            actual = verdicts(eta, first, second)
            check(actual == (local, end), (eta, first, second, actual, local, end))
            check(not local or end, ('composition closure', eta, first, second))


def t_B01_partition_refinement():
    maximum = 6 if PROFILE == 'full' else 4
    bell = (1,1,2,5,15,52,203)
    for size in range(1,maximum+1):
        all_partitions = tuple(model.partitions(size))
        check(len(set(all_partitions)) == bell[size],('Bell number',size))
        for fine,coarse in product(all_partitions,repeat=2):
            fine_blocks,coarse_blocks = blocks(fine),blocks(coarse)
            expected = all(any(b <= c for c in coarse_blocks) for b in fine_blocks)
            check(model.refines(fine,coarse) == expected,(fine,coarse))
            strict = expected and len(fine_blocks) > len(coarse_blocks)
            check(model.strict_refines(fine,coarse) == strict,(fine,coarse))
        for p in all_partitions:
            renamed = tuple(31-7*x for x in p)
            check(model.refines(p,renamed) and model.refines(renamed,p))
            check(not model.strict_refines(renamed,p),'bijective relabelling is not strict')


def t_B02_borrowed_and_retained():
    size = 5 if PROFILE == 'full' else 4
    ps = tuple(model.partitions(size))
    for before,message in product(ps,repeat=2):
        # The borrowed joint reading (V0,Z): its partition is the meet of the two partitions.
        borrowed = model.borrowed_reading(before,message)
        meet = {left & right for left in blocks(before) for right in blocks(message) if left & right}
        check(set(blocks(borrowed)) == meet,('joint reading',before,message))
        check(model.refines(borrowed,before),'borrowing preserves the old reading')
        # Z = g(V0) adds nothing; a message that splits an old fibre makes (V0,Z) strictly finer.
        redundant = all(any(b <= m for m in blocks(message)) for b in blocks(before))
        check(model.strict_refines(borrowed,before) == (not redundant),('borrowed strictness',before,message))
        relabelled = tuple(31-7*z for z in message)
        check(set(blocks(model.borrowed_reading(before,relabelled))) == meet,('relabelled message',before,message))
    for before,after in product(ps,repeat=2):
        # The intrinsic hint-off after channel takes no message: a hint cannot supply it.
        expected = all(any(b <= c for c in blocks(before)) for b in blocks(after)) and len(blocks(after)) > len(blocks(before))
        check(model.strict_retained(before,after) == expected,(before,after))
        if after == before:
            check(not model.strict_retained(before,after),'an unchanged channel is not a strict refinement')
    check(rejected(lambda: model.borrowed_reading((0,0),(0,))),'carrier mismatch')


def t_B03_contextual_cycles():
    for size in range(3,(8 if PROFILE == 'full' else 5)+1):
        names = tuple('x'+str(i) for i in range(size))
        domains = {name:(0,1) for name in names}
        for parities in product((0,1),repeat=size):
            relations = model.cycle_relations(parities)
            rows = model.solve(domains,relations)
            check(len(rows) == (0 if sum(parities)%2 else 2),(size,parities,rows))
            check(rows == model.enumerate_solutions(domains,relations))
            # Deleting any edge of the inconsistent cycle makes an open satisfiable chain.
            if sum(parities)%2:
                for i in range(size):
                    check(bool(model.solve(domains,relations[:i]+relations[i+1:])),(parities,i))


def t_B04_exact_cochains():
    for size in range(2,(6 if PROFILE == 'full' else 4)+1):
        edges = tuple(combinations(range(size),2))
        for potential in product((-1,0,1),repeat=size):
            values = model.gradient(potential,edges)
            for a,b,c in combinations(range(size),3):
                check(model.circulation(values,edges,(a,b,c,a)) == 0,(potential,a,b,c))
            for a,b in permutations(range(size),2):
                check(model.circulation(values,edges,(a,b)) == potential[b]-potential[a])
    # Exhaust every cochain on the tetrahedron, every selected set of faces.
    edges = tuple(combinations(range(4),2))
    faces = tuple(combinations(range(4),3))
    for values in product((-1,0,1),repeat=len(edges)):
        exact = any(all(p[b]-p[a] == value for (a,b),value in zip(edges,values))
                    for p in ((0,)+tail for tail in product(range(-1,2),repeat=3)))
        curls = tuple(model.circulation(values,edges,f+(f[0],)) for f in faces)
        check(exact == all(c==0 for c in curls),(values,curls))
        for selected in subsets(range(len(faces))):
            closed = all(curls[i]==0 for i in selected)
            if exact:
                check(closed,'exact implies closed on any selected faces')
    square = ((0,1),(1,2),(2,3),(0,3))
    check(model.circulation((1,0,0,0),square,(0,1,2,3,0)) == 1,'unfilled cycle has nonzero period')


def t_B05_preservation_class():
    zero, e1, e2 = (0,0), (1,0), (0,1)
    entries = (-1, 0, Fraction(1,2), 1)
    matrices = tuple((row[:2],row[2:]) for row in product(entries,repeat=4))
    sections = ((1,0), (0,1), (1,1), (1,-1), (Fraction(1,2),-1))
    rates = (zero, (1,0), (Fraction(-1,3),2))
    # Explicit covariant derivative v' + A v on the trivial plane bundle over a line,
    # against the column combination of A plus the section derivative.
    for matrix in matrices:
        for value in sections:
            for rate in rates:
                expected = tuple(x + y for x, y in zip(mat_apply(matrix,value),rate))
                check(model.covariant_derivative(matrix,value,rate) == expected,(matrix,value,rate))
    # An off-diagonal entry moves e2 into e1; the section derivative is part of the law:
    # for d the section with v' = v is not parallel, for d - dt on e1 it is.
    coupling = ((0,1),(0,0))
    check(model.covariant_derivative(coupling,e2,zero) == (1,0),'off-diagonal entry acts')
    check(model.covariant_derivative(coupling,e1,zero) == zero,'e1 parallel under the coupling')
    check(model.covariant_derivative(((0,0),(0,0)),e1,e1) == e1,'nonconstant section of d')
    check(model.covariant_derivative(((-1,0),(0,0)),e1,e1) == zero,'the same section parallel for d - dt')
    # The declared class d + diag(a,b) dt on a finite rational slice of its parameters.
    plane = tuple(product(entries,repeat=2))
    def preserved(section, parameters):
        return {p for p in parameters if model.covariant_derivative(model.diagonal_connection(p),section,zero) == zero}
    left, right = preserved(e1,plane), preserved(e2,plane)
    check(left == {p for p in plane if p[0] == 0} and right == {p for p in plane if p[1] == 0},'coordinate sections')
    check(left != right and model.common_preservation(left,right) and not model.equal_nonempty_preservation(left,right),
          'U=e1, W=e2: unequal sets with a common connection')
    nonzero = tuple(p for p in plane if p[0] and p[1])
    left, right = preserved(e1,nonzero), preserved(e2,nonzero)
    check(left == right == set() and not model.common_preservation(left,right) and not model.equal_nonempty_preservation(left,right),
          'U=e1, W=e2 without zero parameters: equal empty sets')
    left, right = preserved((1,1),plane), preserved((1,-1),plane)
    check(left == right == {(0,0)} and model.equal_nonempty_preservation(left,right),
          'U=e1+e2, W=e1-e2: independent blocks, equal nonempty sets')
    for a, b in plane:
        # On the whole diagonal class the derivatives are (a,b) and (a,-b): only a = b = 0
        # preserves either section. The slice checks this linear identity, not every real a,b.
        check(model.covariant_derivative(model.diagonal_connection((a,b)),(1,1),zero) == (a,b))
        check(model.covariant_derivative(model.diagonal_connection((a,b)),(1,-1),zero) == (a,-b))
    # A constant change of frame P: A' = P A P^-1, v' = P v; the derivative is carried by P,
    # so vanishing is preserved.
    for frame in (((1,1),(0,1)), ((2,1),(1,1)), ((0,1),(1,0))):
        inverse = mat_inverse(frame)
        for matrix in (matrices if PROFILE == 'full' else matrices[::5]):
            moved = mat_mul(mat_mul(frame,matrix),inverse)
            for value in sections:
                for rate in rates:
                    original = model.covariant_derivative(matrix,value,rate)
                    changed = model.covariant_derivative(moved,mat_apply(frame,value),mat_apply(frame,rate))
                    check(changed == mat_apply(frame,original) and (changed == zero) == (original == zero),(frame,matrix,value,rate))
    # Data outside the declared shapes is rejected, not interpreted.
    check(rejected(lambda: model.diagonal_connection((0,0,1))),'third undeclared parameter')
    for matrix in (((0,0,0),(0,0,0),(0,0,0)), ((0,0,1),(0,0)), (0,0)):
        check(rejected(lambda: model.covariant_derivative(matrix,zero,zero)),('matrix shape',matrix))
    for value, rate in (((0,0,1),zero), (zero,(0,0,1)), ((0,),zero)):
        check(rejected(lambda: model.covariant_derivative(((0,0),(0,0)),value,rate)),('section shape',value,rate))
    # Declared parameter classes: for U=e1, W=e2 and these diagonal connections the two
    # coordinate conditions are exact (checked above); every subset of {-1,0,1}^2.
    parameters = tuple(product((-1,0,1),repeat=2))
    for declared in subsets(parameters):
        left = {p for p in declared if p[0]==0}
        right = {p for p in declared if p[1]==0}
        exists = any(p[0]==0 and p[1]==0 for p in declared)
        coupled = any(p[0]==0 for p in declared) and all((p[0]==0)==(p[1]==0) for p in declared)
        check(model.common_preservation(left,right) == exists,(declared,left,right))
        check(model.equal_nonempty_preservation(left,right) == coupled,(declared,left,right))
    check(not model.equal_nonempty_preservation(set(),set()), 'empty equality is not preservation')
    diagonal = {(x,x) for x in (-1,0,1)}
    left = {p for p in diagonal if p[0]==0}
    right = {p for p in diagonal if p[1]==0}
    check(model.equal_nonempty_preservation(left,right),'restricted class can hide block independence')


def t_M06_prefix_reflection():
    width = 3 if PROFILE == 'full' else 2
    words = tuple(product((0, 1), repeat=width))
    for image in permutations(words):
        inverse = dict(zip(image, words))
        causal = True
        for k in range(width + 1):
            fibres = {}
            for target, source in inverse.items():
                fibres.setdefault(target[:k], set()).add(source[:k])
            causal = causal and all(len(values) == 1 for values in fibres.values())
        check(model.prefix_reflecting(tuple(zip(words, image))) == causal, image)
    anticipatory_inverse = (((0, 0, 0), (0, 2, 0)), ((0, 1, 1), (0, 2, 1)))
    check(not model.prefix_reflecting(anticipatory_inverse), 'forward causal bijection need not reflect prefixes')
    check(all(x[:k] != u[:k] or y[:k] == v[:k] for x,y in anticipatory_inverse for u,v in anticipatory_inverse for k in range(4)))
    check(rejected(lambda: model.prefix_reflecting((((0,), (0,)), ((1,), (0,))))), 'non-bijection')
    check(rejected(lambda: model.prefix_reflecting((((0,), (0,1)),))), 'different clocks')


def t_M07_charged_language_derivatives():
    words = tuple(product((0, 1), repeat=3))
    languages = subsets(words if PROFILE == 'full' else words[:4])
    prefixes = tuple(p for k in range(4) for p in product((0,1), repeat=k))
    for language in languages:
        for prices in product(range(3), repeat=2):
            costs = dict(enumerate(prices))
            for load, capacity in ((0,0), (0,1), (0,3), (1,2), (2,4)):
                admitted = []
                for word in language:
                    running, legal = load, True
                    for symbol in word:
                        running += prices[symbol]
                        if running > capacity:
                            legal = False
                    if legal:
                        admitted.append(word)
                for prefix in prefixes:
                    expected = frozenset(word[len(prefix):] for word in admitted if word[:len(prefix)] == prefix)
                    actual = model.charged_continuations(language, prefix, costs, load, capacity)
                    check(actual == expected, (language, prices, load, capacity, prefix, actual, expected))
    check(model.charged_continuations(((0,0),), (0,), {0:1}, 0, 1) == frozenset(), 'reset would admit an unaffordable two-step word')
    # This implementation compares final sums with the capacity, so it takes nonnegative prices only:
    # with prices 2 and -2 on capacity 1 the signed total 0 is within capacity although the first step
    # alone already exceeds it. The limit is this implementation's, not M8's: the manuscript's signed
    # extension checks every prefix of the continuation and keeps the load region, and is not modelled here.
    check(rejected(lambda: model.charged_continuations(((0,),), (), {0:-1}, 0, 1)), 'negative price rejected')
    language = {(0,0),(0,1),(1,0)}
    other = {(0,0),(1,1)}
    for prefix in prefixes:
        check(model.language_derivative(language & other,prefix) == model.language_derivative(language,prefix) & model.language_derivative(other,prefix))


def t_M08_residual_keys():
    size = 3 if PROFILE == 'full' else 2
    cells = tuple(product(range(size), repeat=2))
    for language in subsets(cells):
        residuals = tuple(frozenset(b for a,b in language if a == prefix) for prefix in range(size))
        for keys in product((0,1), repeat=size):
            key_values = tuple(sorted(set(keys)))
            inputs = tuple(product(key_values, range(size)))
            possible = False
            for bits in product((False, True), repeat=len(inputs)):
                table = dict(zip(inputs,bits))
                if all(table[keys[a],b] == ((a,b) in language) for a,b in cells):
                    possible = True
                    break
            check(model.residual_key_sufficient(residuals, keys) == possible, (language, keys, possible))
    check(not model.residual_key_sufficient(({0},{1}), (0,0)), 'same state key, different continuations')
    for capacity in range(5):
        costs = tuple(Fraction(k,2) for k in range(11))
        for lower in range(capacity+1):
            for higher in range(lower,capacity+1):
                lost = {x for x in costs if x+lower <= capacity} - {x for x in costs if x+higher <= capacity}
                interval = {x for x in costs if capacity-higher < x <= capacity-lower}
                check(lost == interval, (capacity,lower,higher,lost,interval))


def t_M09_capability_channels():
    # This oracle is a literal independent transition table, including block.
    table = {0:((1,1,1),(2,2,2),(2,0,2)), 1:((1,1,1),(2,2,2),(0,0,2))}
    alphabet = ('silence','request','block')
    depth = 7 if PROFILE == 'full' else 4
    for length in range(depth+1):
        for signals in product(alphabet,repeat=length):
            traces = []
            for mode in (0,1):
                expected = [0]
                for signal in signals:
                    expected.append(table[mode][expected[-1]][alphabet.index(signal)])
                trace = model.mode_trace(mode,signals)
                check(trace == tuple(expected),(mode,signals,trace,expected))
                traces.append(trace)
            exposes = any(state == 2 and signal == 'silence' for state,signal in zip(traces[0],signals))
            check((traces[0] != traces[1]) == exposes, (signals,traces,exposes))
            # Equal-prior two-mode channel: two singleton fibres carry one bit;
            # one two-element fibre carries none. No floating entropy arithmetic.
            fibres = {trace: tuple(i for i,t in enumerate(traces) if t == trace) for trace in traces}
            check(sorted(map(len,fibres.values())) == ([1,1] if exposes else [2]))
    silent = model.mode_trace(1,('silence',)*30)
    check(all(0 in silent[k:k+3] for k in range(29)), 'uniform D=2 for the declared silent automaton')
    check(0 not in model.mode_trace(0,('silence',)*30)[2:], 'mode zero stops returning')


def t_M10_delay_and_floor():
    maximum = 4096 if PROFILE == 'full' else 128
    span = 128 if PROFILE == 'full' else 16
    for count in (1,2,4):
        for delay in range(maximum+1):
            events = model.delayed_events(delay,count)
            if delay <= span:
                # M11 on finite words over events (1) and silence (0): unit debits, budget
                # N = count, admitted = legal with exactly N events. Silence and delayed
                # spending agree on the first `delay` steps; only the second is admitted.
                horizon = delay + 2*count + 1
                silence = (0,) * horizon
                for witness in (events, tuple(delay + 2*i for i in range(count))):
                    word = tuple(1 if t in witness else 0 for t in range(horizon))
                    check(m11_witness(silence,word,delay,count),('M11 witness',delay,count,witness))
                fewer = tuple(1 if t in events[1:] else 0 for t in range(horizon))
                check(not m11_witness(silence,fewer,delay,count),('one event dropped',delay,count))
                if delay:
                    early = tuple(1 if t in (delay-1,) + events[1:] else 0 for t in range(horizon))
                    check(not m11_witness(silence,early,delay,count),('event before the common prefix',delay,count))
            # Constructor coverage: the declared consecutive delayed history.
            expected = tuple(delay+i for i in range(count))
            check(events == expected, (delay,count,events,expected))
            check(len(events) == count and all(t >= delay for t in events))
            check(delay in events, 'same first delay observations as silence; next observation differs')
    for delay in (0, 3, maximum):
        check(model.delayed_events(delay,0) == (), ('no events', delay))
    # Explicit per-step debit against an independent count of prefix sums and events.
    for length in range(9 if PROFILE == 'full' else 7):
        for word in product((0,1),repeat=length):
            for budget in range(4):
                legal = all(sum(word[:k]) <= budget for k in range(length+1))
                check(model.debit_ledger(word,budget) == (legal, word.count(1)),(word,budget))
    # A positive per-event floor bounds the legal events by the budget.
    for floor in (Fraction(1,3), Fraction(1,2), Fraction(1), Fraction(2)):
        for budget in (Fraction(0),Fraction(1),Fraction(3,2),Fraction(5)):
            legal_counts = tuple(n for n in range(20) if model.debit_ledger((floor,)*n,budget)[0])
            check(max(legal_counts) == budget // floor, (floor,budget,legal_counts))
    # Without a floor, debits 2^-k keep a trajectory active at every step within budget 1.
    geometric = tuple(Fraction(1, 2**k) for k in range(1,maximum+1))
    check(model.debit_ledger(geometric,1) == (True,maximum), 'no positive floor')
    check(model.debit_ledger(iter((1,1)),1) == (False,2), 'a one-shot iterator of debits is read once')
    for n in range(1, 33 if PROFILE == 'full' else 9):
        check(model.debit_ledger(geometric[:n],1-Fraction(1,2**n)) == (True,n), ('exact cap',n))
        check(model.debit_ledger(geometric[:n],1-Fraction(1,2**(n-1))) == (False,n), ('last step unaffordable',n))
    # Unbounded delay and the infinite geometric limit are proved in the text; M12's
    # arbitrary admitted set and every-prefix premise are not modelled here: the delayed
    # witness illustrates its conclusion for eternal silence only.


def t_M11_silent_and_driven_bounds():
    upper_n, upper_d = (4,4) if PROFILE == 'full' else (3,2)
    for count in range(upper_n+1):
        for gap in range(upper_d+1):
            horizon = count * (gap+1)
            generated = set()
            for length in range(count+1):
                for increments in product(range(1,gap+2),repeat=length):
                    position, events = -1, []
                    for increment in increments:
                        position += increment
                        events.append(position)
                    generated.add(tuple(events))
            accepted = set()
            for length in range(count+1):
                for events in combinations(range(horizon+2),length):
                    actual = model.silence_bounded(events,gap)
                    check(actual == (events in generated),(count,gap,events,actual))
                    if actual:
                        accepted.add(events)
                        check(all(t < horizon for t in events),(count,gap,events,horizon))
            check(accepted == generated)
            prefixes = {tuple(t in events for t in range(horizon)):events for events in accepted}
            check(len(prefixes) == len(accepted), 'the bounded prefix determines the entire eventually silent history')
            if count:
                check(() in accepted, 'silence-bound allows stopping')
                check(not model.silence_bounded((horizon+1,),gap), 'budget alone permits late events')
                check(not model.silence_bounded(iter((horizon+1,)),gap), 'a one-shot iterator of events is read once')


def t_M12_witness_budget():
    depth = 6 if PROFILE == 'full' else 4
    for length in range(depth+1):
        for sigmas in product((-2,-1,0,1,2),repeat=length):
            for c in (Fraction(1,2),Fraction(1),Fraction(3,2)):
                expected = sum(c*s if s >= 0 else -c*s for s in sigmas)
                actual = model.witness_charge(c,sigmas)
                check(actual == expected,(c,sigmas,actual,expected))
                check(actual >= c*sum(s != 0 for s in sigmas), 'integer witness floor')
    for c,p in product((Fraction(1,3),Fraction(1),Fraction(3,2)),(-2,-1,1,2)):
        for length in range(1,65 if PROFILE == 'full' else 17):
            sigmas = tuple(Fraction(p,2**n) for n in range(length))
            expected = 2*c*abs(p)*(1-Fraction(1,2**length))
            actual = model.witness_charge(c,sigmas)
            check(actual == expected and actual < 2*c*abs(p),(c,p,length,actual,expected))
    check(rejected(lambda: model.witness_charge(0,(1,))))
    # Reordering the same finite absolute charges preserves the total cost.
    for sigmas in ((2,-1,0,1), (Fraction(1,2),-2,Fraction(-1,3))):
        for order in permutations(sigmas):
            check(model.witness_charge(Fraction(3,2),order) == model.witness_charge(Fraction(3,2),sigmas),('reordered charges',order))
    # The payment law of M15 on finite words: event n debits c|sigma_n| from one budget R, in
    # order, against an independently debited balance after every event. Mixed and constant
    # signs; every amplitude here has |sigma| >= s = 1/2, so N paid events give N c s <= R (a).
    amplitudes = (Fraction(-3,2), -1, Fraction(-1,2), Fraction(1,2), 2)
    floor = Fraction(1,2)
    depth = 4 if PROFILE == 'full' else 3
    for c in (Fraction(1,3), Fraction(3,2)):
        for budget in (Fraction(0), Fraction(1,3), Fraction(2), Fraction(9,4)):
            for length in range(depth+1):
                for sigmas in product(amplitudes,repeat=length):
                    balances = stepwise_payment(c,sigmas,budget)
                    paid = len(balances) - 1
                    for k in range(paid+1):
                        check(model.paid_witness_prefix(c,sigmas[:k],budget) == (k,balances[k]),('per-event debit',c,budget,sigmas,k))
                    check(model.paid_witness_prefix(c,sigmas,budget) == (paid,balances[-1]),('paid prefix',c,budget,sigmas))
                    check(paid*c*floor <= budget,('M15(a)',c,budget,sigmas))
    # (c): nonzero integer amplitudes are paid for at most R/c events.
    for c in (Fraction(1,2), Fraction(2)):
        for budget in (Fraction(0), Fraction(3,2), Fraction(5)):
            for sigmas in product((-2,-1,1,2),repeat=4 if PROFILE == 'full' else 3):
                paid, remaining = model.paid_witness_prefix(c,sigmas,budget)
                check(paid*c <= budget and remaining >= 0,('M15(c)',c,budget,sigmas))
    # A held positive floor is refused at the declared finite budget, for alternating,
    # constant negative and constant positive witnesses alike.
    for c, s in product((Fraction(1,3), Fraction(3,2)), (Fraction(1,2), Fraction(2))):
        for budget in (Fraction(0), Fraction(1,3), Fraction(3), Fraction(5)):
            for word in (tuple(s if i % 2 else -s for i in range(40)), (-s,)*40, (s,)*40):
                paid, remaining = model.paid_witness_prefix(c,word,budget)
                check(paid == budget // (c*s) < len(word),('held floor refused',c,s,budget,word[:2]))
                check(remaining == budget - paid*c*s and remaining < c*s,('first unaffordable event',c,s,budget,word[:2]))
    # Exact caps: a budget equal to the first k charges pays them with nothing left,
    # then zero amplitudes, and refuses the next positive charge.
    c = Fraction(3,2)
    for word in ((1,-2,0,1), (Fraction(1,2),Fraction(-1,3),0,Fraction(1,4))):
        for k in range(len(word)+1):
            cap = sum((c*x if x >= 0 else c*-x for x in word[:k]), Fraction(0))
            expected = k
            while expected < len(word) and word[expected] == 0:
                expected += 1
            check(model.paid_witness_prefix(c,word,cap) == (expected,0),('exact cap',word,k))
    check(rejected(lambda: model.paid_witness_prefix(0,(1,),1)))
    check(rejected(lambda: model.paid_witness_prefix(1,(1,),-1)))
    # M15(b) and the infinite series of (d) remain analytic: finite prefixes do not certify them.


def t_M13_frontier_costs():
    depth = 128 if PROFILE == 'full' else 32
    for initial in (Fraction(1,2),Fraction(1),Fraction(3),Fraction(8)):
        for ratio in (Fraction(1,4),Fraction(1,2),Fraction(3,4),Fraction(9,10)):
            remaining, debits = initial, []
            for n in range(depth):
                following = ratio * remaining
                expected = remaining-following
                debit = model.frontier_debit(initial,ratio,n)
                check(debit == expected and debit > 0,(initial,ratio,n,debit,expected))
                debits.append(debit)
                remaining = following
            for c in (Fraction(1,4),Fraction(1),Fraction(2)):
                previous = set(range(depth))
                for magnitude in (Fraction(1,4),Fraction(1,2),Fraction(1),Fraction(2)):
                    paid = {n for n,debit in enumerate(debits) if debit >= c*magnitude}
                    check(paid <= previous and paid == set(range(len(paid))), (c,magnitude,paid))
                    previous = paid
            for threshold in (Fraction(1,4),Fraction(1),Fraction(3)):
                for floor in (Fraction(1,4),Fraction(1),Fraction(2)):
                    domain = (threshold,threshold+1,threshold+3)
                    all_paid = all(model.frontier_debit(f,ratio,0) >= floor for f in domain)
                    check(all_paid == (threshold*(1-ratio) >= floor),(ratio,threshold,floor))
    check(rejected(lambda: model.frontier_debit(Fraction(1),Fraction(1),0)))
    check(rejected(lambda: model.frontier_debit(Fraction(1),Fraction(0),0)))


def t_M14_driven_completion():
    upper_n, upper_d = (4,4) if PROFILE == 'full' else (3,2)
    for count in range(upper_n+1):
        for gap in range(upper_d+1):
            horizon = count*(gap+1)
            expected = set()
            for increments in product(range(1,gap+2),repeat=count):
                position, events = -1, []
                for increment in increments:
                    position += increment
                    events.append(position)
                expected.add(tuple(events))
            observed = set()
            for length in range(count+2):
                for events in combinations(range(horizon+2),length):
                    actual = model.driven_events(events,count,gap)
                    check(actual == (events in expected),(count,gap,events,actual))
                    if actual:
                        observed.add(events)
                        check(len(events) == count and all(t < horizon for t in events))
            check(observed == expected)
    check(not model.driven_events((),1,0), 'an empty future violates the active start obligation')
    check(not model.driven_events((0,),2,0), 'a stopped future violates the active restart obligation')
    check(model.driven_events((0,1),2,0), 'budget exhausted, no further event is required')


def t_B06_boundary_squared():
    vertices = 7 if PROFILE == 'full' else 5
    for size in range(1,vertices+1):
        for simplex in permutations(range(vertices),size):
            boundary = model.simplex_boundary(simplex)
            expected = {}
            if size > 1:
                for omitted in simplex:
                    face = tuple(v for v in simplex if v != omitted)
                    before = simplex.index(omitted)
                    expected[face] = 1 if before % 2 == 0 else -1
            check(boundary == expected,(simplex,boundary,expected))
            twice = {}
            for face,coefficient in boundary.items():
                for subface,sign in model.simplex_boundary(face).items():
                    twice[subface] = twice.get(subface,0) + coefficient*sign
            check(all(value == 0 for value in twice.values()),(simplex,twice))
    check(model.simplex_boundary((0,1)) == {(1,):1,(0,):-1}, 'nonzero boundary, not the trivial zero operator')
    check(rejected(lambda: model.simplex_boundary((0,0))))


def t_B07_selected_and_full_state():
    depth = 3 if PROFILE == 'full' else 2
    paths = tuple(product(range(4),repeat=depth))
    for reading in product((0,1),repeat=4):
        groups = {}
        for path in paths:
            signature = tuple(reading[s] for s in path)
            groups.setdefault(signature,set()).add(path)
        for left in paths:
            own_group = next(group for group in groups.values() if left in group)
            for right in paths:
                same = model.selected_trace_equal(left,right,reading)
                check(same == (right in own_group),(reading,left,right,same))
                if left == right:
                    check(same)
    # Renaming the states, with the reading transformed accordingly, preserves every outcome.
    rename = (2,0,3,1)
    for reading in product((0,1),repeat=4):
        moved = tuple(reading[rename.index(state)] for state in range(4))
        for left in paths:
            for right in paths:
                check(model.selected_trace_equal(tuple(rename[s] for s in left),tuple(rename[s] for s in right),moved)
                      == model.selected_trace_equal(left,right,reading),('renamed states',reading,left,right))
    # Renaming the states while keeping the reading is a different reading and can change it.
    check(model.selected_trace_equal((0,2),(1,3),(0,0,1,1)) and not model.selected_trace_equal((2,3),(0,1),(0,0,1,1)),
          'unrenamed reading')
    # A finite path/readout countermodel on one declared carrier, state = (observed bit,
    # hidden bit): two paths with distinct full states and the same selected trace. It
    # declares no action protocol and is not evidence for N4.
    represented = (0,2,0)
    computation = (0,3,1)
    check(represented != computation and computation[-1] != computation[0])
    check(model.selected_trace_equal(represented,computation,(0,0,1,1)), 'same selected trace despite distinct full states')
    check(not model.selected_trace_equal(represented,computation,(0,1,2,3)), 'an injective reading separates these paths')
    check(not model.selected_trace_equal((0,), (0,0), (0,1,2,3)))


def t_M15_contact_membership():
    worlds = tuple(product((0, 1), repeat=3))  # bond, wire, bias
    fibres = {}
    passive = {}
    for bond, wire, bias in worlds:
        record = model.contact_record(wire, bias)
        expected = (bias, 1 - bias if wire else bias)
        check(record == expected, (bond, wire, bias, record))
        check(model.read_conduction(record) == wire, (wire, record))
        fibres.setdefault(record, set()).add(bond)
        if bond == wire:
            check(model.read_conduction(record) == bond)
            passive.setdefault(record[0], set()).add(bond)
    check(len(fibres) == 4 and all(verdicts == {0, 1} for verdicts in fibres.values()))
    check(passive == {0: {0, 1}, 1: {0, 1}})


def t_M16_interval_extension():
    # Enumerate actual constant sections, independently of the endpoint defect.
    outcomes = set()
    for bond, left, right in product((0, 1), repeat=3):
        sections = [v for v in (0, 1) if (v, v) == (left, right)]
        defect = model.interval_defect(left, right)
        check(defect in (0, 1) and (defect == 0) == bool(sections), (left, right))
        outcomes.add((bond, bool(sections)))
    check(outcomes == set(product((0, 1), (False, True))))


def t_M17_common_family_transport():
    """Proposition M6 on the instance of Mirrors section 8.1, over finite families: one declared family
    of histories realised by two deployments of one operator position."""
    horizon = 4 if PROFILE == 'full' else 3
    iota_x, iota_y = {0: 'x0', 1: 'x1'}, {0: 'y0', 1: 'y1'}
    for length in range(1, horizon + 1):
        words = tuple(product((0, 1), repeat=length))
        # Admission by one obligation on the datum (the number of changes of state), fixed on the position.
        admitted = tuple(w for w in words if sum(a != b for a, b in zip(w, w[1:])) <= 1)
        family = tuple(w for w in words if w[0] == 0)
        common = model.common_family_transport(family, family, iota_x, iota_y, admitted)
        check(all(common[k] for k in ('bijection', 'decoding', 'admission', 'initial_square', 'rooted_lifting')),
              ('every premise of M6 holds with one common family', length, common))
        # Points lying in the images do not replace the common family: an admitted target history
        # outside it, rooted in the image of a source root, has no lift.
        extra = (1,) * length
        widened = model.common_family_transport(family, family + (extra,), iota_x, iota_y, admitted)
        check(not widened['rooted_lifting'] and widened['unlifted'] == (tuple(iota_y[s] for s in extra),),
              ('a target history outside the common family has no lift', length, widened['unlifted']))
        check(not widened['bijection'], ('no bijection without the common family', length))


def t_B08_foucault_readings():
    # Evaluates the declared closed-form law (-sin latitude turns per lap of increasing
    # longitude) and its two readings; this is not a numerical solution of the connection.
    # Closed loops first: at 30 degrees a lap reverses the arrow and returns the axis.
    check(model.foucault_readings(model.foucault_transport(0, Fraction(1, 2), 1)) == (Fraction(1, 2), 0), 'half-turn at 30 degrees')
    # Away from a half-turn the sign is visible: sine 1/3 gives 2/3 of a turn, not 1/3.
    check(model.foucault_readings(model.foucault_transport(0, Fraction(1, 3), 1)) == (Fraction(2, 3), Fraction(1, 6)), 'sine 1/3 lap')
    # Poles are excluded: longitude does not parametrise a loop there.
    latitudes = ((Fraction(-1, 2), 3), (0, 0), (Fraction(1, 3), -2), (Fraction(1, 2), -3))
    for sine, _ in latitudes:
        for laps in range(-2, 3):
            angle = model.foucault_transport(0, sine, laps)
            # Gauss-Bonnet: the enclosed northern cap gives 1 - sin(latitude) turns per lap,
            # equal to the transport law modulo one turn on closed loops, not on open arcs.
            cap = laps * (1 - sine)
            check(model.foucault_readings(angle) == (cap % 1, cap % Fraction(1, 2)), ('closed loop', sine, laps))
            for turns in (-1, 1, 3):
                check(model.foucault_readings(angle + turns) == model.foucault_readings(angle), ('whole turns', sine, laps, turns))
    # Open arcs: unwrapped angle in the local tangent frame, 24 ticks per turn; the signed
    # tick advance below is per quarter-lap.
    for sine, advance in latitudes:
        for start in (0, 1, 7):
            for quarters in range(-8, 9):
                angle = model.foucault_transport(Fraction(start, 24), sine, Fraction(quarters, 4))
                ticks = start + quarters * advance
                check(angle == Fraction(ticks, 24), (sine, start, quarters))
                arrow, axis = model.foucault_readings(angle)
                check((24 * arrow, 24 * axis) == (ticks % 24, ticks % 12))


def t_G10_shear_transport():
    times = range(-4, 5) if PROFILE == 'full' else range(-2, 3)
    for t in times:
        # Images of both basis vectors determine the matrix and its row sums.
        e1, e2 = (model.shear_step(p, t) for p in ((1, 0), (0, 1)))
        check((e1, e2) == ((1, 0), (-t, 1)), t)
        norm = max(abs(a) + abs(b) for a, b in zip(e1, e2))
        check(norm == 1 + abs(t), t)
        for p in ((3, -2), (1, 0), (Fraction(2, 3), Fraction(1, 2))):
            moved = model.shear_step(p, t)
            check(model.shear_step(moved, -t) == p)
            for s in times:
                check(model.shear_step(moved, s) == (p[0] - (s + t) * p[1], p[1]))


def t_G11_fixed_horizon_moments():
    max_horizon = 9 if PROFILE == 'full' else 5
    for start in ((2, 0), (3, -2), (Fraction(2, 3), Fraction(1, 2))):
        x, y = start
        for n in range(max_horizon + 1):
            # Independent oracle: enumerate sign words, use the closed-form endpoint.
            oracle = {}
            for word in product((-1, 1), repeat=n):
                endpoint = (x - sum(word) * y, y)
                oracle[endpoint] = oracle.get(endpoint, 0) + 1
            counts = model.shear_endpoint_counts(start, n)
            check(counts == oracle, (start, n))
            mass = sum(counts.values())
            check(mass == 2 ** n)
            mean = sum(point[0] * weight for point, weight in counts.items()) / Fraction(mass)
            variance = sum((point[0] - mean) ** 2 * weight for point, weight in counts.items()) / Fraction(mass)
            check((mean, variance) == (x, n * y ** 2), (start, n, mean, variance))
            if n > 1 and y:
                # Same fair marginals, one shared sign: the independent-step law fails.
                ends = [model.shear_step(start, sign * n)[0] for sign in (-1, 1)]
                correlated_variance = sum((end - x) ** 2 for end in ends) / Fraction(2)
                check(correlated_variance == n ** 2 * y ** 2 and correlated_variance != variance)


def t_G12_paid_inverse_return():
    for start in ((3, -2), (3, 0)):
        for t, cost, burden in product((-2, 1), (Fraction(1, 3), 2), (0, 1)):
            for steps in range(4):
                cap = burden + steps * cost
                first = model.paid_shear_step(start, burden, t, cost, cap)
                if steps == 0:
                    check(first is None)
                    continue
                check(first == ((start[0] - t * start[1], start[1]), burden + cost))
                returned = model.paid_shear_step(*first, -t, cost, cap)
                if steps == 1:
                    check(returned is None)
                else:
                    check(returned == (start, burden + 2 * cost), (start, t, cost, cap))
    for invalid in (0, -1):
        check(rejected(lambda: model.paid_shear_step((1, 1), 0, 1, invalid, 3)), invalid)


def test_registry():
    return {name:value for name,value in globals().items() if name.startswith('t_') and callable(value)}


def validate_map(mapping, registry):
    if mapping.get('schema') != 1 or not mapping.get('scope'):
        raise ValueError('unknown map schema or missing scope')
    model.dependency_order(mapping['claims'])
    # A declared assumption that no claim requires is a detached prerequisite.
    required = {parent for entry in mapping['claims'] for parent in entry['requires']}
    if any(entry['kind'] == 'assumption' and entry['id'] not in required for entry in mapping['claims']):
        raise ValueError('detached assumption')
    claims = {entry['id'] for entry in mapping['claims']}
    expected = [entry['check'] for entry in mapping['checks']]
    if len(expected) != EXPECTED_TEETH or set(expected) != set(registry) or len(set(expected)) != len(expected):
        raise ValueError('map/check population mismatch')
    # The per-work name sets are the contract every selection is compared with; their
    # members are judged against the selector, so that no list derives from the other.
    declared = mapping.get('work_checks')
    if type(declared) is not dict or sorted(declared) != sorted(WORKS) or any(type(declared[w]) is not list for w in WORKS):
        raise ValueError('per-work name sets must be lists declared for exactly the three works')
    for entry in mapping['checks']:
        if entry['claim'] not in claims or not entry['population']:
            raise ValueError('unknown claim or unnamed population')
    instances = mapping['flow_models']
    if not instances or len({x['id'] for x in instances}) != len(instances):
        raise ValueError('empty or duplicate flow population')
    for instance in instances:
        if not isinstance(instance['id'], str) or not instance['id'] or not instance['relations']:
            raise ValueError('unnamed model or absent relations')
        domains = instance['domains']
        readout = instance['readout']
        if len(set(readout)) != len(readout) or not set(readout) <= domains.keys() or instance['verdict'] not in domains:
            raise ValueError('invalid readout or verdict')
        model.validate(domains, tuple(model.Relation(r['id'], tuple(r['scope']), tuple(tuple(row) for row in r['rows'])) for r in instance['relations']))


def t_G06_map_contract_and_results():
    mapping = json.loads((Path(__file__).parent/'map.json').read_text(encoding='utf-8'))
    validate_map(mapping, test_registry())
    for key, replacement in (('schema', 999), ('checks', []), ('flow_models', []), ('claims', []), ('work_checks', {})):
        broken = copy.deepcopy(mapping)
        broken[key] = replacement
        check(rejected(lambda: validate_map(broken, test_registry())), key)
    broken = copy.deepcopy(mapping)
    broken['checks'][0]['claim'] = 'absent'
    check(rejected(lambda: validate_map(broken, test_registry())), 'unknown source claim')
    broken = copy.deepcopy(mapping)
    broken['flow_models'][0]['readout'] = ['absent']
    check(rejected(lambda: validate_map(broken, test_registry())), 'unknown readout')
    check(rejected(lambda: validate_map(mapping, {})), 'missing implementation')
    # Prerequisites stated only in the source stay declared and attached: removing one, detaching
    # it from its hypothesis or pointing at an absent identifier is refused. An acyclic,
    # well-typed map still does not certify that the extraction from prose is complete.
    stated = [entry['id'] for entry in mapping['claims'] if entry.get('source_only')]
    check(len(stated) >= 4, 'declared source-only prerequisites')
    for key in stated:
        broken = copy.deepcopy(mapping)
        broken['claims'] = [entry for entry in broken['claims'] if entry['id'] != key]
        check(rejected(lambda: validate_map(broken, test_registry())), ('removed prerequisite', key))
        broken = copy.deepcopy(mapping)
        for entry in broken['claims']:
            entry['requires'] = [parent for parent in entry['requires'] if parent != key]
        check(rejected(lambda: validate_map(broken, test_registry())), ('detached prerequisite', key))
        broken = copy.deepcopy(mapping)
        for entry in broken['claims']:
            entry['requires'] = ['absent' if parent == key else parent for parent in entry['requires']]
        check(rejected(lambda: validate_map(broken, test_registry())), ('absent prerequisite', key))
    reordered = copy.deepcopy(mapping)
    reordered['claims'].reverse()
    check(not rejected(lambda: validate_map(reordered, test_registry())), 'reordered claim records')
    # Per-work populations. Before any family runs, only the requested selection is compared with its
    # declared set (run -> checked_selection). Here, in every battery run that includes this family
    # (not under --only), every work selector, the all-work one included, is compared with the exact
    # name set the map declares for that work, never with a second list derived from the selector.
    declared = dict(mapping['work_checks'], all=[entry['check'] for entry in mapping['checks']])
    for work in ('all',) + WORKS:
        selection = selection_or_refusal(mapping, work)
        check(type(selection) is list and sorted(selection) == sorted(declared[work]), ('work selection', work, selection))
        # --only: a declared name alone; a name outside the work is an empty intersection.
        for name in declared['all']:
            single = selection_or_refusal(mapping, work, name)
            expected = [name] if name in declared[work] else 'refused: empty selected population'
            check(single == expected, ('only', work, name, single))
    check(selection_or_refusal(mapping, 'all', 't_absent') == 'refused: unknown requested check', 'unknown check')
    check(rejected(lambda: checked_selection(mapping, 'absent')), 'unknown work')
    # Reordering the declared names or the check records keeps every selected set; a
    # declared name dropped, taken from another work, repeated or unknown is refused. An
    # unknown name takes the path of a foreign one, so it is never the first to fail.
    for records in ('work_checks', 'checks'):
        reordered = copy.deepcopy(mapping)
        for names in (reordered['work_checks'].values() if records == 'work_checks' else (reordered['checks'],)):
            names.reverse()
        for work in WORKS:
            selection = selection_or_refusal(reordered, work)
            check(type(selection) is list and sorted(selection) == sorted(declared[work]), ('reordered', records, work, selection))
    for work in WORKS:
        foreign = next(name for name in declared['all'] if name not in declared[work])
        for corrupt, change in (('dropped', lambda names: names.pop()),
                                ('foreign', lambda names: names.append(foreign)),
                                ('repeated', lambda names: names.append(names[0])),
                                ('unknown', lambda names: names.append('t_absent'))):
            broken = copy.deepcopy(mapping)
            change(broken['work_checks'][work])
            check(rejected(lambda: checked_selection(broken, work)), (corrupt, work))
    # Read actual computed values, not expected verdicts supplied in the map.
    by_id = {row['id']: row for row in evaluate_flow_map(mapping)}
    check(set(by_id) == {'triad-hidden-witness', 'triad-revealed-witness', 'pairwise-without-global-witness'})
    hidden, visible, conflict = (by_id[key] for key in ('triad-hidden-witness','triad-revealed-witness','pairwise-without-global-witness'))
    check(hidden['joint_witness_count'] == visible['joint_witness_count'] == 3)
    check(not hidden['readability_nonvacuous'] and visible['readability_nonvacuous'])
    check(conflict['joint_witness_count'] == 0 and not conflict['readability_nonvacuous'])
    check(conflict['readable_on_joint_population'] is None, 'no raw readability flag on an empty joint population')
    check(conflict['inclusion_minimal_conflicts'] == ((0,1,2),))
    check(all(edge['added_assignments'] == 2 for edge in conflict['edge_influence']))
    reordered = copy.deepcopy(mapping)
    for instance in reordered['flow_models']:
        instance['relations'].reverse()
        for relation in instance['relations']:
            relation['rows'].reverse()
    transformed = {row['id']:row for row in evaluate_flow_map(reordered)}
    for key in by_id:
        check(transformed[key]['assignments'] == by_id[key]['assignments'], key)


def evaluate_flow_map(mapping):
    """Compute the map's joint relation and extensional influence of every edge."""
    results = []
    for instance in mapping['flow_models']:
        domains = {key:tuple(values) for key,values in instance['domains'].items()}
        relations = tuple(model.Relation(r['id'],tuple(r['scope']),tuple(tuple(row) for row in r['rows'])) for r in instance['relations'])
        rows = model.solve(domains,relations)
        if rows != model.enumerate_solutions(domains,relations):
            raise AssertionError('map solver/oracle disagreement: '+instance['id'])
        names = tuple(sorted(domains))
        read_indices = tuple(names.index(k) for k in instance['readout'])
        verdict_index = names.index(instance['verdict'])
        reads = tuple(tuple(row[i] for i in read_indices) for row in rows)
        verdicts = tuple(row[verdict_index] for row in rows)
        # On an empty joint population every decoder is vacuously defined: the raw
        # flag is reported only for a nonempty population, and None marks the vacuous case.
        readable = (model.decoder(reads,verdicts) is not None) if rows else None
        conflict_pair = model.ambiguity_witness(reads,verdicts)
        influence = []
        for i,relation in enumerate(relations):
            removed = model.solve(domains,relations[:i]+relations[i+1:])
            influence.append({'edge':relation.name,'added_assignments':len(set(removed)-set(rows)),
                              'edge_scope':list(relation.scope),
                              'changed_single_variable_projections':[name for j,name in enumerate(names) if {r[j] for r in removed} != {r[j] for r in rows}]})
        results.append({'id':instance['id'],'carrier_order':names,'joint_witness_count':len(rows),
                        'joint_satisfiable':bool(rows),'readable_on_joint_population':readable,
                        'ambiguity_assignments':tuple(rows[i] for i in conflict_pair) if conflict_pair else None,
                        'readability_nonvacuous':bool(rows) and readable,'edge_influence':influence,
                        'inclusion_minimal_conflicts':model.minimal_conflicts(domains,relations) if not rows else (),
                        'assignments':rows})
    return results


def select_checks(mapping, work='all', only=None):
    """Selector: the shared G families and the families lettered for the work, in map order."""
    prefix = {'mirrors':'M','warrior':'W','body':'B'}
    return [entry['check'] for entry in mapping['checks']
            if (work == 'all' or entry['check'][2] in ('G', prefix[work])) and (only is None or entry['check'] == only)]


def declared_checks(mapping, work='all'):
    """The exact name set the map declares for a work; every family for all works."""
    if work == 'all':
        return [entry['check'] for entry in mapping['checks']]
    return list(mapping['work_checks'][work])


def checked_selection(mapping, work='all', only=None):
    """Compare the selector with the declared name set before anything runs.

    --only keeps the single declared name it names. An unknown work or check, an empty
    intersection, and a missing, extra or repeated selected name are refused."""
    if work != 'all' and work not in WORKS:
        raise ValueError('unknown work: ' + str(work))
    if only is not None and only not in declared_checks(mapping):
        raise ValueError('unknown requested check')
    declared = [name for name in declared_checks(mapping, work) if only is None or name == only]
    if not declared:
        raise ValueError('empty selected population')
    selected = select_checks(mapping, work, only)
    if len(selected) != len(declared) or set(selected) != set(declared):
        raise ValueError('WORK_SELECTION_MISMATCH: ' + work + '; missing ' + repr(sorted(set(declared) - set(selected)))
                         + '; extra ' + repr(sorted(set(selected) - set(declared)))
                         + '; selected ' + str(len(selected)) + ' of ' + str(len(declared)) + ' declared')
    return selected


def selection_or_refusal(mapping, work='all', only=None):
    """The checked selection, or the reason it is refused, so that a refusal can be a witness."""
    try:
        return checked_selection(mapping, work, only)
    except ValueError as exc:
        return 'refused: ' + str(exc)


def run(work='all', only=None):
    registry = test_registry()
    mapping = json.loads((Path(__file__).parent/'map.json').read_text(encoding='utf-8'))
    validate_map(mapping, registry)
    selected = checked_selection(mapping, work, only)
    rows = []
    global OBSERVATIONS
    for name in selected:
        OBSERVATIONS = 0
        row = {'name':name,'status':'PASS'}
        try:
            registry[name]()
            if OBSERVATIONS == 0:
                raise ValueError('no observed obligations')
        except AssertionError as exc:
            row.update(status='FAIL',counterexample=str(exc))
        except Exception as exc:
            row.update(status='ERROR',error=type(exc).__name__+': '+str(exc))
        row['observations'] = OBSERVATIONS
        rows.append(row)
    return {'profile':PROFILE,'work':work,'rows':rows,'status':'PASS' if all(r['status']=='PASS' for r in rows) else 'FAIL',
            'relationship_map':evaluate_flow_map(mapping) if all(r['status']=='PASS' for r in rows) else None,
            'open_hypotheses':[n['id'] for n in mapping['claims'] if n['kind']=='hypothesis'],
            'scope':'Declared finite families only; no empirical or universal completeness certificate'}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--teeth', action='store_true', help='run the declared battery (default action)')
    parser.add_argument('--profile',choices=('quick','full'),default='quick')
    parser.add_argument('--work',choices=('all',)+WORKS,default='all')
    parser.add_argument('--only')
    parser.add_argument('--json',default='result.json')
    args = parser.parse_args()
    global PROFILE
    PROFILE = args.profile
    try:
        result = run(args.work,args.only)
    except Exception as exc:
        result = {'status':'ERROR','error':type(exc).__name__+': '+str(exc),'rows':[]}
    result['sources'] = {name:hashlib.sha256((Path(__file__).parent/name).read_bytes()).hexdigest() for name in ('relations.py','suite.py','map.json')}
    Path(args.json).write_text(json.dumps(result,ensure_ascii=False,indent=2,sort_keys=True)+'\n',encoding='utf-8')
    for row in result['rows']:
        if row['status']!='PASS':
            print(row['status']+' '+row['name']+': '+row.get('counterexample',row.get('error','')))
    passed = sum(row['status']=='PASS' for row in result['rows'])
    print('teeth: '+str(passed)+'/'+str(len(result['rows']))+'; '+result['status']+'; '+args.profile)
    if result.get('error'):
        print(result['error'])
    return 0 if result['status']=='PASS' else 1


if __name__=='__main__':
    sys.exit(main())
