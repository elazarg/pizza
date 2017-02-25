#!/usr/bin/env python3
from collections import namedtuple, defaultdict, Counter
import z3

Endpoint = namedtuple('Endpoint', ('L_D', 'K', 'L'))


def read_line_ints(line):
    return [int(x) for x in line.strip().split()]


def read_endpoint(f):
    L_D, K = read_line_ints(next(f))  # latency to data server, number of cache servers
    latencies = {c: L_c for c, L_c in (read_line_ints(next(f)) for _ in range(K))}
    return Endpoint(L_D, K, latencies)


def read_file(filename):
    with open(filename) as f:
        txt = f.readlines()
    f = iter(txt)
    V, E, R, C, X = read_line_ints(next(f))
    S = read_line_ints(next(f))  # The size of each video in MB
    assert len(S) == V
    endpoints = [read_endpoint(f) for _ in range(E)]
    requests = Counter()
    for line in txt[1 + 1 + sum(e.K + 1 for e in endpoints):]:
        v, e, n = read_line_ints(line)
        requests[(v, e)] += n
    relevant = defaultdict(set)
    for (v, e) in requests:
        for c, l in endpoints[e].L.items():
            relevant[c].add(v)

    return C, X, S, endpoints, requests, relevant


def make_dict(m, C, relevant):
    return {j: [i for i in relevant[j] if m.evaluate(has_video(i, j))]
            for j in range(C)}


def write_file(filename, d):
    with open(filename, "w") as out:
        print(len(d), file=out)
        for k in d:
            print(k, *d[k], file=out)


def find_max(xs):
    m = 0
    for x in xs:
        m = z3.If(m > x, m, x)
    return m

has_video = z3.Function('has_video', z3.IntSort(), z3.IntSort(), z3.BoolSort())
SERVE = z3.Int('SERVE')


def generate_constraints(C, X, S, endpoints, requests, relevant):
    print('Generate constraints...')

    print('SERVE_SUM')
    CAPVAR = [z3.Int('CAP_{}'.format(j)) for j in range(C)]
    SERVE_SUM = SERVE == z3.Sum([find_max([z3.If(has_video(v, j), endpoints[e].L_D-endpoints[e].L[j], 0)
                                           for j in endpoints[e].L]
                                          )*n
                                 for (v, e), n in requests.items()])

    print('CAPVAR_SUM')
    CAPVAR_SUM = [CAPVAR[j] == z3.Sum([z3.If(has_video(i, j), S[i], 0) for i in relevant[j]]) for j in range(C)]
    print('CAPACITY')
    CAPACITY = [CAPVAR[j] <= X for j in range(C)]
    print('CAP_FULL')
    CAP_FULL = [z3.Or(has_video(i, j), CAPVAR[j] > X - S[i])
                for j in range(C) for i in relevant[j]]

    return [CAPVAR_SUM, CAPACITY, CAP_FULL, SERVE_SUM]


def iterative(basename, maximize=False):
    C, X, S, endpoints, requests, relevant = read_file(basename + '.in')
    result = 25124934
    print('preparing...')
    constraints = generate_constraints(C, X, S, endpoints, requests, relevant)
    s = z3.Optimize() if maximize else z3.Solver()
    for c in constraints:
        s.add(c)
    if maximize:
        s.maximize(SERVE)
    while True:
        target = int(result)
        print('solving round for', target)
        s.add(SERVE > target)
        s.check()
        try:
            m = s.model()
        except z3.Z3Exception:
            print('UNSAT')
            break
        result = int(str(m.evaluate(SERVE)))
        print('found', result)
        d = make_dict(m, C, relevant)
        write_file("{}/{}.txt".format(basename, result), d)
        if maximize:
            break


iterative('me_at_the_zoo')
iterative('trending_today')
