#!/usr/bin/env python3
from collections import namedtuple, defaultdict
from itertools import islice
import z3

Req = namedtuple('Req', ('v', 'e', 'n'))
Endpoint = namedtuple('Endpoint', ('L_D', 'K', 'L'))

FILENAME = 'me_at_the_zoo.in'
RES = {'me_at_the_zoo.in': 100,
       'videos_worth_spreading.in': 100000,
       'trending_today.in': 150000000}


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
    endpoints = [read_endpoint(f) for i in range(E)]
    from collections import Counter
    c = Counter()
    for line in txt[1 + 1 + sum(e.K + 1 for e in endpoints):]:
        v, e, n = read_line_ints(line)
        c[(v, e)] += n
    requests = [Req(v, e, n) for (v, e), n in c.items()]
    return (V, E, R, C, X), S, endpoints, requests

(V, E, R, C, X), S, endpoints, requests = read_file(FILENAME)


def find_max(xs):
    m = 0
    for x in xs:
        m = z3.If(m > x, m, x)
    return m


def request_key(r):
    return S[r.v] / r.n
NUMREQ = 100


def L(r):
    return find_max([z3.If(has_video(r.v, j), endpoints[r.e].L_D-endpoints[r.e].L[j], 0)
                    for j in endpoints[r.e].L])

print('GENERATE CONSTRAINTS')

print('has_video')
has_video = z3.Function('has_video', z3.IntSort(), z3.IntSort(), z3.BoolSort())
SERVE = z3.Int('SERVE')
print('SERVE_SUM')
SERVE_SUM = SERVE == z3.Sum([L(r)*r.n for r in requests])  # islice(sorted(requests, key=request_key), NUMREQ)])
BIG_SERVE = SERVE > RES[FILENAME]

print('CAPACITY')


i = z3.Int('i')
j = z3.Int('j')

CAPACITY = z3.ForAll([j], z3.Sum([z3.If(z3.And(j < C, j >= 0, has_video(i, j)), S[i], 0) for i in range(V)]) <= X)


def solve(maximize=False, bound=True):
    s = z3.Solver()
    s.add(CAPACITY)
    s.add(SERVE_SUM)
    if maximize:
        s.maximize(SERVE)
    if bound:
        s.add(BIG_SERVE)
    s.check()
    return s.model()

print('solving...')
m = solve(False, True)

if not m:
    print('UNSAT')
else:
    d = defaultdict(list)
    for i in range(V):
        for j in range(C):
            if m.evaluate(has_video(i, j)):
                d[j].append(i)
    result = m.evaluate(SERVE)
    with open("{}.{}.txt".format(FILENAME, result), "w") as out:
        print(len(d), file=out)
        for k in d:
            print(k, *d[k], file=out, sep=' ')
