#!/usr/bin/env python3
from collections import namedtuple, defaultdict, Counter
from itertools import islice
import z3

Req = namedtuple('Req', ('v', 'e', 'n'))
Endpoint = namedtuple('Endpoint', ('L_D', 'K', 'L'))

FILENAME = 'me_at_the_zoo.in'
RES = {'me_at_the_zoo.in': 25090000,  # 25096812,
       'videos_worth_spreading.in': 100000,
       'trending_today.in': 100000}


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
    requests = Counter()
    for line in txt[1 + 1 + sum(e.K + 1 for e in endpoints):]:
        v, e, n = read_line_ints(line)
        requests[(v, e)] += n
    return (V, E, R, C, X), S, endpoints, requests

(V, E, R, C, X), S, endpoints, requests = read_file(FILENAME)

relevant = defaultdict(set)
for (v, e) in requests:
    for c in endpoints[e].L:
        relevant[c].add(v)

print((V, E, R, C, X))
print(S)
print(endpoints)
print(requests)
print(relevant)


def find_max(xs):
    m = 0
    for x in xs:
        m = z3.If(m > x, m, x)
    return m


def request_key(r):
    return S[r.v] / r.n
NUMREQ = 100

print('GENERATE CONSTRAINTS')

has_video = z3.Function('has_video', z3.IntSort(), z3.IntSort(), z3.BoolSort())

SERVE = z3.Int('SERVE')
CAPVAR = [z3.Int('CAP_{}'.format(j)) for j in range(C)]

SERVE_SUM = SERVE == z3.Sum([find_max([z3.If(has_video(v, j), endpoints[e].L_D-endpoints[e].L[j], 0)
                                       for j in endpoints[e].L]
                                      )*n
                             for (v, e), n in requests.items()])  # islice(sorted(requests, key=request_key), NUMREQ)])
BIG_SERVE = SERVE > RES[FILENAME]


CAPVAR_SUM = [CAPVAR[j] == z3.Sum([z3.If(has_video(i, j), S[i], 0) for i in relevant[j]]) for j in range(C)]
CAPACITY = [CAPVAR[j] <= X for j in range(C)]
CAP_FULL = [z3.Or(has_video(i, j), CAPVAR[j] > X - S[i]) for j in range(C) for i in relevant[j]]


def solve(maximize=False, bound=True):
    s = z3.Solver()
    s.add(CAPVAR_SUM)
    s.add(CAPACITY)
    s.add(CAP_FULL)
    s.add(SERVE_SUM)
    if maximize:
        s.maximize(SERVE)
    if bound:
        s.add(BIG_SERVE)
    # sprint(s.sexpr())
    s.check()
    return s.model()

print('solving...')
m = solve(False, True)

if not m:
    print('UNSAT')
else:
    d = defaultdict(list)
    with open("{}.{}.txt".format(FILENAME, m.evaluate(SERVE)), "w") as out:
        for j in range(C):
            for i in relevant[j]:
                if m.evaluate(has_video(i, j)):
                    d[j].append(i)
        out.write(str(len(d)))
        out.write('\n')
        for k in d:
            out.write("{} {}".format(str(k), " ".join(map(str, d[k]))))
            out.write('\n')
