#!/usr/bin/env python3
import numpy as np
from collections import namedtuple, defaultdict
from itertools import islice
import z3

Req = namedtuple('Req', ('v', 'e', 'n'))
Endpoint = namedtuple('Endpoint', ('L_D', 'K', 'L'))

FILENAME = 'me_at_the_zoo.in'
RES = {'me_at_the_zoo.in': 23149946,
       'videos_worth_spreading.in': 0}


def read_line_ints(line):
    return [int(x) for x in line.strip().split()]


def read_endpoint(f):
    L_D, K = read_line_ints(next(f))  # latency to data server, number of cache servers
    latencies = {c: L_c for c, L_c in (read_line_ints(next(f)) for _ in range(K))}
    return Endpoint(L_D, K, latencies)


def read_file(filename):
    with open(filename) as f:
        V, E, R, C, X = read_line_ints(next(f))
        S = read_line_ints(next(f))  # The size of each video in MB
        assert len(S) == V
        endpoints = [read_endpoint(f) for i in range(E)]
        requests = [Req(*read_line_ints(next(f))) for _ in range(R)]
    return (V, E, R, C, X), S, endpoints, requests

(V, E, R, C, X), S, endpoints, requests = read_file(FILENAME)
# print((V, E, R, C, X))
# print(S)
# print(endpoints)
# print(requests)

has_video = [[z3.Bool('has_video_{}_{}'.format(i, j)) for j in range(C)]
             for i in range(V)]


def find_max(xs):
    m = 0
    for x in xs:
        m = z3.If(m > x, m, x)
    return m


def request_key(r):
    return S[r.v] / r.n
NUMREQ = 100


def L(r):
    return find_max([z3.If(has_video[r.v][j], endpoints[r.e].L_D-endpoints[r.e].L[j], 0)
                    for j in range(C) if j in endpoints[r.e].L])

SERVE = z3.Int('SERVE')
SERVE_SUM = SERVE == z3.Sum([L(r)*r.n for r in islice(sorted(requests, key=request_key), NUMREQ)])
BIG_SERVE = SERVE > RES[FILENAME]

CAPACITY = [z3.Sum([z3.If(has_video[i][j], S[i], 0) for i in range(V)]) <= X
            for j in range(C)]


def solve(maximize=False, bound=True):
    s = z3.Optimize()
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
    with open("{}.{}.txt".format(FILENAME, m.evaluate(SERVE)), "w") as out:
        for i in range(V):
            for j in range(C):
                if m.evaluate(z3.Bool('has_video_{}_{}'.format(i, j))):
                    d[j].append(i)
        out.write(str(len(d)))
        for k in d:
            print("{} {}".format(str(k), " ".join(map(str, d[k]))), file=out)
            out.write("{} {}".format(str(k), " ".join(map(str, d[k]))))

