#!/usr/bin/env python3
import numpy as np
from collections import namedtuple
import z3

Req = namedtuple('Req', ('v', 'e', 'n'))
Endpoint = namedtuple('Endpoint', ('L_D', 'K', 'L'))


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

(V, E, R, C, X), S, endpoints, requests = read_file('me_at_the_zoo.in')
print((V, E, R, C, X))
print(S)
print(endpoints)
print(requests)

has_video = [[z3.Bool('has_video_{}_{}'.format(i, j)) for j in range(C)]
             for i in range(V)]


def find_max(xs):
    m = xs[0]
    for x in xs:
        m = z3.If(m > x, m, x)
    return m


def L(r):
    return find_max([z3.If(has_video[r.v][j], endpoints[r.e].L_D-endpoints[r.e].L[j], 0)
                    for j in range(C) if j in endpoints[r.e].L])


SERVE = z3.Int('SERVE')
SERVE_SUM = SERVE == z3.Sum([L(r)*r.n for r in requests])
BIG_SERVE = SERVE > 20615576

CAPACITY = [z3.Sum([z3.If(has_video[i][j], S[i], 0) for i in range(V)]) <= X
            for j in range(C)]


def solve(maximize=True, bound=0):
    s = z3.Optimize()
    s.add(CAPACITY)
    s.add(SERVE_SUM)
    if maximize:
        s.maximize(SERVE)
    if bound:
        s.add(SERVE > 20615576)
    s.check()
    return s.model()

m = solve()

if not m:
    print('UNSAT')
else:
    print('SERVE', m.evaluate(SERVE))

exit()


def optimize(constraints, maximize=True):
    s = Optimize()
    s.add(INIT_TOTAL)
    s.add(INIT_SIZES)
    s.add(constraints)
    # print(s.sexpr())
    if maximize:
        s.maximize(TOTAL_SLICES_SIZE)
    s.check()
    return s.model()


def main():
    print(R, C, L, H)
    print(np.array(rows))

    SLICES = 3

    slices, constraints = create_slices(SLICES)
    m = optimize(constraints)

    # print(total_mushrooms)
    if not m:
        print('UNSAT')
        return
    for i in range(SLICES):
        sc = m.evaluate(slices[i].src.c)
        sr = m.evaluate(slices[i].src.r)
        dc = m.evaluate(slices[i].dst.c)
        dr = m.evaluate(slices[i].dst.r)
        size = m.evaluate(VAR_SLICE_SIZE(i))
        mushes = m.evaluate(VAR_MUSH_COUNT(i))
        assert str(m.evaluate((dc - sc + 1) * (dr - sr + 1))) == str(size), '{} != {}'.format((dc - sc + 1) * (dr - sr + 1), size)
        print("Slice: ({}, {}) x ({}, {}) => MUSH_COUNT = {}, SIZE = {}".format(
            sc, sr, dc, dr, mushes, size)
        )
    print('TOTAL =', m.evaluate(TOTAL_SLICES_SIZE))

main()
