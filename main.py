#!/usr/bin/env python3
import numpy as np
from collections import namedtuple
from z3 import *
import z3

Req = namedtuple('Req', ('v', 'e', 'n'))
Endpoint = namedtuple('Endpoint', ('L_D', 'K', 'latencies'))


def read_line_ints(line):
    return [int(x) for x in line.split(' ')]


def read_endpoint(f):
    L_D, K = read_line_ints(next(f))  # latency to data server, number of cache servers
    latencies = {int(c): int(L_c) for c, L_c in (next(f).split(' ') for _ in range(K))}
    return Endpoint(L_D, K, latencies)


def read_file(filename):
    with open(filename) as f:
        V, E, R, C, X = [int(x) for x in next(f).split(' ')]
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

has_video = [[Bool('has_video_{}_{}'.format(i, j)) for j in range(C)]
             for i in range(V)]


class Constraints:
    CAPACITY = [Sum([If(has_video[i][j], S[i], 0) for i in range(V)]) <= X
                for j in range(C)]

    # def min_r(r):
    #     m = 0
    #     for j in range(C):
    #         If(endpoints[has_video[r.v][j], r) for j in range(C))

    SERVE = Sum([min_r(r) for r in requests])


def solve(constraints):
    s = Solver()
    s.add(constraints)
    s.check()
    return s.model()




print(solve(Constraints.CAPACITY))


exit()

R, C, L, H, rows = read_file('example.in')

TOTAL_SLICES_SIZE = Int('TOTAL_SLICES_SIZE')


def make_2darr(name, f):
    ARR = Function(name, z3.IntSort(), z3.IntSort(), IntSort())
    INIT = [ARR(r, c) == f(r, c) for r in range(R) for c in range(C)]
    INIT += [ARR(r, -1) == 0 for r in range(-1, R)]
    INIT += [ARR(-1, c) == 0 for c in range(-1, C)]

    def call(s):
        sr, sc = s.src.r, s.src.c
        dr, dc = s.dst.r, s.dst.c
        return ARR(dr, dc) - ARR(dr, sc - 1) - ARR(sr - 1, dc) + ARR(sr - 1, sc - 1)
    return ARR, INIT, call


total_mushrooms = np.cumsum(np.cumsum(rows, axis=0), axis=1)
TOTAL, INIT_TOTAL, count_mushrooms = make_2darr('TOTAL', lambda r, c: int(total_mushrooms[r, c]))
SIZES, INIT_SIZES, slice_size = make_2darr('SIZES', lambda r, c: (r + 1) * (c + 1))


def VAR_SLICE_SIZE(i):
    return Int('Slice{}.SIZE'.format(i))


def VAR_MUSH_COUNT(i):
    return Int('Slice{}.MUSH_COUNT'.format(i))


def slice_constraints(s):
    SLICE_SIZE = VAR_SLICE_SIZE(s.i)
    MUSH_COUNT = VAR_MUSH_COUNT(s.i)
    return And(  # slices are in bounds
                s.src.r >= 0, s.src.c >= 0, s.dst.r < R, s.dst.c < C,
                # slices are correctly shaped
                s.src.r <= s.dst.r, s.src.c <= s.dst.c,
                SLICE_SIZE == slice_size(s),
                MUSH_COUNT == count_mushrooms(s),
                L <= MUSH_COUNT,
                L <= SLICE_SIZE - MUSH_COUNT,
                # and at most H cells of any kind in total:
                SLICE_SIZE <= H)


def cons_nonoverlap(s1, s2):
    # The slices being cut out cannot overlap
    return Or(s1.dst.r < s2.src.r, s1.dst.c < s2.src.c)


def create_slices(num):
    slices = [SL(src=Point(c=Int("Slice{}.src.c".format(i)),
                           r=Int("Slice{}.src.r".format(i))),
                 dst=Point(c=Int("Slice{}.dst.c".format(i)),
                           r=Int("Slice{}.dst.r".format(i))),
                 i=i)
              for i in range(num)]
    constraints = [slice_constraints(s) for s in slices]
    constraints += [cons_nonoverlap(s1, s2) for s1 in slices for s2 in slices if s1.i < s2.i]
    constraints += [TOTAL_SLICES_SIZE == Sum([VAR_SLICE_SIZE(s.i) for s in slices]),
                    TOTAL_SLICES_SIZE <= R * C]  # so we stop when we've found an obviously optimal solution
    return slices, constraints


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
