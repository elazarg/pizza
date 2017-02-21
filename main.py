#!/usr/bin/env python3
import numpy as np
from collections import namedtuple
from z3 import *
import z3


def read_file(filename):
    with open(filename) as f:
        txt = [line.rstrip('\n') for line in f]
    R, C, L, H = [int(x) for x in txt[0].split(' ')]
    rows = [[int(c == 'M') for c in row]
            for row in txt[1:]]
    assert len(rows) == R
    assert all(len(row) == C for row in rows)
    assert 0 <= L <= H
    return R, C, L, H, rows


R, C, L, H, rows = read_file('small.in')

total_mushrooms = np.cumsum(np.cumsum(rows, axis=0), axis=1)
TOTAL_SLICES_SIZE = Int('TOTAL_SLICES_SIZE')
TOTAL = Function('TOTAL',  z3.IntSort(), z3.IntSort(), IntSort())
INIT = [TOTAL(r, c) == int(total_mushrooms[r, c])
        for r in range(R)
        for c in range(C)]
INIT += [TOTAL(r, -1) == 0 for r in range(-1, R)]
INIT += [TOTAL(-1, c) == 0 for c in range(-1, C)]

SIZES = Function('SIZES', z3.IntSort(), z3.IntSort(), IntSort())
INIT += [SIZES(r, c) == (r+1)*(c+1)
         for r in range(R)
         for c in range(C)]
INIT += [SIZES(r, -1) == 0 for r in range(-1, R)]
INIT += [SIZES(-1, c) == 0 for c in range(-1, C)]

Point = namedtuple('Point', ('c', 'r', ))
SL = namedtuple('SL', ('src', 'dst', 'i', ))


def slice_size(s):
    sr, sc = s.src.r, s.src.c
    dr, dc = s.dst.r, s.dst.c
    return SIZES(dr, dc) - SIZES(dr, sc-1) - SIZES(sr-1, dc) + SIZES(sr-1, sc-1)


# def slice_size(s):
#     return (s.dst.r - s.src.r + 1) * (s.dst.c - s.src.c + 1)


def count_mushrooms(s):
    sr, sc = s.src.r, s.src.c
    dr, dc = s.dst.r, s.dst.c
    return TOTAL(dr, dc) - TOTAL(dr, sc-1) - TOTAL(sr-1, dc) + TOTAL(sr-1, sc-1)


def VAR_SLICE_SIZE(i):
    return Int('Slice{}.SIZE'.format(i))


def slice_constraints(s):
    SLICE_SIZE = VAR_SLICE_SIZE(s.i)
    MUSH_COUNT = Int('Slice{}.MUSH_COUNT'.format(s.i))
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
    constraints += [TOTAL_SLICES_SIZE == Sum([VAR_SLICE_SIZE(s.i) for s in slices])]
    return slices, constraints


def optimize(constraints, maximize=True):
    s = Optimize()
    s.add(INIT)
    s.add(constraints)
    # print(s.sexpr())
    if maximize:
        s.maximize(TOTAL_SLICES_SIZE)
    s.check()
    return s.model()


def main():
    print(R, C, L, H)
    print(np.array(rows))

    SLICES = 9

    slices, constraints = create_slices(SLICES)
    m = optimize(constraints)

    # print(total_mushrooms)
    if not m:
        print('UNSAT')
        return
    for i in range(SLICES):
        print("Slice: ({}, {}) x ({}, {}) => MUSH_COUNT = {}, SIZE = {}".format(
            m.evaluate(slices[i].src.c),
            m.evaluate(slices[i].src.r),
            m.evaluate(slices[i].dst.c),
            m.evaluate(slices[i].dst.r),
            m.evaluate(Int("Slice{}.MUSH_COUNT".format(i))),
            m.evaluate(VAR_SLICE_SIZE(i)))
        )
    print('TOTAL =', m.evaluate(TOTAL_SLICES_SIZE))

main()
