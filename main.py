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
print(R, C, L, H)
print(np.array(rows))


def ind(r, c):
    return r*C + c

total_mushrooms = np.cumsum(np.cumsum(rows, axis=0), axis=1)
TOTAL = Array('TOTAL', z3.IntSort(), z3.IntSort())
INIT = And(*[TOTAL[ind(r, c)] == int(total_mushrooms[r, c])
            for r in range(R)
            for c in range(C)])


print(total_mushrooms)
# exit()


Point = namedtuple('Point', ('c', 'r', ))
SL = namedtuple('SL', ('src', 'dst', 'i', ))


def slice_size(s):
    return (s.dst.r - s.src.r + 1) * (s.dst.c - s.src.c + 1)

def zc(r, c):
    return If(Or(r < 0, c < 0), 0, TOTAL[ind(r, c)])

def Stoma(s):
    return zc(s.dst.r, s.dst.c) - zc(s.dst.r, s.src.c - 1) - zc(s.src.r - 1, s.dst.c) + zc(s.src.r - 1, s.src.c - 1)

def Smush(s, Stoma, slice_size):
    return slice_size - Stoma

def slice_constraints(s):
    s_size = Int('Slice{}.size'.format(s.i))
    s_Stoma = Int('Slice{}.Stoma'.format(s.i))
    return And(  # slices are in bounds
               s.src.r >= 0, s.src.c >= 0, s.dst.r < R, s.dst.c < C,
               # slices are correctly shaped
               s.src.r <= s.dst.r, s.src.c <= s.dst.c,
               s_size == slice_size(s),
               s_Stoma == Stoma(s),
               L <= Smush(s, s_Stoma, s_size),
               L <= Stoma(s),
               # and at most H cells of any kind in total:
               s_size <= H)


def cons_nonoverlap(s1, s2):
    # The slices being cut out cannot overlap
    return Or(s1.dst.r < s2.src.r, s1.dst.r < s2.src.r,
              s1.dst.c < s2.src.c, s1.dst.c < s2.src.c)


def create_slices(num):
    slices = [SL(src = Point(c = Int("Slice{}.src.c".format(i)),
                             r = Int("Slice{}.src.r".format(i))),
                 dst = Point(c = Int("Slice{}.dst.c".format(i)),
                             r = Int("Slice{}.dst.r".format(i))),
                 i = i)
              for i in range(num)]
    return slices, [ slice_constraints(s) for s in slices ] + [ cons_nonoverlap(s1, s2) for s1 in slices for s2 in slices if id(s1) != id(s2) ]

SLICES = 3

s = Solver()
s.add(INIT)
slices, constraints = create_slices(SLICES)
s.add(*constraints)

print(s.check())

m = s.model()

for i in range(SLICES):
    print("Slice: ({}, {}) x ({}, {}) => Stoma = {}, Ssize = {}".format(
        m.evaluate(slices[i].src.c),
        m.evaluate(slices[i].src.r),
        m.evaluate(slices[i].dst.c),
        m.evaluate(slices[i].dst.r),
        m.evaluate(Int("Slice{}.Stoma".format(i))),
        m.evaluate(Int("Slice{}.size".format(i)))))
