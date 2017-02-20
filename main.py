import numpy as np
from typing import NamedTuple
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
TOTAL = Array('TOTAL', IntSort, IntSort)
INIT = And(TOTAL[ind(r, c)] == total_mushrooms[r, c]
           for r in range(R)
           for c in range(C))


print(total_mushrooms)
exit()


class Point(NamedTuple):
    c: Int
    r: Int


class SL(NamedTuple):
    """A slice of pizza is a rectangular section of the pizza
    delimited by two rows and two columns, without holes."""
    src: Point
    dst: Point


def slice_size(s):
    return (s.dst.r - s.src.r) * (s.dst.c - s.src.c)

MUSH = Int('MUSH')
SIZE = Int('SIZE')

# TODO: accumulate sums for each point


def countmush_in_slice(s):
    return Sum(If(And(s.src.row <= Int(row), Int(row) < s.dst.row,
                      s.src.col <= Int(col), Int(col) < s.dst.col),
                  Int(rows[row][col]), Int(0))
               for row in range(R)
               for col in range(C))


def cons_per_slice(s):
    return And(  # slices are in bounds
               s.src.r >= 0, s.src.c >= 0, s.dst.r < R, s.dst.c < C,
               # The slices we want to cut out must contain at least L cells of each ingredient:
               MUSH == countmush_in_slice(s),
               MUSH >= L,  # at least L mushrooms
               SIZE == slice_size(s),
               SIZE - MUSH >= L,  # at least L tomatoes
               # and at most H cells of any kind in total:
               SIZE < H)


def cons_nonoverlap(s1, s2):
    # The slices being cut out cannot overlap
    return Or(s1.dst.r <= s2.src.r, s1.to.r <= s2.src.r,
              s1.dst.c <= s2.src.c, s1.to.c <= s2.src.c)


def total():
    return Sum(If(And(s.src.row <= Int(row), Int(row) < s.dst.row,
                      s.src.col <= Int(col), Int(col) < s.dst.col),
                  Int(rows[row][col]), Int(0))
               for row in range(R)
               for col in range(C))
x = z3.Int('x')
y = z3.Int('y')
z3.solve(x > 2, y < 10, x + 2*y == 7)
