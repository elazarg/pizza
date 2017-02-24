#!/usr/bin/env python3
from collections import namedtuple, defaultdict, Counter
from itertools import islice
import z3

Req = namedtuple('Req', ('v', 'e', 'n'))
Endpoint = namedtuple('Endpoint', ('L_D', 'K', 'L'))

BASENAME = 'trending_today'
FILENAME = BASENAME + '.in'
RES = {'me_at_the_zoo.in': 0,
       'videos_worth_spreading.in': 0,
       'kittens.in': 0,
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
    print('requests before:', len(requests))
    requests = Counter(dict(requests.most_common(1000)))
    print('requests after:', len(requests))
    return (V, E, R, C, X), S, endpoints, requests


def make_dict(m):
    d = defaultdict(list)
    for j in range(C):
        for i in relevant[j]:
            if m.evaluate(has_video(i, j)):
                d[j].append(i)
    return d


def write_file(d, result):
    with open("{}/{}.txt".format(BASENAME, result), "w") as out:
        out.write(str(len(d)))
        out.write('\n')
        for k in d:
            out.write("{} {}".format(str(k), " ".join(map(str, d[k]))))
            out.write('\n')

print('Reading file...', end=' ')
(V, E, R, C, X), S, endpoints, requests = read_file(FILENAME)
print('done.')

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

print('Generate constraints...')

has_video = z3.Function('has_video', z3.IntSort(), z3.IntSort(), z3.BoolSort())

SERVE = z3.Int('SERVE')
CAPVAR = [z3.Int('CAP_{}'.format(j)) for j in range(C)]

print('SERVE_SUM')
SERVE_SUM = SERVE == z3.Sum([find_max([z3.If(has_video(v, j), endpoints[e].L_D-endpoints[e].L[j], 0)
                                       for j in endpoints[e].L]
                                      )*n
                             for (v, e), n in requests.items()])

print('CAPVAR_SUM')
CAPVAR_SUM = [CAPVAR[j] == z3.Sum([z3.If(has_video(i, j), S[i], 0) for i in relevant[j]]) for j in range(C)]
print('CAPACITY')
CAPACITY = [CAPVAR[j] <= X for j in range(C)]
print('CAP_FULL')
CAP_FULL = [z3.Or(has_video(i, j), CAPVAR[j] > X - S[i]) for j in range(C) for i in relevant[j]]


def prepare_solver():
    s = z3.Solver()
    s.add(CAPVAR_SUM)
    s.add(CAPACITY)
    s.add(CAP_FULL)
    s.add(SERVE_SUM)
    return s


def maximize(s):
    s.maximize(SERVE)
    s.check()
    return s.model()


def solve(s, bound=0):
    s.add(SERVE > bound)
    s.check()
    try:
        return s.model()
    except e:
        return None


result = RES[FILENAME]
print('preparing...')
s = prepare_solver()


while True:
    target = int(result*1.1)
    print('solving round for {}...'.format(target))
    m = solve(s, target)

    if not m:
        print('UNSAT')
        break
    else:
        result = int(str(m.evaluate(SERVE)))
        print('found {}...'.format(result))
        d = make_dict(m)
        write_file(d, result)
