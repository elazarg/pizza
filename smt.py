#!/usr/bin/env python3
import z3
import readfile as io


def find_max(xs, v, ld):
    m = 0
    for c, latency in xs:
        m = z3.If(z3.And(has_video(v, c), m < ld - latency), ld - latency, m)
    return m

has_video = z3.Function('has_video', z3.IntSort(), z3.IntSort(), z3.BoolSort())
SERVE = z3.Int('SERVE')


def generate_constraints(capacity, sizes, endpoints, caches):
    print('Generate constraints...')

    print('SERVE_SUM')
    SERVE_SUM = SERVE == z3.Sum([find_max(e.L.items(), v, e.L_D) * ratio
                                 for e,_  in ((e, print('.', end='', flush=True)) for e in endpoints)
                                 for v, ratio in e.requests.items()])
    print()
    print('CAPACITY')
    CAPACITY = [z3.Sum([z3.If(has_video(v, c), sizes[v], 0) for v in videos]) == capacity
                for c, videos in caches.items()]
    VIDEO = z3.Int('VIDEO')
    print('IMP')
    IMP = [z3.ForAll([VIDEO],
                     z3.Implies(has_video(VIDEO, c), z3.Or([VIDEO == v for v in videos])))
           for c, videos in caches.items()]
    return [CAPACITY, SERVE_SUM, IMP]


def iterative(basename, maximize=False):
    capacity, sizes, requests, caches = io.read_file(basename + '.in')
    result = 0  #25234071
    print('preparing...')
    constraints = generate_constraints(capacity, sizes, requests, caches)
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
        d = {c: [v for v in videos if m.evaluate(has_video(v, c))]
             for c, videos in caches.items()}
        io.write_file("{}/{}.txt".format(basename, result), d)
        if maximize:
            break
iterative('videos_worth_spreading')

# iterative('me_at_the_zoo')
# iterative('trending_today')
# iterative('kittens')
