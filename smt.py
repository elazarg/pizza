#!/usr/bin/env python3
import readfile as io
from collections import defaultdict


def progressbar(xs):
    xs = list(xs)
    for i, x in enumerate(xs):
        print('\r{}%'.format(i * 100 / len(xs)), end='', flush=True)
        yield x
    print('\r100%')


def generate_constraints(capacity, sizes, endpoints, caches):
    print('Generate constraints...')

    d = defaultdict(list)
    for c, videos in progressbar(list(caches.items())):
        def latency_gain(v):
            return sum(e.requests[v] * (e.L[c1] - e.L[c]) // sizes[v]
                       for e in endpoints
                       for c1 in e.L
                       if c in e.L and c1 != c)
        total = 0
        for v in sorted(videos, key=latency_gain, reverse=True):
            s = sizes[v]
            if total + s == capacity:
                break
            if total + s <= capacity:
                total += s
                d[c].append(v)
    return d


def greedy(basename, maximize=False, result=0):
    capacity, sizes, endpoints, caches = io.read_file(basename + '.in')
    print('preparing...')
    d = generate_constraints(capacity, sizes, endpoints, caches)
    io.write_file("{}/{}.txt".format(basename, 'greedy'), d)

if __name__ == '__main__':
    greedy('trending_today')
    greedy('kittens')
    greedy('videos_worth_spreading')
    greedy('me_at_the_zoo')
