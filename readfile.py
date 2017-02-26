
from collections import namedtuple, defaultdict, Counter

Endpoint = namedtuple('Endpoint', ('L_D', 'K', 'L', 'requests'))


def read_line_ints(line):
    return [int(x) for x in line.strip().split()]


def read_endpoint(f):
    L_D, K = read_line_ints(next(f))  # latency to data server, number of cache servers
    latencies = {c: L_c for c, L_c in (read_line_ints(next(f)) for _ in range(K))}
    requests = Counter()
    return Endpoint(L_D, K, latencies, requests)


def read_file(filename):
    with open(filename) as f:
        txt = f.readlines()
    f = iter(txt)
    V, E, R, C, capacity = read_line_ints(next(f))
    print('Videos: {}\n'
          'Endpoints: {}\n'
          'Requests: {}\n'
          'Servers: {}\n'
          'Capacity: {}'.format(V, E, R, C, capacity))
    sizes = read_line_ints(next(f))
    assert len(sizes) == V
    endpoints = [read_endpoint(f) for _ in range(E)]

    start = 1 + 1 + sum(e.K + 1 for e in endpoints)
    for line in txt[start:]:
        v, e, n = read_line_ints(line)
        endpoints[e].requests[v] += n
    # for e in endpoints:
    #     for v, n in list(e.requests.items()):
    #         e.requests[v] = (n // sizes[v]**2) + 1
    #         print(e.requests[v])

    caches = defaultdict(set)
    for e in endpoints:
        for v in e.requests:
            for c, l in e.L.items():
                caches[c].add(v)

    return capacity, sizes, endpoints, caches


def write_file(filename, d):
    with open(filename, "w") as out:
        print(len(d), file=out)
        for k in d:
            print(k, *d[k], file=out)
