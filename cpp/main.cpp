#include <stdio.h>
#include <algorithm>
#include <map>
#include <set>
#include <queue>

using latency_t = int;
using video_t = size_t;
using cache_t = size_t;

template<typename ... Args>
void log(const char* fmt, Args&&... args) {
    fprintf(stderr, fmt, args...);
}

void read(size_t& x) {
    (void)scanf("%zu", &x);
}
void read(int& x) {
    (void)scanf("%d", &x);
}

template<typename T, typename T1, typename ... Args>
void read(T& x, T1& x1, Args&&... args) {
    read(x);
    read(x1, args...);
}

struct Endpoint {
    std::map<cache_t, latency_t> latencies;
    std::vector<int> requests;
};

Endpoint read_endpoint(size_t V) {
    latency_t ld;
    size_t k;
    read(ld, k);
    std::map<cache_t, latency_t> latencies;
    for (size_t i=0; i < k; i++) {
        size_t c;
        latency_t lc;
        read(c); read(lc);
        latencies[c] = lc;
    }
    return Endpoint{latencies, std::vector<int>(V)};
}

struct Data {
    std::vector<int> sizes;
    std::vector<Endpoint> endpoints;
};

struct LatencyGainComp {
    const Data& d;
    const cache_t c;
    int sum(video_t v) {
        int sum = 0;
        for (auto e : d.endpoints) {
            for (auto c1 : e.latencies) {
                if (e.latencies.count(c) && c1.first != c) {
                    sum += e.requests[v] * (c1.second - e.latencies[c]) / d.sizes[v];
                }
            }
        }
        return sum;
    }
    bool operator()(video_t v1, video_t v2) {
        return sum(v1) > sum(v2);
    }
};

std::vector<std::set<video_t>> readfile() {
    size_t V, E, R, C, capacity;
    read(V, E, R, C, capacity);
    std::vector<int> sizes(V);
    for (size_t i=0; i < V; i++)
        read(sizes[i]);

    std::vector<Endpoint> endpoints(E);
    for (size_t i=0; i < E; i++) {
        endpoints[i] = read_endpoint(V);
    }
    Data d{sizes, endpoints};
    using PQ=std::priority_queue<video_t, std::vector<video_t>, LatencyGainComp>;
    std::vector<PQ> caches;
    for (size_t c=0; c < C; c++) {
        caches.emplace_back(LatencyGainComp{d, c});
    }
    for (size_t r=0; r < R; r++) {
        size_t v, en;
        latency_t n;
        read(v, en, n);
        Endpoint& e = endpoints[en];
        e.requests[v] += n;
        size_t all = e.latencies.size();
        size_t i = 0;
        for (auto cl: e.latencies) {
            log("Requests: %zu / %zu - cache %zu / %zu   \r", r, R, i++, all);
            caches[cl.first].push(v);
        }
    }
    log("                                             \r");

    std::vector<std::set<video_t>> res;
    const size_t size = caches.size();
    int c = 0;
    for (auto cache : caches) {
        std::set<video_t> vs;
        size_t total = 0;
        size_t all = cache.size();
        while (!cache.empty()) {
            video_t v = cache.top();
            log("Caches: %zu / %zu - video %zu / %zu    \r", c, size, all - cache.size(), all);
            cache.pop();
            auto s = sizes[v];
            if (total + s <= capacity) {
                total += s;
                vs.insert(v);
            }
            if (total == capacity)
                break;
        }
        res.emplace_back(vs);
    }
    log("                                                   \r");
    return res;
}

void print_file(std::vector<std::set<video_t>> allocation) {
    size_t size = allocation.size();
    printf("%zu\n", size);
    for (size_t c=0; c<size; c++) {
        printf("%zu", c);
        for (auto v : allocation[c])
             printf(" %zu", v);
        printf("\n");
    }

}
int main() {
    setbuf(stderr, NULL);
    print_file(readfile());
}
