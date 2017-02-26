#include <stdio.h>
#include <algorithm>
#include <vector>
#include <map>
#include <set>

struct Endpoint {
    int ld;
    int k;
    std::map<int, int> latencies;
    std::vector<int> requests;
};

Endpoint read_endpoint(int C, int V) {
    int ld, k;
    scanf("%d %d", &ld, &k);
    std::map<int, int> latencies; //(C);
    for (int i=0; i < k; i++) {
        int c, lc;
        scanf("%d %d", &c, &lc);
        latencies[c] = lc;
    }
    return Endpoint{ld, k, latencies, std::vector<int>(V)};
}

struct Data {
    int capacity;
    std::vector<int> sizes;
    std::vector<Endpoint> endpoints;
    std::vector<std::set<int>> caches;
};

Data readfile() {
    int V, E, R, C, capacity;
    scanf("%d %d %d %d %d", &V, &E, &R, &C, &capacity);
    std::vector<int> sizes(V);
    for (int i=0; i < V; i++)
        scanf("%d", &sizes[i]);
    /*
    printf("%d %d %d %d %d\n", V, E, R, C, capacity);
    for (auto s : sizes)
        printf("%d ", s);
    printf("\n");
    */
    std::vector<Endpoint> endpoints(E);
    for (int i=0; i < E; i++) {
        endpoints[i] = read_endpoint(C, V);
    }
    //printf("Requests...\n");
    std::vector<std::set<int>> caches(C);
    for (int r=0; r < R; r++) {
        int v, en, n;
        scanf("%d %d %d", &v, &en, &n);
        // printf("%d %d %d\n", v, e, n);
        Endpoint& e = endpoints[en];
        e.requests[v] += n;
        for (auto cl: e.latencies) {
            caches[cl.first].insert(v);
        }
    }
    return Data{capacity, sizes, endpoints, caches};
}

struct LatencyGainComp {
    const Data& d;
    const int c;
    int sum(int v) {
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
    bool operator()(int v1, int v2) {
        return sum(v1) > sum(v2);
    }
};

std::vector<std::set<int>> allocate(const Data& d) {
    std::vector<std::set<int>> res(d.caches.size());
    for (int c=0; c < (int)d.caches.size(); c++) {
        std::vector<int> videos(d.caches[c].begin(), d.caches[c].end());
        std::sort(videos.begin(), videos.end(), LatencyGainComp{d, c});
        int total = 0;
        for (auto v : videos) {
            auto s = d.sizes[v];
            if (total + s <= d.capacity) {
                total += s;
                res[c].insert(v);
            }
            if (total == d.capacity)
                break;
        }
    }
    return res;
}

void print_file(std::vector<std::set<int>> allocation) {
    int size = allocation.size();
    printf("%d\n", size);
    for (int c=0; c<size; c++) {
        printf("%d", c);
        for (auto v : allocation[c])
             printf(" %d", v);
        printf("\n");
    }

}
int main() {
    Data d = readfile();
    std::vector<std::set<int>> allocation = allocate(d);
    print_file(allocation);
}
