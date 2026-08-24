#define main topology_free_original_main_for_small_cover_test
#include "a2_topology_free_search.cpp"
#undef main

#include "a2_multi_edge_exact_cover.hpp"

#include <array>
#include <functional>
#include <iostream>
#include <unordered_set>

static a2_multi_cover::Input make_input(const Search &s,
                                        const Search::Analysis &z) {
    a2_multi_cover::Input in;
    in.n = s.n;
    in.target = s.target;
    in.mex = z.mex;
    in.components = z.vertices;
    for (int i = 0; i < s.n; ++i) for (int j = 0; j < s.n; ++j)
        in.distance[i][j] = z.dist[i][j];
    for (int d = 1; d <= s.target; ++d)
        if (!z.used.get(d)) in.missing.set(d);
    return in;
}

int main() {
    const int expected[7] = {0, 0, 1, 1, 2, 0, 1};
    for (int order = 2; order <= 6; ++order) {
        Search search(order);
        a2_multi_cover::Checker checker;
        a2_multi_cover::Config config;
        config.max_components = 18;
        config.exact_max_components = 18;
        config.exact_state_budget = 1000000;
        config.validate_candidates = true;
        a2_multi_cover::Counters counters;
        std::array<std::unordered_set<std::string>, 18> seen;
        std::unordered_set<std::string> solutions;

        std::function<void()> rec = [&]() {
            Search::Analysis z = search.analyze();
            if (!z.valid) return;
            std::string state = search.forest_code(true);
            if (!seen[search.edges.size()].insert(state).second) return;
            auto out = checker.check(make_input(search, z), config, counters);
            if (!out.possible) return;
            if (search.edges.size() == static_cast<std::size_t>(order - 1)) {
                if (z.mex == search.target + 1)
                    solutions.insert(search.forest_code(false));
                return;
            }
            for (int u = 0; u < order; ++u) for (int v = u + 1; v < order; ++v) {
                if (z.comp[u] == z.comp[v]) continue;
                if (!search.candidate_cross_ok(z, u, v, z.mex)) continue;
                search.add_edge(u, v, z.mex);
                rec();
                search.pop_edge();
            }
        };
        rec();
        std::cout << "COVER_SMALL order=" << order
                  << " topologies=" << solutions.size()
                  << " checks=" << counters.checks
                  << " hall_fail=" << counters.hall_fail
                  << " exact_fail=" << counters.exact_fail
                  << " exact_unknown=" << counters.exact_budget_pass << "\n";
        if (static_cast<int>(solutions.size()) != expected[order]) return 1;
        if (counters.validation_fail) return 2;
    }
    std::cout << "MULTI_EDGE_EXACT_COVER_SMALL_ORDER_OK\n";
    return 0;
}

