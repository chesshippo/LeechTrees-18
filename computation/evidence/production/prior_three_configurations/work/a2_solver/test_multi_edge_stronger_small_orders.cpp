#define main topology_free_original_main_for_stronger_small_test
#include "a2_topology_free_search.cpp"
#undef main

#include "a2_multi_edge_stronger_relaxation.hpp"

#include <array>
#include <functional>
#include <iostream>
#include <unordered_set>

static a2_multi_cover::Input stronger_input(const Search &search,
                                             const Search::Analysis &z) {
    a2_multi_cover::Input in;
    in.n = search.n;
    in.target = search.target;
    in.mex = z.mex;
    in.components = z.vertices;
    for (int i = 0; i < search.n; ++i)
        for (int j = 0; j < search.n; ++j)
            in.distance[i][j] = z.dist[i][j];
    for (int rank = 1; rank <= search.target; ++rank)
        if (!z.used.get(rank)) in.missing.set(rank);
    return in;
}

int main() {
    const int expected[7] = {0, 0, 1, 1, 2, 0, 1};
    for (int order = 2; order <= 6; ++order) {
        Search search(order);
        a2_multi_cover_stronger::Checker checker;
        a2_multi_cover_stronger::Config config;
        config.max_components = 18;
        config.max_mex_owner_blocks = 10000;
        config.run_two_merge_conditioned = true;
        config.max_two_merge_branches = 1000000;
        config.matching_work_budget = 1000000000ULL;
        a2_multi_cover_stronger::Counters counters;
        std::array<std::unordered_set<std::string>, 18> seen;
        std::unordered_set<std::string> solutions;

        std::function<void()> rec = [&]() {
            Search::Analysis z = search.analyze();
            if (!z.valid) return;
            std::string state = search.forest_code(true);
            if (!seen[search.edges.size()].insert(state).second) return;
            auto out = checker.check(stronger_input(search, z), config,
                                     counters);
            if (!out.possible) return;
            if (search.edges.size() == static_cast<std::size_t>(order - 1)) {
                if (z.mex == search.target + 1)
                    solutions.insert(search.forest_code(false));
                return;
            }
            for (int u = 0; u < order; ++u) {
                for (int v = u + 1; v < order; ++v) {
                    if (z.comp[u] == z.comp[v]) continue;
                    if (!search.candidate_cross_ok(z, u, v, z.mex)) continue;
                    search.add_edge(u, v, z.mex);
                    rec();
                    search.pop_edge();
                }
            }
        };
        rec();
        std::cout << "STRONGER_SMALL order=" << order
                  << " topologies=" << solutions.size()
                  << " checks=" << counters.checks
                  << " indexed_fail=" << counters.indexed_matching_fail
                  << " conditioned_fail=" << counters.mex_owner_fail
                  << " budget_pass=" << counters.budget_pass << "\n";
        if (static_cast<int>(solutions.size()) != expected[order]) return 1;
        if (counters.budget_pass) return 2;
    }
    std::cout << "MULTI_EDGE_STRONGER_SMALL_ORDER_OK\n";
    return 0;
}
