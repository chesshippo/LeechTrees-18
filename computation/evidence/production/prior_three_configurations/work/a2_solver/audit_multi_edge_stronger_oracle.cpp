#define main topology_free_original_main_for_stronger_audit
#include "a2_topology_free_search.cpp"
#undef main

#include "a2_multi_edge_exact_cover.hpp"
#include "a2_multi_edge_stronger_relaxation.hpp"

#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <random>
#include <unordered_set>
#include <vector>

using a2_multi_cover::Input;
using a2_multi_cover::RankMask;

static Input snapshot(const Search &search, const Search::Analysis &z) {
    Input in;
    in.n = search.n;
    in.target = search.target;
    in.mex = z.mex;
    in.components = z.vertices;
    for (int i = 0; i < search.n; ++i)
        for (int j = 0; j < search.n; ++j)
            in.distance[i][j] = z.dist[i][j];
    for (int r = 1; r <= search.target; ++r)
        if (!z.used.get(r)) in.missing.set(r);
    return in;
}

static bool brute_match_rec(const std::vector<RankMask> &domains,
                            const RankMask &available, int target,
                            std::vector<unsigned char> &done,
                            RankMask used, int left) {
    if (!left) return true;
    int chosen = -1, best = target + 1;
    for (int s = 0; s < static_cast<int>(domains.size()); ++s) {
        if (done[s]) continue;
        int count = (domains[s] & available).without(used).count();
        if (count < best) { best = count; chosen = s; }
    }
    if (chosen < 0 || !best) return false;
    done[chosen] = 1;
    RankMask choices = (domains[chosen] & available).without(used);
    for (int r = 1; r <= target; ++r) {
        if (!choices.get(r)) continue;
        RankMask next = used;
        next.set(r);
        if (brute_match_rec(domains, available, target, done, next, left - 1)) {
            done[chosen] = 0;
            return true;
        }
    }
    done[chosen] = 0;
    return false;
}

static bool brute_match(const std::vector<RankMask> &domains,
                        const RankMask &available, int target,
                        bool require_cover) {
    if (domains.size() > static_cast<std::size_t>(available.count()) ||
        (require_cover && domains.size() !=
                              static_cast<std::size_t>(available.count())))
        return false;
    std::vector<unsigned char> done(domains.size());
    return brute_match_rec(domains, available, target, done, RankMask{},
                           static_cast<int>(domains.size()));
}

static void audit_matcher(std::mt19937_64 &rng) {
    for (int target = 1; target <= 8; ++target) {
        for (int trial = 0; trial < 4000; ++trial) {
            RankMask available;
            for (int r = 1; r <= target; ++r)
                if (rng() & 1ULL) available.set(r);
            int slots = static_cast<int>(rng() % 9);
            std::vector<RankMask> domains(slots);
            for (RankMask &domain : domains)
                for (int r = 1; r <= target; ++r)
                    if (rng() & 1ULL) domain.set(r);
            for (bool cover : {false, true}) {
                bool expected = brute_match(domains, available, target, cover);
                a2_multi_cover_stronger::Counters counters;
                auto got = a2_multi_cover_stronger::detail::
                    indexed_matching_possible(domains, available, target,
                                              UINT64_MAX / 4, counters, cover);
                assert(got != a2_multi_cover_stronger::detail::
                                  MatchingStatus::unknown);
                assert((got == a2_multi_cover_stronger::detail::
                                   MatchingStatus::yes) == expected);
            }
        }
    }
}

struct OracleTotals {
    std::uint64_t states = 0;
    std::uint64_t exact_yes = 0;
    std::uint64_t exact_no = 0;
    std::uint64_t exact_unknown = 0;
    std::uint64_t stronger_reject = 0;
};

static void compare_state(const Search &search, const Search::Analysis &z,
                          OracleTotals &totals) {
    if (z.vertices.size() > 5 || z.vertices.size() <= 1) return;
    ++totals.states;
    Input in = snapshot(search, z);

    a2_multi_cover::Checker exact_checker;
    a2_multi_cover::Config exact_config;
    exact_config.local_max_components = 18;
    exact_config.max_components = 18;
    exact_config.exact_max_components = 18;
    exact_config.exact_candidate_cap = 10000000;
    exact_config.exact_state_budget = 1000000000ULL;
    exact_config.exact_residual_hall = true;
    exact_config.validate_candidates = true;
    a2_multi_cover::Counters exact_counters;
    auto exact = exact_checker.check(in, exact_config, exact_counters);
    bool exact_yes = exact.possible && exact_counters.exact_pass == 1;
    bool exact_unknown = exact.possible && exact_counters.exact_pass == 0;
    totals.exact_yes += exact_yes;
    totals.exact_unknown += exact_unknown;
    totals.exact_no += !exact.possible;

    a2_multi_cover_stronger::Checker stronger_checker;
    a2_multi_cover_stronger::Config stronger_config;
    stronger_config.max_components = 18;
    stronger_config.max_mex_owner_blocks = 100000;
    stronger_config.matching_work_budget = 1000000000ULL;
    a2_multi_cover_stronger::Counters stronger_counters;
    auto stronger = stronger_checker.check(in, stronger_config,
                                            stronger_counters);
    totals.stronger_reject += !stronger.possible;
    // A whole-pattern exact cover induces every stronger Hall matching,
    // including the mex-owner branch.  This is the key no-false-negative
    // implication being independently checked here.
    if (exact_yes && !stronger.possible) {
        std::cerr << "ORACLE_IMPLICATION_FAILURE n=" << search.n
                  << " edges=" << search.edges.size()
                  << " reason=" << static_cast<int>(stronger.reason) << "\n";
        std::abort();
    }
}

static OracleTotals exhaustive_states(int order) {
    Search search(order);
    std::array<std::unordered_set<std::string>, 18> seen;
    OracleTotals totals;
    std::function<void()> rec = [&]() {
        Search::Analysis z = search.analyze();
        if (!z.valid) return;
        std::string state = search.forest_code(true);
        if (!seen[search.edges.size()].insert(state).second) return;
        compare_state(search, z, totals);
        if (search.edges.size() == static_cast<std::size_t>(order - 1)) return;
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
    return totals;
}

int main() {
    std::mt19937_64 rng(0x51A11A2ULL);
    audit_matcher(rng);
    std::cout << "MATCHER_BRUTE_ORACLE_OK cases=64000\n";
    for (int order = 2; order <= 8; ++order) {
        OracleTotals z = exhaustive_states(order);
        std::cout << "ORACLE order=" << order
                  << " states=" << z.states
                  << " exact_yes=" << z.exact_yes
                  << " exact_no=" << z.exact_no
                  << " exact_unknown=" << z.exact_unknown
                  << " stronger_reject=" << z.stronger_reject << "\n";
        assert(z.exact_unknown == 0);
    }
    std::cout << "MULTI_EDGE_STRONGER_ORACLE_AUDIT_OK\n";
}
