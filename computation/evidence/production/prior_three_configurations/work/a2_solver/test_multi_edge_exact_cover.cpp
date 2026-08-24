#include "a2_multi_edge_exact_cover.hpp"

#include <cassert>
#include <iostream>

using namespace a2_multi_cover;

static RankMask mask(std::initializer_list<int> ranks) {
    RankMask z;
    for (int r : ranks) z.set(r);
    return z;
}

static Input singleton_input(int n) {
    Input in;
    in.n = n;
    in.target = n * (n - 1) / 2;
    for (int i = 0; i < n; ++i) {
        in.components.push_back({i});
        in.distance[i][i] = 0;
    }
    for (int r = 1; r <= in.target; ++r) in.missing.set(r);
    return in;
}

int main() {
    {
        RankMask x = mask({1, 63, 64, 127, 128, 153});
        RankMask y = x.shifted_up(1);
        assert(y.get(2) && y.get(64) && y.get(65));
        assert(y.get(128) && y.get(129) && y.get(154));
        assert(y.shifted_down(1) == x);
    }

    Config cfg;
    cfg.max_components = 18;
    cfg.exact_max_components = 18;
    cfg.validate_candidates = true;
    Counters counters;
    Checker checker;

    // With four singleton components, each component-pair block is an
    // arbitrary one-rank block.  The generic-slot reduction must pass.
    {
        Input in = singleton_input(4);
        Outcome out = checker.check(in, cfg, counters);
        assert(out.possible);
    }

    // One exposed weight-1 edge and one singleton.  The only cross block is
    // {2,3}, produced by either endpoint orientation with port length 2.
    {
        Input in;
        in.n = 3;
        in.target = 3;
        in.components = {{0, 1}, {2}};
        in.distance[0][0] = in.distance[1][1] = in.distance[2][2] = 0;
        in.distance[0][1] = in.distance[1][0] = 1;
        in.missing = mask({2, 3});
        Outcome out = checker.check(in, cfg, counters);
        assert(out.possible);
    }

    // The same rooted component cannot translate {0,1} into the punctured
    // missing set {2,4}; candidate construction must reject it exactly.
    {
        Input in;
        in.n = 3;
        in.target = 4;
        in.components = {{0, 1}, {2}};
        in.distance[0][0] = in.distance[1][1] = in.distance[2][2] = 0;
        in.distance[0][1] = in.distance[1][0] = 1;
        in.missing = mask({2, 4});
        Outcome out = checker.check(in, cfg, counters);
        assert(!out.possible && out.reason == Reason::no_candidate);
    }

    // Synthetic coherence gap: clone-Hall sees all four ranks for both
    // demand-2 slots, but no candidate block of the second slot complements
    // a candidate block of the first.  Exact DP must detect this.
    {
        Slot a, b;
        a.demand = b.demand = 2;
        a.candidates = {mask({1, 2}), mask({3, 4})};
        b.candidates = {mask({1, 3}), mask({2, 4})};
        for (const auto &z : a.candidates) a.allowed_ranks |= z;
        for (const auto &z : b.candidates) b.allowed_ranks |= z;
        std::vector<const Slot *> slots{&a, &b};
        std::vector<RankMask> domains{a.allowed_ranks, b.allowed_ranks};
        assert(detail::rank_hall_possible(slots, domains, 4));
        Counters local;
        detail::ExactSolver solver(slots, 4, 100, local);
        assert(solver.run() == detail::ExactStatus::no);

        b.candidates.push_back(mask({3, 4}));
        b.allowed_ranks |= b.candidates.back();
        Counters local2;
        detail::ExactSolver solver2(slots, 4, 100, local2);
        assert(solver2.run() == detail::ExactStatus::yes);
    }

    std::cout << "MULTI_EDGE_EXACT_COVER_TEST_OK\n";
    return 0;
}

