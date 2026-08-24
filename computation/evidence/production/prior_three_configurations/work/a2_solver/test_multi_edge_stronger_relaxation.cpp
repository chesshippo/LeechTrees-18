#include "a2_multi_edge_stronger_relaxation.hpp"

#include <cassert>
#include <iostream>

using a2_multi_cover::Input;
using a2_multi_cover::RankMask;

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
    // Abstract strict-strength witness: the old capacitated group Hall test
    // gives both demand clones {1,2}, while indexed domains {1},{1} fail.
    {
        RankMask available = mask({1, 2});
        std::vector<RankMask> indexed{mask({1}), mask({1})};
        a2_multi_cover_stronger::Counters counters;
        auto status = a2_multi_cover_stronger::detail::indexed_matching_possible(
            indexed, available, 2, 1000, counters);
        assert(status ==
               a2_multi_cover_stronger::detail::MatchingStatus::no);

        a2_multi_cover::Slot group;
        group.demand = 2;
        group.allowed_ranks = available;
        std::vector<const a2_multi_cover::Slot *> slots{&group};
        std::vector<RankMask> group_domains{available};
        assert(a2_multi_cover::detail::rank_hall_possible(
            slots, group_domains, 2));
    }

    a2_multi_cover_stronger::Config config;
    config.max_components = 18;
    config.matching_work_budget = 10000000;
    a2_multi_cover_stronger::Checker checker;

    // Every all-singleton prefix is feasible for both indexed Hall layers.
    {
        Input in = singleton_input(4);
        a2_multi_cover_stronger::Counters counters;
        a2_multi_cover_stronger::Outcome out =
            checker.check(in, config, counters);
        assert(out.possible);
        assert(counters.mex_owner_branches == 1);
    }

    // The order-3 weight-1 prefix has the unique missing block {2,3}; fixing
    // its mex owner leaves no slots, so conditioned Hall passes.
    {
        Input in;
        in.n = 3;
        in.target = 3;
        in.mex = 2;
        in.components = {{0, 1}, {2}};
        in.distance[0][0] = in.distance[1][1] =
            in.distance[2][2] = 0;
        in.distance[0][1] = in.distance[1][0] = 1;
        in.missing = mask({2, 3});
        a2_multi_cover_stronger::Counters counters;
        a2_multi_cover_stronger::Outcome out =
            checker.check(in, config, counters);
        assert(out.possible);
    }

    // There is no additive block for the punctured set {2,4}.
    {
        Input in;
        in.n = 3;
        in.target = 4;
        in.mex = 2;
        in.components = {{0, 1}, {2}};
        in.distance[0][0] = in.distance[1][1] =
            in.distance[2][2] = 0;
        in.distance[0][1] = in.distance[1][0] = 1;
        in.missing = mask({2, 4});
        a2_multi_cover_stronger::Counters counters;
        a2_multi_cover_stronger::Outcome out =
            checker.check(in, config, counters);
        assert(!out.possible && out.reason ==
                   a2_multi_cover_stronger::Reason::no_pattern);
    }

    std::cout << "MULTI_EDGE_STRONGER_RELAXATION_TEST_OK\n";
    return 0;
}
