#include "a2_multi_edge_exact_cover_optimized.hpp"

#include <cassert>
#include <iostream>
#include <random>
#include <unordered_set>

using a2_multi_cover::RankMask;
using a2_multi_cover::Slot;

static RankMask mask(std::initializer_list<int> ranks) {
    RankMask z;
    for (int rank : ranks) z.set(rank);
    return z;
}

static Slot slot(int demand, std::initializer_list<RankMask> candidates) {
    Slot z;
    z.demand = demand;
    z.candidates.assign(candidates.begin(), candidates.end());
    std::sort(z.candidates.begin(), z.candidates.end(),
              [](const RankMask &a, const RankMask &b) { return a.x < b.x; });
    for (const auto &candidate : z.candidates) z.allowed_ranks |= candidate;
    return z;
}

static void compare(const std::vector<Slot> &slots) {
    std::vector<const Slot *> pointers;
    for (const Slot &z : slots) pointers.push_back(&z);
    a2_multi_cover::Counters old_counters;
    a2_multi_cover::detail::ExactSolver old(
        pointers, 16, 10000000, old_counters, false);
    auto old_status = old.run();
    assert(old_status != a2_multi_cover::detail::ExactStatus::unknown);

    a2_multi_cover_optimized::Counters counters;
    a2_multi_cover_optimized::Config config;
    config.state_budget = 10000000;
    config.root_arc_comparison_budget = 10000000;
    a2_multi_cover_optimized::Solver optimized(slots, config, counters);
    auto status = optimized.run();
    assert(status != a2_multi_cover_optimized::Status::unknown);
    assert((old_status == a2_multi_cover::detail::ExactStatus::yes) ==
           (status == a2_multi_cover_optimized::Status::yes));
}

int main() {
    compare({slot(2, {mask({1,2}), mask({3,4})}),
             slot(2, {mask({1,3}), mask({2,4})})});
    compare({slot(2, {mask({1,2}), mask({3,4})}),
             slot(2, {mask({1,3}), mask({2,4}), mask({3,4})})});

    // Identical families exercise the exact permutation quotient.
    Slot repeated_yes = slot(2, {mask({1,2}), mask({3,4}), mask({5,6})});
    compare({repeated_yes, repeated_yes, repeated_yes});
    Slot repeated_no = slot(2, {mask({1,2}), mask({1,3}), mask({2,3})});
    compare({repeated_no, repeated_no});

    std::mt19937_64 rng(0xA2018ULL);
    for (int trial = 0; trial < 500; ++trial) {
        const int rank_count = 4 + rng() % 5;
        const int family_count = 1 + rng() % 5;
        std::vector<Slot> slots;
        for (int family = 0; family < family_count; ++family) {
            // Frequently clone an earlier family to stress multiplicities.
            if (!slots.empty() && rng() % 4 == 0) {
                slots.push_back(slots[rng() % slots.size()]);
                continue;
            }
            const int demand = 1 + rng() % std::min(3, rank_count);
            std::unordered_set<RankMask, a2_multi_cover::RankMaskHash> unique;
            int combinations = 1;
            for (int k = 1; k <= demand; ++k)
                combinations = combinations * (rank_count - demand + k) / k;
            const int wanted = 1 + rng() % std::min(6, combinations);
            while (static_cast<int>(unique.size()) < wanted) {
                RankMask candidate;
                while (candidate.count() < demand)
                    candidate.set(1 + rng() % rank_count);
                unique.insert(candidate);
            }
            Slot z;
            z.demand = demand;
            z.candidates.assign(unique.begin(), unique.end());
            std::sort(z.candidates.begin(), z.candidates.end(),
                      [](const RankMask &a, const RankMask &b) {
                          return a.x < b.x;
                      });
            for (const auto &candidate : z.candidates)
                z.allowed_ranks |= candidate;
            slots.push_back(std::move(z));
        }
        compare(slots);
    }

    // Budget exhaustion is explicitly UNKNOWN/PASS material, never NO.
    {
        std::vector<Slot> slots{slot(1, {mask({1}), mask({2})})};
        a2_multi_cover_optimized::Counters counters;
        a2_multi_cover_optimized::Config config;
        config.state_budget = 0;
        a2_multi_cover_optimized::Solver optimized(slots, config, counters);
        assert(optimized.run() == a2_multi_cover_optimized::Status::unknown);
    }

    std::cout << "MULTI_EDGE_EXACT_COVER_OPTIMIZED_TEST_OK\n";
    return 0;
}
