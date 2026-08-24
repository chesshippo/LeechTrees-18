#include "multi_edge_parity_coherence.hpp"

#include <cassert>
#include <iostream>

using a2_multi_cover::Input;
using multi_edge_parity_coherence::Checker;
using multi_edge_parity_coherence::Config;
using multi_edge_parity_coherence::Counters;
using multi_edge_parity_coherence::Reason;

static void set_missing(Input &in, std::initializer_list<int> ranks) {
    for (int r : ranks) in.missing.set(r);
}

int main() {
    Checker checker;
    Config config;

    // The unique order-2 parity pattern has one odd cross rank.
    {
        Input in;
        in.n = 2;
        in.target = 1;
        in.mex = 1;
        in.components = {{0}, {1}};
        set_missing(in, {1});
        Counters counters;
        auto out = checker.check(in, config, counters);
        assert(out.possible);
    }

    // For n=5 the ten prescribed ranks contain five odd distances, but
    // p(5-p)=5 has no integer solution.  This is the parity reason that no
    // order-5 Leech tree exists.
    {
        Input in;
        in.n = 5;
        in.target = 10;
        in.mex = 1;
        in.components = {{0}, {1}, {2}, {3}, {4}};
        for (int r = 1; r <= 10; ++r) in.missing.set(r);
        Counters counters;
        auto out = checker.check(in, config, counters);
        assert(!out.possible);
        assert(out.reason == Reason::impossible_global_mass);
    }

    // Guard against unsound offset-mask deduplication.  Rooting an odd dimer
    // at its two endpoints yields the same {0,1} offset mask but opposite
    // parity labels.  Both generating port patterns must be examined.
    {
        Input in;
        in.n = 3;
        in.target = 3;
        in.mex = 2;
        in.components = {{0}, {1, 2}};
        in.distance[1][2] = in.distance[2][1] = 1;
        set_missing(in, {2, 3});
        Counters counters;
        auto out = checker.check(in, config, counters);
        assert(out.possible);
        assert(counters.port_patterns == 2);
        assert(counters.candidate_lengths == 2);
    }

    // Pure profile-CSP regression: three pair labels all forced to 1 cannot
    // be the pairwise XORs of three component orientations.  Mass-one
    // profiles exist, so failure is genuinely global relation inconsistency.
    {
        std::vector<std::array<int, 2>> counts(3, {1, 0});
        std::vector<std::vector<unsigned>> relation(
            3, std::vector<unsigned>(3, 0));
        relation[0][1] = relation[0][2] = relation[1][2] = 1U << 1;
        Counters counters;
        bool possible =
            multi_edge_parity_coherence::detail::coherent_profile_exists(
                counts, relation, 1, counters);
        assert(!possible);
        assert(counters.mass_profiles_tested > 0);
    }

    // The canonical G001 row-7 prefix has internal spectrum 1,...,6 and
    // must admit at least one coherent 7|11 continuation profile at this
    // deliberately relaxed precheck.
    {
        Input in;
        in.n = 18;
        in.target = 153;
        in.mex = 7;
        in.components.push_back({0, 1, 2, 3});
        for (int v = 4; v < 18; ++v) in.components.push_back({v});
        const int coordinate[4] = {0, 1, 4, 6};
        for (int x = 0; x < 4; ++x) for (int y = 0; y < 4; ++y)
            in.distance[x][y] =
                coordinate[x] > coordinate[y]
                    ? coordinate[x] - coordinate[y]
                    : coordinate[y] - coordinate[x];
        for (int r = 7; r <= 153; ++r) in.missing.set(r);
        Counters counters;
        auto out = checker.check(in, config, counters);
        assert(out.possible);
    }

    std::cout << "MULTI_EDGE_PARITY_COHERENCE_OK\n";
    return 0;
}
