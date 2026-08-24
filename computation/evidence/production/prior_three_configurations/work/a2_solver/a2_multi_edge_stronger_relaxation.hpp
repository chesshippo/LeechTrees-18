#pragma once

#include "a2_multi_edge_exact_cover.hpp"

#include <algorithm>
#include <cstdint>
#include <functional>
#include <stdexcept>
#include <unordered_set>
#include <utility>
#include <vector>

// Stronger, still sound relaxations of the current-component additive
// exact-cover condition.  This file is deliberately isolated from the
// production solver and from a2_multi_edge_exact_cover.hpp so that the new
// conditions can be audited and benchmarked before integration.
//
// For components K_i,K_j and each indexed vertex pair (x,y), let
//
//   D_{ijxy} = { d_i(x,u)+L+d_j(v,y) }
//
// where the union ranges only over port/length triples (u,v,L) whose *whole*
// |K_i||K_j|-entry block is injective and contained in the missing ranks.
// Any Leech completion assigns every indexed cross-component pair a distinct
// member of its D-domain.  Thus a perfect matching of all indexed pairs to
// all missing ranks is necessary.  This refines the existing capacitated
// Hall check, which gives every pair in K_i x K_j the same union domain.
//
// The conditioned version uses T2a/self-puncturing once more.  The block that
// owns the current mex must have translation L=mex and is exactly the first
// chronological merge block.  Fix each possible such block B in turn,
// delete its component-pair family and its ranks, discard every remaining
// candidate pattern meeting B, and rerun indexed Hall.  A completion supplies
// one branch of this disjunction, so failure of every branch is sound.

namespace a2_multi_cover_stronger {

using a2_multi_cover::Input;
using a2_multi_cover::RankMask;
using a2_multi_cover::RankMaskHash;

struct Pattern {
    RankMask block;
    std::vector<unsigned char> value; // one rank per indexed vertex pair
    int length = 0;
    int left_port = -1;
    int right_port = -1;
};

struct Family {
    int left = -1;
    int right = -1;
    std::vector<std::pair<int, int>> indexed_pairs;
    std::vector<Pattern> patterns;
    std::vector<RankMask> indexed_domains;
};

struct Config {
    int max_components = 8;
    bool run_translation_hall = true;
    bool run_mex_conditioned = true;
    // Fix the first two chronological merges coherently before Hall.  This is
    // substantially stronger late in the search, but is off by default until
    // its branch cost has been benchmarked.
    bool run_two_merge_conditioned = false;
    // A cap or budget exhaustion is UNKNOWN/PASS, never a rejection.
    std::size_t max_mex_owner_blocks = 256;
    std::size_t max_two_merge_branches = 10000;
    std::uint64_t matching_work_budget = 100000000;
};

struct Counters {
    std::uint64_t checks = 0;
    std::uint64_t skipped_early = 0;
    std::uint64_t families = 0;
    std::uint64_t port_length_patterns = 0;
    std::uint64_t indexed_slots = 0;
    std::uint64_t translation_matching_calls = 0;
    std::uint64_t translation_matching_fail = 0;
    std::uint64_t indexed_matching_calls = 0;
    std::uint64_t indexed_matching_fail = 0;
    std::uint64_t mex_owner_blocks = 0;
    std::uint64_t mex_owner_branches = 0;
    std::uint64_t mex_owner_hall_fail = 0;
    std::uint64_t mex_owner_fail = 0;
    std::uint64_t two_merge_branches = 0;
    std::uint64_t two_merge_hall_fail = 0;
    std::uint64_t two_merge_fail = 0;
    std::uint64_t cap_pass = 0;
    std::uint64_t budget_pass = 0;
    std::uint64_t matching_edge_scans = 0;
};

enum class Reason {
    pass,
    skipped,
    no_pattern,
    translation_hall,
    indexed_hall,
    no_mex_owner,
    mex_conditioned_hall,
    two_merge_conditioned_hall,
    unknown
};

struct Outcome {
    bool possible = true;
    Reason reason = Reason::pass;
};

namespace detail {

struct PatternKey {
    RankMask block;
    std::vector<unsigned char> value;
    bool operator==(const PatternKey &other) const {
        return block == other.block && value == other.value;
    }
};

struct PatternKeyHash {
    std::size_t operator()(const PatternKey &key) const noexcept {
        std::size_t h = RankMaskHash{}(key.block);
        for (unsigned char v : key.value)
            h ^= static_cast<std::size_t>(v) + 0x9e3779b9U + (h << 6) +
                 (h >> 2);
        return h;
    }
};

inline Family build_family(const Input &in, int i, int j,
                           Counters &counters) {
    Family family;
    family.left = i;
    family.right = j;
    const auto &a = in.components[i];
    const auto &b = in.components[j];
    for (int x : a)
        for (int y : b) family.indexed_pairs.push_back({x, y});
    family.indexed_domains.resize(family.indexed_pairs.size());

    std::unordered_set<PatternKey, PatternKeyHash> unique;
    for (int u : a) {
        for (int v : b) {
            std::vector<int> offset;
            offset.reserve(family.indexed_pairs.size());
            RankMask offsets;
            bool injective = true;
            for (const auto &xy : family.indexed_pairs) {
                int q = in.distance[xy.first][u] +
                        in.distance[v][xy.second];
                if (q < 0 || q > in.target || offsets.get(q)) {
                    injective = false;
                    break;
                }
                offsets.set(q);
                offset.push_back(q);
            }
            if (!injective) continue;

            RankMask allowed_length = in.missing;
            for (int q : offset)
                allowed_length &= in.missing.shifted_down(q);
            allowed_length.clear_outside(1, in.target);

            for (int length = 1; length <= in.target; ++length) {
                if (!allowed_length.get(length)) continue;
                Pattern pattern;
                pattern.length = length;
                pattern.left_port = u;
                pattern.right_port = v;
                pattern.value.reserve(offset.size());
                for (int q : offset) {
                    int rank = length + q;
                    pattern.block.set(rank);
                    pattern.value.push_back(static_cast<unsigned char>(rank));
                }
                if (pattern.block.count() !=
                        static_cast<int>(family.indexed_pairs.size()) ||
                    pattern.block.without(in.missing).any())
                    throw std::logic_error("bad indexed additive pattern");
                PatternKey key{pattern.block, pattern.value};
                if (unique.insert(key).second)
                    family.patterns.push_back(std::move(pattern));
            }
        }
    }

    std::sort(family.patterns.begin(), family.patterns.end(),
              [](const Pattern &p, const Pattern &q) {
                  if (p.block.x != q.block.x) return p.block.x < q.block.x;
                  return p.value < q.value;
              });
    for (const Pattern &pattern : family.patterns)
        for (std::size_t s = 0; s < pattern.value.size(); ++s)
            family.indexed_domains[s].set(pattern.value[s]);

    ++counters.families;
    counters.port_length_patterns += family.patterns.size();
    counters.indexed_slots += family.indexed_pairs.size();
    return family;
}

enum class MatchingStatus { no, yes, unknown };

// Exact bipartite matching for arbitrary per-indexed-pair rank domains.
// The work counter makes this safe in a production pruning layer: UNKNOWN is
// propagated as PASS.
inline MatchingStatus indexed_matching_possible(
    const std::vector<RankMask> &domains, const RankMask &available,
    int target, std::uint64_t work_limit, Counters &counters,
    bool require_cover = true) {
    ++counters.indexed_matching_calls;
    if (domains.size() > static_cast<std::size_t>(available.count()) ||
        (require_cover &&
         domains.size() != static_cast<std::size_t>(available.count())))
        return MatchingStatus::no;
    std::vector<int> order(domains.size());
    for (int s = 0; s < static_cast<int>(domains.size()); ++s) {
        order[s] = s;
        if (!(domains[s] & available).any()) return MatchingStatus::no;
    }
    std::sort(order.begin(), order.end(), [&](int a, int b) {
        return (domains[a] & available).count() <
               (domains[b] & available).count();
    });

    std::vector<int> owner(target + 1, -1);
    bool exhausted = false;
    std::function<bool(int, std::vector<unsigned char> &)> augment =
        [&](int slot, std::vector<unsigned char> &seen) {
            for (int rank = 1; rank <= target; ++rank) {
                if (!available.get(rank) || !domains[slot].get(rank) ||
                    seen[rank])
                    continue;
                if (++counters.matching_edge_scans > work_limit) {
                    exhausted = true;
                    return false;
                }
                seen[rank] = 1;
                if (owner[rank] < 0 || augment(owner[rank], seen)) {
                    owner[rank] = slot;
                    return true;
                }
                if (exhausted) return false;
            }
            return false;
        };

    for (int slot : order) {
        std::vector<unsigned char> seen(target + 1, 0);
        if (!augment(slot, seen))
            return exhausted ? MatchingStatus::unknown : MatchingStatus::no;
    }
    return MatchingStatus::yes;
}

inline std::vector<RankMask> unconditional_domains(
    const std::vector<Family> &families) {
    std::vector<RankMask> domains;
    for (const Family &family : families)
        domains.insert(domains.end(), family.indexed_domains.begin(),
                       family.indexed_domains.end());
    return domains;
}

inline std::vector<RankMask> translation_domains(
    const std::vector<Family> &families,
    const std::vector<unsigned char> *fixed_families = nullptr,
    const RankMask *forbidden = nullptr) {
    std::vector<RankMask> domains;
    for (int f = 0; f < static_cast<int>(families.size()); ++f) {
        if (fixed_families && (*fixed_families)[f]) continue;
        RankMask domain;
        for (const Pattern &pattern : families[f].patterns) {
            if (forbidden && pattern.block.intersects(*forbidden)) continue;
            domain.set(pattern.length);
        }
        domains.push_back(domain);
    }
    return domains;
}

inline std::vector<RankMask> translation_domains(
    const std::vector<Family> &families, int fixed_family,
    const RankMask *forbidden) {
    std::vector<unsigned char> fixed(families.size(), 0);
    if (fixed_family >= 0) fixed[fixed_family] = 1;
    return translation_domains(families, &fixed, forbidden);
}

inline std::vector<RankMask> domains_conditioned_on(
    const std::vector<Family> &families,
    const std::vector<unsigned char> &fixed_families,
    const RankMask &fixed_block) {
    std::vector<RankMask> domains;
    for (int f = 0; f < static_cast<int>(families.size()); ++f) {
        if (fixed_families[f]) continue;
        const Family &family = families[f];
        std::vector<RankMask> local(family.indexed_pairs.size());
        for (const Pattern &pattern : family.patterns) {
            if (pattern.block.intersects(fixed_block)) continue;
            for (std::size_t s = 0; s < pattern.value.size(); ++s)
                local[s].set(pattern.value[s]);
        }
        domains.insert(domains.end(), local.begin(), local.end());
    }
    return domains;
}

inline std::vector<RankMask> domains_conditioned_on(
    const std::vector<Family> &families, int fixed_family,
    const RankMask &fixed_block) {
    std::vector<unsigned char> fixed(families.size(), 0);
    if (fixed_family >= 0) fixed[fixed_family] = 1;
    return domains_conditioned_on(families, fixed, fixed_block);
}

} // namespace detail

class Checker {
  public:
    Outcome check(const Input &in, const Config &config,
                  Counters &counters) const {
        ++counters.checks;
        int component_count = static_cast<int>(in.components.size());
        if (component_count <= 1) return {true, Reason::pass};
        if (component_count > config.max_components) {
            ++counters.skipped_early;
            return {true, Reason::skipped};
        }

        int expected_missing = 0;
        for (int i = 0; i < component_count; ++i)
            for (int j = i + 1; j < component_count; ++j)
                expected_missing += static_cast<int>(
                    in.components[i].size() * in.components[j].size());
        if (expected_missing != in.missing.count())
            throw std::logic_error(
                "indexed Hall cross-pair/missing count mismatch");

        std::vector<Family> families;
        families.reserve(component_count * (component_count - 1) / 2);
        for (int i = 0; i < component_count; ++i) {
            for (int j = i + 1; j < component_count; ++j) {
                families.push_back(detail::build_family(in, i, j, counters));
                if (families.back().patterns.empty())
                    return {false, Reason::no_pattern};
            }
        }

        std::uint64_t work_limit = counters.matching_edge_scans +
                                   config.matching_work_budget;
        if (config.run_translation_hall) {
            ++counters.translation_matching_calls;
            auto translations = detail::translation_domains(families);
            auto status = detail::indexed_matching_possible(
                translations, in.missing, in.target, work_limit, counters,
                false);
            if (status == detail::MatchingStatus::unknown) {
                ++counters.budget_pass;
                return {true, Reason::unknown};
            }
            if (status == detail::MatchingStatus::no) {
                ++counters.translation_matching_fail;
                return {false, Reason::translation_hall};
            }
        }
        auto domains = detail::unconditional_domains(families);
        auto base = detail::indexed_matching_possible(
            domains, in.missing, in.target, work_limit, counters);
        if (base == detail::MatchingStatus::unknown) {
            ++counters.budget_pass;
            return {true, Reason::unknown};
        }
        if (base == detail::MatchingStatus::no) {
            ++counters.indexed_matching_fail;
            return {false, Reason::indexed_hall};
        }
        if (!config.run_mex_conditioned) return {true, Reason::pass};

        struct Owner {
            int family = -1;
            const Pattern *pattern = nullptr;
        };
        std::vector<Owner> owners;
        for (int f = 0; f < static_cast<int>(families.size()); ++f) {
            for (const Pattern &pattern : families[f].patterns) {
                if (pattern.length != in.mex) continue;
                owners.push_back({f, &pattern});
            }
        }
        counters.mex_owner_blocks += owners.size();
        if (owners.empty()) {
            ++counters.mex_owner_fail;
            return {false, Reason::no_mex_owner};
        }
        if (owners.size() > config.max_mex_owner_blocks) {
            ++counters.cap_pass;
            return {true, Reason::unknown};
        }

        auto hall_after_fixed = [&](const std::vector<unsigned char> &fixed,
                                    const RankMask &used) {
            RankMask available = in.missing.without(used);
            if (config.run_translation_hall) {
                ++counters.translation_matching_calls;
                auto translations = detail::translation_domains(
                    families, &fixed, &used);
                auto translation_status = detail::indexed_matching_possible(
                    translations, available, in.target, work_limit, counters,
                    false);
                if (translation_status != detail::MatchingStatus::yes) {
                    if (translation_status == detail::MatchingStatus::no)
                        ++counters.translation_matching_fail;
                    return translation_status;
                }
            }
            auto conditional = detail::domains_conditioned_on(
                families, fixed, used);
            return detail::indexed_matching_possible(
                conditional, available, in.target, work_limit, counters);
        };

        if (!config.run_two_merge_conditioned) {
            // Multiple port pairs can induce the same set block.  Their
            // distinction is irrelevant once only B_1 is fixed, so avoid
            // rerunning Hall for duplicate (family,block) branches.
            std::vector<std::unordered_set<RankMask, RankMaskHash>> seen(
                families.size());
            for (const Owner &owner : owners) {
                const RankMask &block = owner.pattern->block;
                if (!seen[owner.family].insert(block).second) continue;
                ++counters.mex_owner_branches;
                std::vector<unsigned char> fixed(families.size(), 0);
                fixed[owner.family] = 1;
                auto status = hall_after_fixed(fixed, block);
                if (status == detail::MatchingStatus::yes)
                    return {true, Reason::pass};
                if (status == detail::MatchingStatus::unknown) {
                    ++counters.budget_pass;
                    return {true, Reason::unknown};
                }
                ++counters.mex_owner_hall_fail;
            }
            ++counters.mex_owner_fail;
            return {false, Reason::mex_conditioned_hall};
        }

        // Map unordered component pairs to their family index.
        std::vector<std::vector<int>> family_index(
            component_count, std::vector<int>(component_count, -1));
        for (int f = 0; f < static_cast<int>(families.size()); ++f) {
            family_index[families[f].left][families[f].right] = f;
            family_index[families[f].right][families[f].left] = f;
        }

        std::size_t local_two_branches = 0;
        for (const Owner &owner : owners) {
            ++counters.mex_owner_branches;
            const Pattern &first = *owner.pattern;
            const RankMask &first_block = first.block;
            const int left = families[owner.family].left;
            const int right = families[owner.family].right;

            int second_weight = -1;
            for (int rank = 1; rank <= in.target; ++rank) {
                if (in.missing.get(rank) && !first_block.get(rank)) {
                    second_weight = rank;
                    break;
                }
            }
            if (second_weight < 0) {
                // Two components: the first merge consumes every missing
                // rank, and the valid first pattern is already a completion.
                return {true, Reason::pass};
            }

            auto test_second = [&](std::vector<unsigned char> fixed,
                                   const RankMask &second_block) {
                if (++local_two_branches > config.max_two_merge_branches)
                    return detail::MatchingStatus::unknown;
                ++counters.two_merge_branches;
                RankMask used = first_block | second_block;
                auto status = hall_after_fixed(fixed, used);
                if (status == detail::MatchingStatus::no)
                    ++counters.two_merge_hall_fail;
                return status;
            };

            // Case 1: the second edge joins two untouched current
            // components.  Its whole chronological block is one existing
            // component-pair family.
            for (int f = 0; f < static_cast<int>(families.size()); ++f) {
                if (f == owner.family) continue;
                int a = families[f].left, b = families[f].right;
                if (a == left || a == right || b == left || b == right)
                    continue;
                std::unordered_set<RankMask, RankMaskHash> seen_blocks;
                for (const Pattern &second : families[f].patterns) {
                    if (second.length != second_weight ||
                        second.block.intersects(first_block) ||
                        !seen_blocks.insert(second.block).second)
                        continue;
                    std::vector<unsigned char> fixed(families.size(), 0);
                    fixed[owner.family] = fixed[f] = 1;
                    auto status = test_second(fixed, second.block);
                    if (status == detail::MatchingStatus::yes)
                        return {true, Reason::pass};
                    if (status == detail::MatchingStatus::unknown) {
                        ++counters.cap_pass;
                        return {true, Reason::unknown};
                    }
                }
            }

            // Case 2: the second edge joins K_left union K_right to one
            // untouched component K_k.  Here the chronological block fixes
            // the two original families (left,k) and (right,k) coherently.
            std::vector<std::pair<int, bool>> merged_vertices;
            for (int x : in.components[left])
                merged_vertices.push_back({x, true});
            for (int x : in.components[right])
                merged_vertices.push_back({x, false});

            for (int k = 0; k < component_count; ++k) {
                if (k == left || k == right) continue;
                std::unordered_set<RankMask, RankMaskHash> seen_blocks;
                for (const auto &aa : merged_vertices) {
                    int attach = aa.first;
                    bool attach_left = aa.second;
                    for (int port_k : in.components[k]) {
                        RankMask second_block;
                        bool valid = true;
                        for (const auto &xx : merged_vertices) {
                            int x = xx.first;
                            bool x_left = xx.second;
                            int to_attach;
                            if (x_left == attach_left) {
                                to_attach = in.distance[x][attach];
                            } else if (x_left) {
                                to_attach =
                                    in.distance[x][first.left_port] + in.mex +
                                    in.distance[first.right_port][attach];
                            } else {
                                to_attach =
                                    in.distance[x][first.right_port] + in.mex +
                                    in.distance[first.left_port][attach];
                            }
                            for (int y : in.components[k]) {
                                int rank = to_attach + second_weight +
                                           in.distance[port_k][y];
                                if (rank < 1 || rank > in.target ||
                                    !in.missing.get(rank) ||
                                    first_block.get(rank) ||
                                    second_block.get(rank)) {
                                    valid = false;
                                    break;
                                }
                                second_block.set(rank);
                            }
                            if (!valid) break;
                        }
                        int demand = static_cast<int>(
                            merged_vertices.size() * in.components[k].size());
                        if (!valid || second_block.count() != demand ||
                            !seen_blocks.insert(second_block).second)
                            continue;
                        std::vector<unsigned char> fixed(families.size(), 0);
                        fixed[owner.family] = 1;
                        fixed[family_index[left][k]] = 1;
                        fixed[family_index[right][k]] = 1;
                        auto status = test_second(fixed, second_block);
                        if (status == detail::MatchingStatus::yes)
                            return {true, Reason::pass};
                        if (status == detail::MatchingStatus::unknown) {
                            ++counters.cap_pass;
                            return {true, Reason::unknown};
                        }
                    }
                }
            }
        }
        ++counters.two_merge_fail;
        return {false, Reason::two_merge_conditioned_hall};
    }
};

} // namespace a2_multi_cover_stronger
