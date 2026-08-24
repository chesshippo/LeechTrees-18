#pragma once

#include "a2_multi_edge_exact_cover.hpp"

#include <algorithm>
#include <cstdint>
#include <limits>
#include <string>
#include <unordered_set>
#include <utility>
#include <vector>

// Isolated prototype of a faster whole-block packing engine.  It deliberately
// does not modify the audited baseline checker.  The mathematical condition
// is identical: choose one pairwise-disjoint candidate block for every
// non-generic component-pair family.
//
// The main improvements are:
//   * identical candidate families are quotient by permutation symmetry;
//   * sound root arc consistency removes blocks that cannot have enough
//     disjoint partners in another (possibly identical) family;
//   * family-union Hall inequalities are evaluated with three-word masks,
//     instead of running a rank-by-rank augmenting matcher at every node;
//   * exact dead states retain the symmetry-class lower bounds, so the cache
//     remains exact.

namespace a2_multi_cover_optimized {

using a2_multi_cover::Input;
using a2_multi_cover::RankMask;
using a2_multi_cover::RankMaskHash;
using a2_multi_cover::Slot;

struct Config {
    int max_components = 6;
    std::uint64_t state_budget = 1000000;
    std::uint64_t root_arc_comparison_budget = 50000000;
    int dynamic_subset_hall_max_classes = 10;
    bool root_arc_consistency = true;
};

struct Counters {
    std::uint64_t checks = 0;
    std::uint64_t skipped = 0;
    std::uint64_t no_candidate_fail = 0;
    std::uint64_t exact_fail = 0;
    std::uint64_t exact_pass = 0;
    std::uint64_t exact_unknown = 0;
    std::uint64_t generated_candidates = 0;
    std::uint64_t raw_families = 0;
    std::uint64_t generic_families = 0;
    std::uint64_t symmetry_classes = 0;
    std::uint64_t symmetry_families_saved = 0;
    std::uint64_t arc_rounds = 0;
    std::uint64_t arc_comparisons = 0;
    std::uint64_t arc_removed = 0;
    std::uint64_t states = 0;
    std::uint64_t memo_hits = 0;
    std::uint64_t local_capacity_fail = 0;
    std::uint64_t subset_hall_calls = 0;
    std::uint64_t subset_hall_fail = 0;
    std::uint64_t budget_unknown = 0;
};

enum class Status { no, yes, unknown };

namespace detail {

inline Slot build_slot(const Input &in, int i, int j, Counters &counters) {
    Slot slot;
    slot.left = i;
    slot.right = j;
    const auto &a = in.components[i];
    const auto &b = in.components[j];
    slot.demand = static_cast<int>(a.size() * b.size());

    if (slot.demand == 1) {
        slot.allowed_ranks = in.missing;
        slot.generic_singleton = true;
        return slot;
    }

    std::vector<RankMask> generated_blocks;
    std::unordered_set<RankMask, RankMaskHash> unique_offsets;
    for (int u : a) for (int v : b) {
        RankMask offsets;
        bool injective = true;
        for (int x : a) for (int y : b) {
            const int offset = in.distance[x][u] + in.distance[v][y];
            if (offset < 0 || offset > in.target || offsets.get(offset)) {
                injective = false;
                break;
            }
            offsets.set(offset);
        }
        if (!injective || !unique_offsets.insert(offsets).second) continue;

        RankMask allowed_length = in.missing;
        for (int offset = 0; offset <= in.target; ++offset)
            if (offsets.get(offset))
                allowed_length &= in.missing.shifted_down(offset);
        allowed_length.clear_outside(1, in.target);
        for (int length = 1; length <= in.target; ++length) {
            if (!allowed_length.get(length)) continue;
            RankMask block = offsets.shifted_up(length);
            if (block.count() == slot.demand &&
                !block.without(in.missing).any())
                generated_blocks.push_back(block);
        }
    }

    std::sort(generated_blocks.begin(), generated_blocks.end(),
              [](const RankMask &a, const RankMask &b) { return a.x < b.x; });
    generated_blocks.erase(
        std::unique(generated_blocks.begin(), generated_blocks.end()),
        generated_blocks.end());
    slot.candidates = std::move(generated_blocks);
    for (const RankMask &block : slot.candidates) slot.allowed_ranks |= block;
    counters.generated_candidates += slot.candidates.size();
    return slot;
}

struct SymmetryClass {
    int demand = 0;
    int multiplicity = 0;
    std::vector<RankMask> candidates;
};

inline bool same_family(const SymmetryClass &a, const Slot &b) {
    return a.demand == b.demand && a.candidates == b.candidates;
}

inline bool subset_hall(const std::vector<SymmetryClass> &classes,
                        const std::vector<int> &remaining,
                        const std::vector<RankMask> &domains,
                        Counters &counters) {
    std::vector<int> live;
    for (int i = 0; i < static_cast<int>(classes.size()); ++i)
        if (remaining[i]) live.push_back(i);
    const int k = static_cast<int>(live.size());
    if (!k) return true;
    if (k >= 63) return true;
    ++counters.subset_hall_calls;

    const std::uint64_t limit = 1ULL << k;
    std::vector<RankMask> unions(limit);
    std::vector<int> needs(limit, 0);
    for (std::uint64_t mask = 1; mask < limit; ++mask) {
        const std::uint64_t bit = mask & (~mask + 1);
        const int local = __builtin_ctzll(bit);
        const std::uint64_t prior = mask ^ bit;
        const int c = live[local];
        unions[mask] = unions[prior] | domains[c];
        needs[mask] = needs[prior] + classes[c].demand * remaining[c];
        if (unions[mask].count() < needs[mask]) {
            ++counters.subset_hall_fail;
            return false;
        }
    }
    return true;
}

struct DeadKeyHash {
    std::size_t operator()(const std::string &s) const noexcept {
        // std::hash<string> is permitted to use every byte (including zero).
        return std::hash<std::string>{}(s);
    }
};

} // namespace detail

inline std::vector<Slot> build_nontrivial_slots(const Input &in,
                                                 Counters &counters,
                                                 bool *impossible = nullptr) {
    if (impossible) *impossible = false;
    std::vector<Slot> slots;
    const int c = static_cast<int>(in.components.size());
    for (int i = 0; i < c; ++i) for (int j = i + 1; j < c; ++j) {
        Slot slot = detail::build_slot(in, i, j, counters);
        ++counters.raw_families;
        if (slot.generic_singleton) {
            ++counters.generic_families;
            continue;
        }
        if (slot.candidates.empty()) {
            if (impossible) *impossible = true;
            return {};
        }
        slots.push_back(std::move(slot));
    }
    return slots;
}

class Solver {
    Config config_;
    Counters &counters_;
    std::vector<detail::SymmetryClass> classes_;
    std::unordered_set<std::string, detail::DeadKeyHash> dead_;
    bool budget_exhausted_ = false;
    std::uint64_t state_limit_ = 0;
    std::uint64_t arc_limit_ = 0;

    static std::string key_of(const RankMask &used,
                              const std::vector<int> &remaining,
                              const std::vector<int> &lower) {
        std::string key;
        key.reserve(24 + remaining.size() * 5);
        for (std::uint64_t word : used.x)
            for (int shift = 0; shift < 64; shift += 8)
                key.push_back(static_cast<char>((word >> shift) & 0xff));
        for (int i = 0; i < static_cast<int>(remaining.size()); ++i) {
            key.push_back(static_cast<char>(remaining[i]));
            const std::uint32_t value = static_cast<std::uint32_t>(lower[i]);
            for (int shift = 0; shift < 32; shift += 8)
                key.push_back(static_cast<char>((value >> shift) & 0xff));
        }
        return key;
    }

    bool root_arc_consistency() {
        if (!config_.root_arc_consistency) return true;
        bool changed = true;
        while (changed) {
            changed = false;
            ++counters_.arc_rounds;
            for (int i = 0; i < static_cast<int>(classes_.size()); ++i) {
                std::vector<RankMask> kept;
                kept.reserve(classes_[i].candidates.size());
                for (const RankMask &candidate : classes_[i].candidates) {
                    bool supported = true;
                    for (int j = 0; j < static_cast<int>(classes_.size()); ++j) {
                        int needed = classes_[j].multiplicity - (i == j ? 1 : 0);
                        if (needed <= 0) continue;
                        int found = 0;
                        bool completed_scan = true;
                        for (const RankMask &other : classes_[j].candidates) {
                            if (counters_.arc_comparisons >= arc_limit_) {
                                completed_scan = false;
                                break;
                            }
                            ++counters_.arc_comparisons;
                            if (!candidate.intersects(other) && ++found >= needed)
                                break;
                        }
                        // Budget exhaustion means unknown support, never
                        // grounds for deleting a candidate.
                        if (!completed_scan) return true;
                        if (found < needed) {
                            supported = false;
                            break;
                        }
                    }
                    if (supported) kept.push_back(candidate);
                    else {
                        ++counters_.arc_removed;
                        changed = true;
                    }
                }
                classes_[i].candidates.swap(kept);
                if (classes_[i].candidates.size() <
                    static_cast<std::size_t>(classes_[i].multiplicity))
                    return false;
            }
        }
        return true;
    }

    Status rec(const RankMask &used, std::vector<int> &remaining,
               std::vector<int> &lower) {
        bool done = true;
        for (int value : remaining) if (value) { done = false; break; }
        if (done) return Status::yes;
        if (counters_.states >= state_limit_) {
            budget_exhausted_ = true;
            return Status::unknown;
        }
        ++counters_.states;

        const std::string key = key_of(used, remaining, lower);
        if (dead_.find(key) != dead_.end()) {
            ++counters_.memo_hits;
            return Status::no;
        }

        int chosen = -1;
        std::uint64_t best_score = std::numeric_limits<std::uint64_t>::max();
        std::vector<std::vector<int>> compatible(classes_.size());
        std::vector<RankMask> domains(classes_.size());
        int live_classes = 0;
        for (int c = 0; c < static_cast<int>(classes_.size()); ++c) {
            if (!remaining[c]) continue;
            ++live_classes;
            const auto &cand = classes_[c].candidates;
            for (int k = lower[c]; k < static_cast<int>(cand.size()); ++k) {
                if (cand[k].intersects(used)) continue;
                compatible[c].push_back(k);
                domains[c] |= cand[k];
            }
            if (compatible[c].size() < static_cast<std::size_t>(remaining[c]) ||
                domains[c].count() < classes_[c].demand * remaining[c]) {
                ++counters_.local_capacity_fail;
                dead_.insert(key);
                return Status::no;
            }
            // Compare binomial branching pressure without overflow.  The
            // slack is primary; multiplicity breaks ties in favor of tighter
            // repeated-family choices.
            const std::uint64_t slack = compatible[c].size() - remaining[c];
            const std::uint64_t score = slack * 256ULL +
                                        static_cast<std::uint64_t>(255 -
                                            std::min(remaining[c], 255));
            if (score < best_score) {
                best_score = score;
                chosen = c;
            }
        }

        if (live_classes <= config_.dynamic_subset_hall_max_classes &&
            !detail::subset_hall(classes_, remaining, domains, counters_)) {
            dead_.insert(key);
            return Status::no;
        }

        bool saw_unknown = false;
        const int old_remaining = remaining[chosen];
        const int old_lower = lower[chosen];
        for (int index : compatible[chosen]) {
            remaining[chosen] = old_remaining - 1;
            lower[chosen] = index + 1;
            Status child = rec(used | classes_[chosen].candidates[index],
                               remaining, lower);
            remaining[chosen] = old_remaining;
            lower[chosen] = old_lower;
            if (child == Status::yes) return child;
            if (child == Status::unknown) saw_unknown = true;
        }
        if (saw_unknown) return Status::unknown;
        dead_.insert(key);
        return Status::no;
    }

  public:
    Solver(const std::vector<Slot> &slots, const Config &config,
           Counters &counters)
        : config_(config), counters_(counters),
          state_limit_(counters.states + config.state_budget),
          arc_limit_(counters.arc_comparisons +
                     config.root_arc_comparison_budget) {
        for (const Slot &slot : slots) {
            int found = -1;
            for (int c = 0; c < static_cast<int>(classes_.size()); ++c)
                if (detail::same_family(classes_[c], slot)) {
                    found = c;
                    break;
                }
            if (found < 0) {
                detail::SymmetryClass z;
                z.demand = slot.demand;
                z.multiplicity = 1;
                z.candidates = slot.candidates;
                classes_.push_back(std::move(z));
            } else {
                ++classes_[found].multiplicity;
                ++counters_.symmetry_families_saved;
            }
        }
        counters_.symmetry_classes += classes_.size();
    }

    Status run() {
        if (classes_.empty()) return Status::yes;
        if (!root_arc_consistency()) return Status::no;
        std::vector<int> remaining, lower(classes_.size(), 0);
        for (const auto &z : classes_) remaining.push_back(z.multiplicity);
        RankMask empty;
        Status result = rec(empty, remaining, lower);
        if (result == Status::unknown) ++counters_.budget_unknown;
        return result;
    }
};

struct Outcome {
    bool possible = true;
    Status status = Status::yes;
};

class Checker {
  public:
    Outcome check(const Input &in, const Config &config,
                  Counters &counters) const {
        ++counters.checks;
        const int component_count = static_cast<int>(in.components.size());
        if (component_count <= 1) return {true, Status::yes};
        if (component_count > config.max_components) {
            ++counters.skipped;
            return {true, Status::yes};
        }
        if (in.target < 1 || in.target >= 64 * RankMask::words)
            throw std::logic_error("optimized exact-cover target out of range");
        int expected_missing = 0;
        for (int i = 0; i < component_count; ++i)
            for (int j = i + 1; j < component_count; ++j)
                expected_missing += static_cast<int>(
                    in.components[i].size() * in.components[j].size());
        if (expected_missing != in.missing.count())
            throw std::logic_error(
                "optimized exact-cover cross-pair/missing mismatch");

        bool impossible = false;
        auto slots = build_nontrivial_slots(in, counters, &impossible);
        if (impossible) {
            ++counters.no_candidate_fail;
            return {false, Status::no};
        }
        Solver solver(slots, config, counters);
        Status status = solver.run();
        if (status == Status::no) {
            ++counters.exact_fail;
            return {false, status};
        }
        if (status == Status::unknown) {
            ++counters.exact_unknown;
            return {true, status};
        }
        ++counters.exact_pass;
        return {true, status};
    }
};

} // namespace a2_multi_cover_optimized
