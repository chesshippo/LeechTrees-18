#pragma once

#include <algorithm>
#include <array>
#include <cstdint>
#include <functional>
#include <limits>
#include <stdexcept>
#include <unordered_set>
#include <utility>
#include <vector>

// Experimental, topology-independent multi-block exact-cover pruning.
//
// The topology-free solver wires this checker behind independent active and
// shadow flags.  Both are off by default, preserving baseline behavior.
//
// Mathematical contract.  Let K_i be the components of a valid prefix
// forest.  In any completion, and for every i < j, the path from K_i to K_j
// has a first port u in K_i, a last port v in K_j, and a port-to-port length L.
// Hence its indexed cross-distance block is
//
//   { d_i(x,u) + L + d_j(v,y) : x in K_i, y in K_j }.
//
// L and every member of this block are currently missing ranks.  The blocks
// for all unordered component pairs are disjoint and, by cardinality, exactly
// cover all currently missing ranks.  The checker below enumerates every
// possible additive block for each component pair.  Failure of either its
// capacitated Hall relaxation or its exact block-cover search is therefore a
// sound reason to prune.  Passing is only a relaxation: ports and lengths
// chosen for different component pairs need not come from one common tree.

namespace a2_multi_cover {

struct RankMask {
    static constexpr int words = 3; // ranks 0..191; order 18 needs 0..153
    std::array<std::uint64_t, words> x{{0, 0, 0}};

    bool get(int bit) const {
        return bit >= 0 && bit < 64 * words &&
               ((x[bit >> 6] >> (bit & 63)) & 1ULL);
    }
    void set(int bit) {
        if (bit >= 0 && bit < 64 * words)
            x[bit >> 6] |= 1ULL << (bit & 63);
    }
    void reset(int bit) {
        if (bit >= 0 && bit < 64 * words)
            x[bit >> 6] &= ~(1ULL << (bit & 63));
    }
    bool any() const { return x[0] || x[1] || x[2]; }
    int count() const {
        return __builtin_popcountll(x[0]) + __builtin_popcountll(x[1]) +
               __builtin_popcountll(x[2]);
    }
    bool intersects(const RankMask &other) const {
        return (x[0] & other.x[0]) || (x[1] & other.x[1]) ||
               (x[2] & other.x[2]);
    }
    bool operator==(const RankMask &other) const { return x == other.x; }
    bool operator!=(const RankMask &other) const { return !(*this == other); }
    RankMask &operator|=(const RankMask &other) {
        for (int i = 0; i < words; ++i) x[i] |= other.x[i];
        return *this;
    }
    RankMask &operator&=(const RankMask &other) {
        for (int i = 0; i < words; ++i) x[i] &= other.x[i];
        return *this;
    }
    friend RankMask operator|(RankMask a, const RankMask &b) { return a |= b; }
    friend RankMask operator&(RankMask a, const RankMask &b) { return a &= b; }

    RankMask without(const RankMask &other) const {
        RankMask z;
        for (int i = 0; i < words; ++i) z.x[i] = x[i] & ~other.x[i];
        return z;
    }

    // Move bit r to r+amount.  Bits outside the fixed mask are discarded.
    RankMask shifted_up(int amount) const {
        RankMask z;
        if (amount < 0 || amount >= 64 * words) return z;
        const int whole = amount >> 6, part = amount & 63;
        for (int src = 0; src < words; ++src) {
            int dst = src + whole;
            if (dst >= words) continue;
            z.x[dst] |= x[src] << part;
            if (part && dst + 1 < words) z.x[dst + 1] |= x[src] >> (64 - part);
        }
        return z;
    }

    // Move bit r to r-amount.  Thus output bit L is set precisely when input
    // bit L+amount was set.
    RankMask shifted_down(int amount) const {
        RankMask z;
        if (amount < 0 || amount >= 64 * words) return z;
        const int whole = amount >> 6, part = amount & 63;
        for (int dst = 0; dst < words; ++dst) {
            int src = dst + whole;
            if (src >= words) continue;
            z.x[dst] |= x[src] >> part;
            if (part && src + 1 < words) z.x[dst] |= x[src + 1] << (64 - part);
        }
        return z;
    }

    void clear_outside(int lo, int hi) {
        for (int r = 0; r < 64 * words; ++r)
            if (r < lo || r > hi) reset(r);
    }
};

struct RankMaskHash {
    std::size_t operator()(const RankMask &m) const noexcept {
        std::size_t h = 0x9e3779b97f4a7c15ULL;
        for (std::uint64_t v : m.x) {
            v ^= v >> 30;
            v *= 0xbf58476d1ce4e5b9ULL;
            v ^= v >> 27;
            v *= 0x94d049bb133111ebULL;
            v ^= v >> 31;
            h ^= static_cast<std::size_t>(v) + 0x9e3779b9 + (h << 6) + (h >> 2);
        }
        return h;
    }
};

struct Input {
    int n = 0;
    int target = 0;
    int mex = 1;
    std::vector<std::vector<int>> components;
    std::array<std::array<int, 18>, 18> distance{};
    RankMask missing;
};

struct Config {
    // The inexpensive test that every component pair has at least one rooted
    // additive block can run earlier than materializing every candidate.
    int local_max_components = 9;
    // Full candidate construction and capacitated Hall start this late.
    int max_components = 7;
    // Exact Algorithm-X/DP is attempted only this late.  Hall still runs up
    // to max_components.
    int exact_max_components = 6;
    std::uint64_t exact_state_budget = 100000;
    std::size_t exact_candidate_cap = 50000;
    bool run_hall = true;
    bool run_exact = true;
    // Residual capacitated Hall at every DP node is strong but can dominate
    // runtime.  Disabling it only weakens pruning; exhaustive DP failures and
    // budget-as-UNKNOWN behavior remain sound.
    bool exact_residual_hall = true;
    // Recompute all candidates by scalar loops and compare them to the mask
    // generator.  Intended only for tests and small-order validation.
    bool validate_candidates = false;
};

struct Counters {
    std::uint64_t checks = 0;
    std::uint64_t skipped_early = 0;
    std::uint64_t skipped_full = 0;
    std::uint64_t local_component_pair_slots = 0;
    std::uint64_t local_port_patterns = 0;
    std::uint64_t component_pair_slots = 0;
    std::uint64_t port_patterns = 0;
    std::uint64_t candidate_blocks = 0;
    std::uint64_t no_candidate_fail = 0;
    std::uint64_t hall_fail = 0;
    std::uint64_t hall_calls = 0;
    std::uint64_t exact_calls = 0;
    std::uint64_t exact_fail = 0;
    std::uint64_t exact_pass = 0;
    std::uint64_t exact_budget_pass = 0;
    std::uint64_t exact_cap_pass = 0;
    std::uint64_t exact_states = 0;
    std::uint64_t exact_hall_fail = 0;
    std::uint64_t validation_fail = 0;
};

enum class Reason {
    pass,
    skipped,
    no_candidate,
    hall,
    exact_cover,
    exact_unknown
};

struct Outcome {
    bool possible = true;
    Reason reason = Reason::pass;
};

struct Slot {
    int left = -1, right = -1;
    int demand = 0;
    RankMask allowed_ranks;
    std::vector<RankMask> candidates;
    bool generic_singleton = false;
};

namespace detail {

inline bool rank_hall_possible(const std::vector<const Slot *> &slots,
                               const std::vector<RankMask> &domains,
                               int target) {
    int total = 0;
    std::vector<int> slot_order(slots.size());
    for (int i = 0; i < static_cast<int>(slots.size()); ++i) {
        total += slots[i]->demand;
        slot_order[i] = i;
        if (domains[i].count() < slots[i]->demand) return false;
    }
    if (!total) return true;

    // Tight domains first usually makes the augmenting matcher substantially
    // faster and does not affect its exactness.
    std::sort(slot_order.begin(), slot_order.end(), [&](int a, int b) {
        int slack_a = domains[a].count() - slots[a]->demand;
        int slack_b = domains[b].count() - slots[b]->demand;
        if (slack_a != slack_b) return slack_a < slack_b;
        return slots[a]->demand > slots[b]->demand;
    });

    std::vector<int> clone_slot;
    clone_slot.reserve(total);
    for (int s : slot_order)
        for (int k = 0; k < slots[s]->demand; ++k) clone_slot.push_back(s);

    std::vector<int> owner(target + 1, -1);
    std::function<bool(int, std::vector<unsigned char> &)> augment =
        [&](int clone, std::vector<unsigned char> &seen_rank) {
            int s = clone_slot[clone];
            for (int r = 1; r <= target; ++r) {
                if (!domains[s].get(r) || seen_rank[r]) continue;
                seen_rank[r] = 1;
                if (owner[r] < 0 || augment(owner[r], seen_rank)) {
                    owner[r] = clone;
                    return true;
                }
            }
            return false;
        };

    for (int clone = 0; clone < static_cast<int>(clone_slot.size()); ++clone) {
        std::vector<unsigned char> seen_rank(target + 1, 0);
        if (!augment(clone, seen_rank)) return false;
    }
    return true;
}

struct DeadKey {
    std::uint64_t remaining = 0;
    RankMask used;
    bool operator==(const DeadKey &other) const {
        return remaining == other.remaining && used == other.used;
    }
};

struct DeadKeyHash {
    std::size_t operator()(const DeadKey &k) const noexcept {
        std::size_t h = RankMaskHash{}(k.used);
        h ^= static_cast<std::size_t>(k.remaining) + 0x9e3779b9 + (h << 6) +
             (h >> 2);
        return h;
    }
};

enum class ExactStatus { no, yes, unknown };

class ExactSolver {
    const std::vector<const Slot *> &slots_;
    int target_;
    std::uint64_t budget_;
    Counters &counters_;
    bool residual_hall_;
    std::unordered_set<DeadKey, DeadKeyHash> dead_;
    bool exhausted_budget_ = false;

    ExactStatus rec(std::uint64_t remaining, const RankMask &used) {
        if (!remaining) return ExactStatus::yes;
        if (counters_.exact_states >= budget_) {
            exhausted_budget_ = true;
            return ExactStatus::unknown;
        }
        ++counters_.exact_states;

        DeadKey key{remaining, used};
        if (dead_.find(key) != dead_.end()) return ExactStatus::no;

        int chosen = -1;
        std::size_t best_count = std::numeric_limits<std::size_t>::max();
        std::vector<RankMask> domains(slots_.size());
        std::vector<const Slot *> hall_slots;
        std::vector<RankMask> hall_domains;

        for (int s = 0; s < static_cast<int>(slots_.size()); ++s) {
            if (!(remaining & (1ULL << s))) continue;
            std::size_t compatible = 0;
            RankMask domain;
            for (const RankMask &block : slots_[s]->candidates) {
                if (block.intersects(used)) continue;
                ++compatible;
                domain |= block;
            }
            if (!compatible) {
                dead_.insert(key);
                return ExactStatus::no;
            }
            domains[s] = domain;
            hall_slots.push_back(slots_[s]);
            hall_domains.push_back(domain);
            if (compatible < best_count ||
                (compatible == best_count &&
                 (chosen < 0 || slots_[s]->demand > slots_[chosen]->demand))) {
                chosen = s;
                best_count = compatible;
            }
        }

        if (residual_hall_) {
            ++counters_.hall_calls;
            if (!rank_hall_possible(hall_slots, hall_domains, target_)) {
                ++counters_.exact_hall_fail;
                dead_.insert(key);
                return ExactStatus::no;
            }
        }

        bool saw_unknown = false;
        for (const RankMask &block : slots_[chosen]->candidates) {
            if (block.intersects(used)) continue;
            RankMask next_used = used | block;
            ExactStatus child = rec(remaining & ~(1ULL << chosen), next_used);
            if (child == ExactStatus::yes) return child;
            if (child == ExactStatus::unknown) saw_unknown = true;
        }
        if (saw_unknown) return ExactStatus::unknown;
        dead_.insert(key);
        return ExactStatus::no;
    }

  public:
    ExactSolver(const std::vector<const Slot *> &slots, int target,
                std::uint64_t budget, Counters &counters,
                bool residual_hall = true)
        : slots_(slots), target_(target), budget_(budget), counters_(counters),
          residual_hall_(residual_hall) {}

    ExactStatus run() {
        if (slots_.empty()) return ExactStatus::yes;
        if (slots_.size() > 63) return ExactStatus::unknown;
        return rec((1ULL << slots_.size()) - 1, RankMask{});
    }
};

inline std::vector<RankMask> scalar_candidates(const Input &in,
                                                const std::vector<int> &a,
                                                const std::vector<int> &b) {
    std::unordered_set<RankMask, RankMaskHash> unique;
    for (int u : a) for (int v : b) {
        for (int length = 1; length <= in.target; ++length) {
            RankMask block;
            bool ok = true;
            for (int x : a) for (int y : b) {
                int rank = in.distance[x][u] + length + in.distance[v][y];
                if (rank < 1 || rank > in.target || !in.missing.get(rank) ||
                    block.get(rank)) {
                    ok = false;
                    break;
                }
                block.set(rank);
            }
            if (ok) unique.insert(block);
        }
    }
    return std::vector<RankMask>(unique.begin(), unique.end());
}

} // namespace detail

class Checker {
    static bool slot_has_candidate(const Input &in, int i, int j,
                                   Counters &counters) {
        const auto &a = in.components[i];
        const auto &b = in.components[j];
        for (int u : a) for (int v : b) {
            RankMask offsets;
            bool injective = true;
            for (int x : a) for (int y : b) {
                int offset = in.distance[x][u] + in.distance[v][y];
                if (offset < 0 || offset > in.target || offsets.get(offset)) {
                    injective = false;
                    break;
                }
                offsets.set(offset);
            }
            if (!injective) continue;
            ++counters.local_port_patterns;
            RankMask allowed_length = in.missing;
            for (int offset = 0; offset <= in.target; ++offset)
                if (offsets.get(offset))
                    allowed_length &= in.missing.shifted_down(offset);
            allowed_length.clear_outside(1, in.target);
            if (allowed_length.any()) return true;
        }
        return false;
    }

    static Slot build_slot(const Input &in, int i, int j, Counters &counters,
                           bool validate) {
        Slot slot;
        slot.left = i;
        slot.right = j;
        const auto &a = in.components[i];
        const auto &b = in.components[j];
        slot.demand = static_cast<int>(a.size() * b.size());

        // A singleton--singleton family can choose any one missing rank and
        // is eliminated analytically from Hall/exact packing later.  Avoid
        // materializing one one-bit candidate per missing rank.
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
                int offset = in.distance[x][u] + in.distance[v][y];
                if (offset < 0 || offset > in.target || offsets.get(offset)) {
                    injective = false;
                    break;
                }
                offsets.set(offset);
            }
            if (!injective || !unique_offsets.insert(offsets).second) continue;
            ++counters.port_patterns;

            // length is allowed iff length+offset is missing for every offset.
            RankMask allowed_length = in.missing;
            for (int offset = 0; offset <= in.target; ++offset)
                if (offsets.get(offset)) allowed_length &= in.missing.shifted_down(offset);
            allowed_length.clear_outside(1, in.target);

            for (int length = 1; length <= in.target; ++length) {
                if (!allowed_length.get(length)) continue;
                RankMask block = offsets.shifted_up(length);
                // The intersection construction should make these assertions
                // redundant; retaining them protects future mask refactors.
                if (block.count() != slot.demand ||
                    block.without(in.missing).any())
                    throw std::logic_error("invalid generated cross block");
                generated_blocks.push_back(block);
            }
        }
        std::sort(generated_blocks.begin(), generated_blocks.end(),
                  [](const RankMask &p, const RankMask &q) { return p.x < q.x; });
        generated_blocks.erase(
            std::unique(generated_blocks.begin(), generated_blocks.end()),
            generated_blocks.end());
        slot.candidates=std::move(generated_blocks);
        for (const RankMask &block : slot.candidates) slot.allowed_ranks |= block;

        if (validate) {
            auto slow = detail::scalar_candidates(in, a, b);
            std::unordered_set<RankMask, RankMaskHash> slow_set(slow.begin(), slow.end());
            if (slow_set.size() != slot.candidates.size()) {
                ++counters.validation_fail;
                throw std::logic_error("candidate mask/scalar size mismatch");
            }
            for (const RankMask &block : slot.candidates)
                if (slow_set.find(block) == slow_set.end()) {
                    ++counters.validation_fail;
                    throw std::logic_error("candidate mask/scalar content mismatch");
                }
        }
        counters.candidate_blocks += slot.candidates.size();
        return slot;
    }

  public:
    Outcome check(const Input &in, const Config &config, Counters &counters) const {
        ++counters.checks;
        if (in.target < 1 || in.target >= 64 * RankMask::words)
            throw std::logic_error("rank mask target out of range");
        const int component_count = static_cast<int>(in.components.size());
        if (component_count <= 1) return {true, Reason::pass};
        if (component_count > std::max(config.local_max_components,
                                       config.max_components)) {
            ++counters.skipped_early;
            return {true, Reason::skipped};
        }

        int expected_missing = 0;
        for (int i = 0; i < component_count; ++i)
            for (int j = i + 1; j < component_count; ++j)
                expected_missing += static_cast<int>(in.components[i].size() *
                                                     in.components[j].size());
        if (expected_missing != in.missing.count())
            throw std::logic_error("prefix cross-pair/missing-rank count mismatch");

        if (component_count > config.max_components) {
            // Preflight only asks whether each current component pair admits
            // one internally injective block inside the punctured missing set.
            for (int i = 0; i < component_count; ++i) {
                for (int j = i + 1; j < component_count; ++j) {
                    ++counters.local_component_pair_slots;
                    if (!slot_has_candidate(in, i, j, counters)) {
                        ++counters.no_candidate_fail;
                        return {false, Reason::no_candidate};
                    }
                }
            }
            ++counters.skipped_full;
            return {true, Reason::pass};
        }

        std::vector<Slot> slots;
        slots.reserve(component_count * (component_count - 1) / 2);
        for (int i = 0; i < component_count; ++i) {
            for (int j = i + 1; j < component_count; ++j) {
                slots.push_back(build_slot(in, i, j, counters,
                                           config.validate_candidates));
                ++counters.component_pair_slots;
                if (!slots.back().generic_singleton &&
                    slots.back().candidates.empty()) {
                    ++counters.no_candidate_fail;
                    return {false, Reason::no_candidate};
                }
            }
        }

        // Singleton-singleton slots can consume any one missing rank.  Once
        // all nontrivial blocks have been injected, these generic slots fill
        // precisely the leftover ranks, so they may be omitted from Hall and
        // exact search without weakening soundness.
        std::vector<const Slot *> nontrivial;
        std::vector<RankMask> domains;
        std::size_t candidates = 0;
        for (const Slot &slot : slots) {
            if (slot.generic_singleton) continue;
            nontrivial.push_back(&slot);
            domains.push_back(slot.allowed_ranks);
            candidates += slot.candidates.size();
        }

        if (config.run_hall) {
            ++counters.hall_calls;
            if (!detail::rank_hall_possible(nontrivial, domains, in.target)) {
                ++counters.hall_fail;
                return {false, Reason::hall};
            }
        }

        if (!config.run_exact || component_count > config.exact_max_components)
            return {true, Reason::pass};
        if (candidates > config.exact_candidate_cap || nontrivial.size() > 63) {
            ++counters.exact_cap_pass;
            return {true, Reason::exact_unknown};
        }

        ++counters.exact_calls;
        std::uint64_t before = counters.exact_states;
        detail::ExactSolver solver(nontrivial, in.target,
                                   before + config.exact_state_budget, counters,
                                   config.exact_residual_hall);
        detail::ExactStatus status = solver.run();
        if (status == detail::ExactStatus::no) {
            ++counters.exact_fail;
            return {false, Reason::exact_cover};
        }
        if (status == detail::ExactStatus::unknown) {
            ++counters.exact_budget_pass;
            return {true, Reason::exact_unknown};
        }
        ++counters.exact_pass;
        return {true, Reason::pass};
    }
};

} // namespace a2_multi_cover
