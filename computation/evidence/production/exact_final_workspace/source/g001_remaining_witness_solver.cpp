#ifdef _WIN32
#ifndef NOMINMAX
#define NOMINMAX 1
#endif
#include <windows.h>
#endif

#define main frozen_order18_topology_free_search_main
#include "order18_topology_free_search.cpp"
#undef main

#include <atomic>
#include <cerrno>
#include <chrono>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <sstream>
#include <system_error>

#ifndef _WIN32
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
#endif

// Production-safety wrapper for the five unresolved G001 configurations.
//
// The search and every pruning predicate come from the frozen solver included
// above.  WitnessSearch repeats only its recursive dispatcher so that a full
// terminal edge set can be serialized and durably installed before recursion
// removes any edge.  The ordinary frozen source is not modified.

namespace g001_witness {

namespace fs = std::filesystem;

constexpr int kUsageExit = 64;
constexpr int kInternalExit = 70;
constexpr int kIoExit = 74;

struct Configuration {
    int external = -1;
    std::string mode;
};

bool configuration_from_external(int external, Configuration &out) {
    switch (external) {
    case 1: out = {1, "g001_row0"}; return true;
    case 4: out = {4, "g001_row3"}; return true;
    case 5: out = {5, "g001_row4"}; return true;
    case 6: out = {6, "g001_row5"}; return true;
    case 7: out = {7, "g001_row6"}; return true;
    default: return false;
    }
}

bool configuration_from_mode(const std::string &mode, Configuration &out) {
    if (mode == "g001_row0") { out = {1, mode}; return true; }
    if (mode == "g001_row3") { out = {4, mode}; return true; }
    if (mode == "g001_row4") { out = {5, mode}; return true; }
    if (mode == "g001_row5") { out = {6, mode}; return true; }
    if (mode == "g001_row6") { out = {7, mode}; return true; }
    return false;
}

bool parse_nonnegative_int(const std::string &text, int &value) {
    if (text.empty()) return false;
    std::size_t consumed = 0;
    try {
        const long long parsed = std::stoll(text, &consumed);
        if (consumed != text.size() || parsed < 0 ||
            parsed > std::numeric_limits<int>::max()) return false;
        value = static_cast<int>(parsed);
        return true;
    } catch (...) {
        return false;
    }
}

bool parse_nonnegative_u64(const std::string &text, std::uint64_t &value) {
    if (text.empty() || text.front() == '-') return false;
    std::size_t consumed = 0;
    try {
        const unsigned long long parsed = std::stoull(text, &consumed);
        if (consumed != text.size()) return false;
        value = static_cast<std::uint64_t>(parsed);
        return true;
    } catch (...) {
        return false;
    }
}

bool parse_branch_path(const std::string &text, std::vector<int> &path) {
    if (text.empty()) return false;
    std::stringstream stream(text);
    std::string item;
    while (std::getline(stream, item, ',')) {
        int branch = -1;
        if (!parse_nonnegative_int(item, branch)) return false;
        path.push_back(branch);
    }
    return !path.empty();
}

int initialize_seed(Search &search, const std::string &mode) {
    if (mode == "g001_row0") {
        search.add_edge(0, 1, 1);
        search.add_edge(1, 2, 2);
        search.add_edge(3, 4, 4);
        return 5;
    }
    if (mode == "g001_row3") {
        search.add_edge(0, 1, 1);
        search.add_edge(0, 2, 2);
        search.add_edge(0, 3, 4);
        return 7;
    }
    if (mode == "g001_row4") {
        search.add_edge(0, 1, 1);
        search.add_edge(2, 3, 2);
        search.add_edge(4, 5, 3);
        return 4;
    }
    if (mode == "g001_row5") {
        search.add_edge(0, 1, 1);
        search.add_edge(3, 4, 2);
        search.add_edge(1, 2, 3);
        return 5;
    }
    if (mode == "g001_row6") {
        search.add_edge(0, 1, 1);
        search.add_edge(2, 3, 2);
        search.add_edge(3, 4, 3);
        return 4;
    }
    return -1;
}

std::string serialize_witness(const Configuration &configuration,
                              const std::vector<Edge> &edges,
                              std::string &error) {
    if (edges.size() != 17U) {
        error = "internal witness has " + std::to_string(edges.size()) +
                " edges instead of 17";
        return {};
    }
    int previous_weight = 0;
    for (const Edge &edge : edges) {
        if (edge.u < 0 || edge.u >= 18 || edge.v < 0 || edge.v >= 18 ||
            edge.u == edge.v || edge.w <= previous_weight) {
            error = "internal witness edge order or endpoint validation failed";
            return {};
        }
        previous_weight = edge.w;
    }

    std::ostringstream out;
    out << "LEECH_WITNESS_V1\n"
        << "configuration " << configuration.external << "\n"
        << "mode " << configuration.mode << "\n"
        << "vertices 18\n"
        << "edges 17\n";
    for (const Edge &edge : edges)
        out << "edge " << edge.u << ' ' << edge.v << ' ' << edge.w << '\n';
    out << "end\n";
    return out.str();
}

std::string process_token() {
    static std::atomic<std::uint64_t> serial{0};
    const auto tick = std::chrono::high_resolution_clock::now()
                          .time_since_epoch().count();
#ifdef _WIN32
    const auto pid = static_cast<unsigned long long>(GetCurrentProcessId());
#else
    const auto pid = static_cast<unsigned long long>(::getpid());
#endif
    return std::to_string(pid) + "." + std::to_string(tick) + "." +
           std::to_string(serial.fetch_add(1, std::memory_order_relaxed));
}

bool target_is_new_and_parent_exists(const fs::path &target,
                                     std::string &error) {
    if (target.empty() || target.filename().empty()) {
        error = "--witness-file must name a file";
        return false;
    }
    std::error_code ec;
    const fs::file_status target_status = fs::symlink_status(target, ec);
    if (ec && ec != std::errc::no_such_file_or_directory) {
        error = "cannot inspect witness target: " + ec.message();
        return false;
    }
    if (!ec && target_status.type() != fs::file_type::not_found) {
        error = "witness target already exists; a unique path is required";
        return false;
    }
    fs::path parent = target.parent_path();
    if (parent.empty()) parent = ".";
    ec.clear();
    if (!fs::is_directory(parent, ec) || ec) {
        error = "witness parent directory does not exist or is inaccessible";
        if (ec) error += ": " + ec.message();
        return false;
    }
    return true;
}

#ifdef _WIN32

std::string windows_error_message(DWORD code) {
    LPWSTR buffer = nullptr;
    const DWORD flags = FORMAT_MESSAGE_ALLOCATE_BUFFER |
                        FORMAT_MESSAGE_FROM_SYSTEM |
                        FORMAT_MESSAGE_IGNORE_INSERTS;
    const DWORD length = FormatMessageW(
        flags, nullptr, code, 0, reinterpret_cast<LPWSTR>(&buffer), 0, nullptr);
    std::string result = "Windows error " + std::to_string(code);
    if (length && buffer) {
        const int bytes = WideCharToMultiByte(CP_UTF8, 0, buffer,
                                               static_cast<int>(length),
                                               nullptr, 0, nullptr, nullptr);
        if (bytes > 0) {
            std::string text(static_cast<std::size_t>(bytes), '\0');
            WideCharToMultiByte(CP_UTF8, 0, buffer, static_cast<int>(length),
                                text.data(), bytes, nullptr, nullptr);
            while (!text.empty() &&
                   (text.back() == '\r' || text.back() == '\n' ||
                    text.back() == ' ')) text.pop_back();
            result += ": " + text;
        }
    }
    if (buffer) LocalFree(buffer);
    return result;
}

bool durable_atomic_write_new(const fs::path &target, const std::string &data,
                              std::string &error) {
    if (!target_is_new_and_parent_exists(target, error)) return false;
    const fs::path temporary = target.parent_path() /
        (target.filename().wstring() + L".tmp." +
         fs::path(process_token()).wstring());

    HANDLE file = CreateFileW(temporary.c_str(), GENERIC_WRITE, 0, nullptr,
                              CREATE_NEW, FILE_ATTRIBUTE_NORMAL, nullptr);
    if (file == INVALID_HANDLE_VALUE) {
        error = "cannot create temporary witness: " +
                windows_error_message(GetLastError());
        return false;
    }

    bool ok = true;
    std::size_t offset = 0;
    while (offset < data.size()) {
        const std::size_t left = data.size() - offset;
        const DWORD chunk = static_cast<DWORD>(
            std::min<std::size_t>(left, std::numeric_limits<DWORD>::max()));
        DWORD written = 0;
        if (!WriteFile(file, data.data() + offset, chunk, &written, nullptr) ||
            written == 0) {
            error = "cannot write temporary witness: " +
                    windows_error_message(GetLastError());
            ok = false;
            break;
        }
        offset += written;
    }
    if (ok && !FlushFileBuffers(file)) {
        error = "cannot flush temporary witness: " +
                windows_error_message(GetLastError());
        ok = false;
    }
    if (!CloseHandle(file) && ok) {
        error = "cannot close temporary witness: " +
                windows_error_message(GetLastError());
        ok = false;
    }
    if (!ok) {
        DeleteFileW(temporary.c_str());
        return false;
    }
    if (!MoveFileExW(temporary.c_str(), target.c_str(),
                     MOVEFILE_WRITE_THROUGH)) {
        error = "cannot atomically install witness without overwriting: " +
                windows_error_message(GetLastError());
        DeleteFileW(temporary.c_str());
        return false;
    }
    return true;
}

#else

std::string errno_message(int code) {
    return std::error_code(code, std::generic_category()).message();
}

bool write_all(int descriptor, const std::string &data, std::string &error) {
    std::size_t offset = 0;
    while (offset < data.size()) {
        const ssize_t written = ::write(descriptor, data.data() + offset,
                                        data.size() - offset);
        if (written < 0) {
            if (errno == EINTR) continue;
            error = "cannot write temporary witness: " + errno_message(errno);
            return false;
        }
        if (written == 0) {
            error = "zero-byte write while saving witness";
            return false;
        }
        offset += static_cast<std::size_t>(written);
    }
    return true;
}

bool durable_atomic_write_new(const fs::path &target, const std::string &data,
                              std::string &error) {
    if (!target_is_new_and_parent_exists(target, error)) return false;
    const fs::path temporary = target.parent_path() /
        (target.filename().string() + ".tmp." + process_token());

    const int descriptor = ::open(temporary.c_str(),
                                  O_WRONLY | O_CREAT | O_EXCL, 0600);
    if (descriptor < 0) {
        error = "cannot create temporary witness: " + errno_message(errno);
        return false;
    }

    bool ok = write_all(descriptor, data, error);
    if (ok && ::fsync(descriptor) != 0) {
        error = "cannot fsync temporary witness: " + errno_message(errno);
        ok = false;
    }
    if (::close(descriptor) != 0 && ok) {
        error = "cannot close temporary witness: " + errno_message(errno);
        ok = false;
    }
    if (!ok) {
        ::unlink(temporary.c_str());
        return false;
    }

    // link(2) is an atomic no-replace install on the same filesystem.  It
    // prevents two shards that accidentally share a target from clobbering a
    // certificate.  The temporary file lives beside the target by design.
    if (::link(temporary.c_str(), target.c_str()) != 0) {
        error = "cannot atomically install witness without overwriting: " +
                errno_message(errno);
        ::unlink(temporary.c_str());
        return false;
    }

    fs::path parent = target.parent_path();
    if (parent.empty()) parent = ".";
    const int directory = ::open(parent.c_str(), O_RDONLY
#ifdef O_DIRECTORY
                                 | O_DIRECTORY
#endif
    );
    if (directory < 0 || ::fsync(directory) != 0) {
        const int saved_errno = errno;
        if (directory >= 0) ::close(directory);
        ::unlink(temporary.c_str());
        error = "witness was installed but its directory could not be "
                "fsynced: " + errno_message(saved_errno);
        return false;
    }
    if (::close(directory) != 0) {
        ::unlink(temporary.c_str());
        error = "cannot close witness directory: " + errno_message(errno);
        return false;
    }
    if (::unlink(temporary.c_str()) != 0) {
        // The durable target is already installed.  A leftover hard-link is
        // harmless and must not turn a safely recorded discovery into ZERO.
        std::cerr << "warning: durable witness installed but temporary link "
                     "could not be removed: " << errno_message(errno) << '\n';
    }
    return true;
}

#endif

struct WitnessSearch : Search {
    Configuration configuration;
    fs::path witness_path;
    bool witness_saved = false;
    bool witness_io_failed = false;
    std::string witness_error;

    WitnessSearch(Configuration selected, fs::path output)
        : Search(18), configuration(std::move(selected)),
          witness_path(std::move(output)) {}

    bool save_terminal_witness() {
        std::string serialization_error;
        const std::string text =
            serialize_witness(configuration, edges, serialization_error);
        if (text.empty()) {
            witness_io_failed = true;
            witness_error = serialization_error;
            return false;
        }
        if (!durable_atomic_write_new(witness_path, text, witness_error)) {
            witness_io_failed = true;
            return false;
        }
        witness_saved = true;
        return true;
    }

    // Kept mechanically parallel to Search::rec in the frozen source.  The
    // only semantic change is the terminal block marked below.
    bool rec_with_witness() {
        nodes++;
        if (max_nodes && nodes > max_nodes) { limit = true; return false; }
        depth_nodes[edges.size()]++;
        Analysis z = analyze();
        if (!z.valid) return false;
        if (!partial_hop_diameter_ok(z)) { diameter_fail++; return false; }
        if (!parity_profile_possible(z)) { parity_fail++; return false; }
        if (!equality_profile_possible()) return false;
        if (use_late_t9a && !late_t9a_profile_possible(z)) {
            late_t9a_fail++;
            return false;
        }
        if (use_structural_bounds) {
            const int failed = structural_cut_bounds(z);
            if (failed == 1) { g002_fail++; return false; }
            if (failed == 2) { cut_lower_fail++; return false; }
            if (failed == 3) { cut_upper_fail++; return false; }
        }
        const int selected_equality_r = attached_equality_r >= 0
            ? attached_equality_r : separate_equality_r;
        if (selected_equality_r >= 0 && static_cast<int>(edges.size()) < 17) {
            int odd = 0;
            for (const Edge &edge : edges) odd += edge.w & 1;
            const int remaining = 17 - static_cast<int>(edges.size());
            const int need_odd = selected_equality_r - odd;
            const int need_even = remaining - need_odd;
            if (((z.mex & 1) && need_odd == 0) ||
                (!(z.mex & 1) && need_even == 0)) return false;
        }
        if (use_multi_edge_cover || shadow_multi_edge_cover) {
            const a2_multi_cover::Outcome cover = multi_cover_checker.check(
                multi_cover_input(z), multi_cover_config,
                multi_cover_counters);
            if (!cover.possible) {
                if (shadow_multi_edge_cover) multi_cover_shadow_reject++;
                else return false;
            }
        }
        if (use_parity_coherence || shadow_parity_coherence) {
            const auto outcome = parity_coherence_checker.check(
                multi_cover_input(z), parity_coherence_config,
                parity_coherence_counters);
            if (!outcome.possible) {
                if (shadow_parity_coherence) parity_coherence_shadow_reject++;
                else return false;
            }
        }
        if (stronger_cover_mode) {
            a2_multi_cover_stronger::Config config = stronger_cover_config;
            config.run_mex_conditioned = stronger_cover_mode >= 3;
            const auto outcome = stronger_cover_checker.check(
                multi_cover_input(z), config, stronger_cover_counters);
            if (!outcome.possible) {
                const bool shadow = stronger_cover_mode == 2 ||
                                    stronger_cover_mode == 4;
                if (shadow) stronger_cover_shadow_reject++;
                else return false;
            }
        }
        if (use_exact_pack || shadow_exact_pack) {
            auto config = exact_pack_config;
            if (exact_pack_late_components > 0 &&
                static_cast<int>(z.vertices.size()) <=
                    exact_pack_late_components) {
                if (exact_pack_late_budget)
                    config.state_budget = exact_pack_late_budget;
                if (exact_pack_late_arc_budget)
                    config.root_arc_comparison_budget =
                        exact_pack_late_arc_budget;
            }
            const auto outcome = exact_pack_checker.check(
                multi_cover_input(z), config, exact_pack_counters);
            if (!outcome.possible) {
                if (shadow_exact_pack) exact_pack_shadow_reject++;
                else return false;
            }
        }
        accepted++;

        if (stop_edges >= 0 && static_cast<int>(edges.size()) == stop_edges) {
            frontier++;
            frontier_mex[z.mex]++;
            int odd = 0;
            int third = -1;
            for (const Edge &edge : edges) if (edge.w & 1) {
                odd++;
                if (odd == 3) third = edge.w;
            }
            frontier_odd_count[odd]++;
            frontier_third_odd[third]++;
            return false;
        }

        if (static_cast<int>(edges.size()) == n - 1) {
            if (z.mex == target + 1) {
                // Production-safety change: install the complete certificate
                // before this stack frame returns and callers pop any edge.
                if (!save_terminal_witness()) return true;
                solution_topologies.insert(forest_code(false));
                return true;
            }
            return false;
        }
        if (z.mex > target) return false;

        struct Candidate { int score, u, v; };
        std::vector<Candidate> candidates;
        std::vector<std::string> component_code(z.vertices.size());
        std::vector<std::vector<int>> port_reps(z.vertices.size());
        std::vector<std::string> root_signature(n);
        std::map<std::string, std::vector<int>> component_types;
        for (int cid = 0; cid < static_cast<int>(z.vertices.size()); cid++) {
            bool first = true;
            std::map<std::string, int> roots;
            for (int vertex : z.vertices[cid]) {
                const std::string rooted = rooted_code(vertex, -1, 0, true);
                root_signature[vertex] = rooted;
                if (first || rooted < component_code[cid]) {
                    component_code[cid] = rooted;
                    first = false;
                }
                roots.emplace(rooted, vertex);
            }
            for (const auto &entry : roots)
                port_reps[cid].push_back(entry.second);
            component_types[component_code[cid]].push_back(cid);
        }
        const std::vector<std::pair<std::string, std::vector<int>>> types(
            component_types.begin(), component_types.end());
        for (int ta = 0; ta < static_cast<int>(types.size()); ta++) {
            for (int tb = ta; tb < static_cast<int>(types.size()); tb++) {
                if (ta == tb && types[ta].second.size() < 2U) continue;
                const int ca = types[ta].second[0];
                const int cb = ta == tb ? types[tb].second[1]
                                        : types[tb].second[0];
                for (int u : port_reps[ca]) for (int v : port_reps[cb]) {
                    if (ta == tb && root_signature[v] < root_signature[u])
                        continue;
                    const int score = -static_cast<int>(
                        z.vertices[ca].size() * z.vertices[cb].size());
                    candidates.push_back({score, u, v});
                }
            }
        }
        std::sort(candidates.begin(), candidates.end(),
                  [](const Candidate &left, const Candidate &right) {
            return std::tie(left.score, left.u, left.v) <
                   std::tie(right.score, right.u, right.v);
        });

        int valid_at_node = 0;
        for (const Candidate &candidate : candidates) {
            generated++;
            if (!candidate_cross_ok(z, candidate.u, candidate.v, z.mex)) {
                const auto &left = z.vertices[z.comp[candidate.u]];
                const auto &right = z.vertices[z.comp[candidate.v]];
                bool out = false;
                for (int a : left) for (int b : right)
                    out |= z.dist[a][candidate.u] + z.mex +
                           z.dist[candidate.v][b] > target;
                if (out) range_fail++;
                else collision++;
                continue;
            }
            const int branch = valid_at_node++;
            valid_children_max[edges.size()] = std::max(
                valid_children_max[edges.size()], valid_at_node);
            const int path_index = static_cast<int>(edges.size()) -
                                   branch_path_base_depth;
            if (path_index >= 0 &&
                path_index < static_cast<int>(branch_path.size()) &&
                branch != branch_path[path_index]) continue;
            if (static_cast<int>(edges.size()) == root_branch_depth) {
                root_valid_branches = std::max(root_valid_branches,
                                               valid_at_node);
                if (root_branch >= 0 && branch != root_branch) continue;
            }
            add_edge(candidate.u, candidate.v, z.mex);
            const bool done = rec_with_witness();
            pop_edge();
            if (done || limit) return done;
        }
        return false;
    }
};

void print_usage() {
    std::cout
        << "Usage: g001_remaining_witness_solver "
           "(--configuration 1|4|5|6|7 | --mode "
           "g001_row0|g001_row3|g001_row4|g001_row5|g001_row6) "
           "--witness-file UNIQUE_PATH "
           "[--root-branch I | --branch-path i,j,...] "
           "[--multi-edge-cover|--multi-edge-cover-shadow] "
           "[--multi-edge-cover-local-max-components K] "
           "[--multi-edge-cover-max-components K] "
           "[--multi-edge-cover-exact-max-components K] "
           "[--multi-edge-cover-budget N] "
           "[--multi-edge-cover-candidate-cap N] "
           "[--multi-edge-cover-no-hall] "
           "[--multi-edge-cover-no-exact] "
           "[--multi-edge-cover-no-exact-hall] "
           "[--multi-edge-cover-validate]\n"
        << "This executable always searches its selected subtree to a "
           "terminal ZERO or FOUND; node and depth caps are unsupported.\n";
}

} // namespace g001_witness

#ifndef G001_WITNESS_NO_MAIN
int main(int argc, char **argv) {
    using namespace g001_witness;
    std::ios::sync_with_stdio(false);
    std::cin.tie(nullptr);

    int external_configuration = -1;
    std::string internal_mode;
    fs::path witness_file;
    int root_branch = -1;
    std::vector<int> branch_path;
    bool use_multi_edge_cover = false;
    bool shadow_multi_edge_cover = false;
    a2_multi_cover::Config cover_config;

    for (int i = 1; i < argc; i++) {
        const std::string argument = argv[i];
        const auto require_value = [&](const char *option) -> std::string {
            if (i + 1 >= argc) {
                std::cerr << option << " requires a value\n";
                std::exit(kUsageExit);
            }
            return argv[++i];
        };
        if (argument == "--configuration") {
            if (!parse_nonnegative_int(require_value("--configuration"),
                                       external_configuration)) {
                std::cerr << "invalid --configuration\n";
                return kUsageExit;
            }
        } else if (argument == "--mode") {
            internal_mode = require_value("--mode");
        } else if (argument == "--witness-file") {
            witness_file = fs::path(require_value("--witness-file"));
        } else if (argument == "--root-branch") {
            if (!parse_nonnegative_int(require_value("--root-branch"),
                                       root_branch)) {
                std::cerr << "invalid --root-branch\n";
                return kUsageExit;
            }
        } else if (argument == "--branch-path") {
            if (!parse_branch_path(require_value("--branch-path"),
                                   branch_path)) {
                std::cerr << "invalid --branch-path\n";
                return kUsageExit;
            }
        } else if (argument == "--multi-edge-cover") {
            use_multi_edge_cover = true;
        } else if (argument == "--multi-edge-cover-shadow") {
            shadow_multi_edge_cover = true;
        } else if (argument == "--multi-edge-cover-local-max-components") {
            if (!parse_nonnegative_int(require_value(argument.c_str()),
                                       cover_config.local_max_components)) {
                std::cerr << "invalid local component limit\n";
                return kUsageExit;
            }
        } else if (argument == "--multi-edge-cover-max-components") {
            if (!parse_nonnegative_int(require_value(argument.c_str()),
                                       cover_config.max_components)) {
                std::cerr << "invalid component limit\n";
                return kUsageExit;
            }
        } else if (argument == "--multi-edge-cover-exact-max-components") {
            if (!parse_nonnegative_int(require_value(argument.c_str()),
                                       cover_config.exact_max_components)) {
                std::cerr << "invalid exact component limit\n";
                return kUsageExit;
            }
        } else if (argument == "--multi-edge-cover-budget") {
            if (!parse_nonnegative_u64(require_value(argument.c_str()),
                                       cover_config.exact_state_budget)) {
                std::cerr << "invalid cover budget\n";
                return kUsageExit;
            }
        } else if (argument == "--multi-edge-cover-candidate-cap") {
            std::uint64_t cap = 0;
            if (!parse_nonnegative_u64(require_value(argument.c_str()), cap) ||
                cap > std::numeric_limits<std::size_t>::max()) {
                std::cerr << "invalid candidate cap\n";
                return kUsageExit;
            }
            cover_config.exact_candidate_cap = static_cast<std::size_t>(cap);
        } else if (argument == "--multi-edge-cover-no-hall") {
            cover_config.run_hall = false;
        } else if (argument == "--multi-edge-cover-no-exact") {
            cover_config.run_exact = false;
        } else if (argument == "--multi-edge-cover-no-exact-hall") {
            cover_config.exact_residual_hall = false;
        } else if (argument == "--multi-edge-cover-validate") {
            cover_config.validate_candidates = true;
        } else if (argument == "--help") {
            print_usage();
            return 0;
        } else {
            std::cerr << "unsupported argument: " << argument << '\n';
            return kUsageExit;
        }
    }

    Configuration configuration;
    bool have_configuration = false;
    if (external_configuration >= 0) {
        if (!configuration_from_external(external_configuration,
                                         configuration)) {
            std::cerr << "configuration must be one of 1,4,5,6,7\n";
            return kUsageExit;
        }
        have_configuration = true;
    }
    if (!internal_mode.empty()) {
        Configuration by_mode;
        if (!configuration_from_mode(internal_mode, by_mode)) {
            std::cerr << "unsupported internal mode\n";
            return kUsageExit;
        }
        if (have_configuration &&
            by_mode.external != configuration.external) {
            std::cerr << "--configuration and --mode disagree\n";
            return kUsageExit;
        }
        configuration = by_mode;
        have_configuration = true;
    }
    if (!have_configuration) {
        std::cerr << "a supported --configuration or --mode is required\n";
        return kUsageExit;
    }
    if (witness_file.empty()) {
        std::cerr << "a unique --witness-file is required\n";
        return kUsageExit;
    }
    if (root_branch >= 0 && !branch_path.empty()) {
        std::cerr << "choose --root-branch or --branch-path, not both\n";
        return kUsageExit;
    }
    if (branch_path.size() > 14U) {
        std::cerr << "branch path exceeds the 14 post-seed edge choices\n";
        return kUsageExit;
    }
    if (use_multi_edge_cover && shadow_multi_edge_cover) {
        std::cerr << "choose active or shadow multi-edge cover, not both\n";
        return kUsageExit;
    }
    const auto valid_component_limit = [](int value) {
        return value >= 1 && value <= 18;
    };
    if (!valid_component_limit(cover_config.local_max_components) ||
        !valid_component_limit(cover_config.max_components) ||
        !valid_component_limit(cover_config.exact_max_components) ||
        cover_config.exact_max_components > cover_config.max_components) {
        std::cerr << "cover thresholds require 1 <= exact <= max <= 18 and "
                     "1 <= local <= 18\n";
        return kUsageExit;
    }

    std::string preflight_error;
    if (!target_is_new_and_parent_exists(witness_file, preflight_error)) {
        std::cerr << "witness-file error: " << preflight_error << '\n';
        return kIoExit;
    }

    WitnessSearch search(configuration, witness_file);
    search.use_order18_parity = true;
    search.root_branch = root_branch;
    search.branch_path = branch_path;
    search.branch_path_base_depth = 3;
    search.root_branch_depth = 3;
    search.stop_edges = -1;
    search.max_nodes = 0;
    search.stop_at_first = true;
    search.use_multi_edge_cover = use_multi_edge_cover;
    search.shadow_multi_edge_cover = shadow_multi_edge_cover;
    search.multi_cover_config = cover_config;

    const int expected_mex = initialize_seed(search, configuration.mode);
    const Search::Analysis seed_analysis = search.analyze();
    if (!seed_analysis.valid || seed_analysis.mex != expected_mex) {
        std::cerr << "internal seed validation failed for "
                  << configuration.mode << " expected_mex=" << expected_mex
                  << " actual_mex=" << seed_analysis.mex << '\n';
        return kInternalExit;
    }

    search.rec_with_witness();
    if (search.witness_io_failed) {
        std::cerr << "witness IO failure: " << search.witness_error << '\n';
        std::cout << "RESULT mode=" << configuration.mode
                  << " configuration=" << configuration.external
                  << " status=IO_ERROR nodes=" << search.nodes
                  << " states=" << search.accepted << '\n';
        return kIoExit;
    }
    search.print_result(configuration.mode);
    if (search.witness_saved) {
        if (search.solution_topologies.empty()) {
            std::cerr << "internal error: witness saved without FOUND state\n";
            return kInternalExit;
        }
        std::cout << "WITNESS format=LEECH_WITNESS_V1 configuration="
                  << configuration.external << " file="
                  << std::quoted(witness_file.string()) << '\n';
        return 2;
    }
    if (!search.solution_topologies.empty()) {
        std::cerr << "internal error: FOUND state without durable witness\n";
        return kInternalExit;
    }
    return 0;
}
#endif
