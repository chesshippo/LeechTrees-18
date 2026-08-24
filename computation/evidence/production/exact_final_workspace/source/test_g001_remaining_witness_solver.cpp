#define G001_WITNESS_NO_MAIN
#include "g001_remaining_witness_solver.cpp"

#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>

namespace {

bool equivalent_shallow_result(const Search &frozen,
                               const g001_witness::WitnessSearch &wrapped) {
    return frozen.nodes == wrapped.nodes &&
           frozen.accepted == wrapped.accepted &&
           frozen.generated == wrapped.generated &&
           frozen.duplicate == wrapped.duplicate &&
           frozen.collision == wrapped.collision &&
           frozen.range_fail == wrapped.range_fail &&
           frozen.parity_fail == wrapped.parity_fail &&
           frozen.diameter_fail == wrapped.diameter_fail &&
           frozen.frontier == wrapped.frontier &&
           frozen.frontier_mex == wrapped.frontier_mex &&
           frozen.frontier_odd_count == wrapped.frontier_odd_count &&
           frozen.frontier_third_odd == wrapped.frontier_third_odd &&
           frozen.root_valid_branches == wrapped.root_valid_branches &&
           frozen.valid_children_max == wrapped.valid_children_max &&
           frozen.depth_nodes == wrapped.depth_nodes;
}

void configure_shallow(Search &search) {
    search.use_order18_parity = true;
    search.branch_path_base_depth = 3;
    search.root_branch_depth = 3;
    search.stop_edges = 5;
}

void configure_partition(Search &search, int base_depth,
                         const std::vector<int> &path, int stop_edges) {
    search.use_order18_parity = true;
    search.branch_path_base_depth = base_depth;
    search.root_branch_depth = base_depth;
    search.branch_path = path;
    search.stop_edges = stop_edges;
    search.stop_at_first = true;
}

void initialize_row1_seed(Search &search) {
    search.add_edge(1, 2, 1);
    search.add_edge(2, 3, 2);
    search.add_edge(0, 1, 4);
}

void initialize_row7_seed(Search &search) {
    search.add_edge(0, 1, 1);
    search.add_edge(2, 3, 2);
    search.add_edge(1, 2, 3);
}

void initialize_a2_attached_seed(Search &search) {
    search.add_edge(0, 1, 1);
    search.add_edge(1, 2, 2);
    search.add_edge(2, 3, 4);
    search.add_edge(3, 4, 5);
}

void enable_production_cover(Search &search) {
    search.use_multi_edge_cover = true;
    search.multi_cover_config.run_hall = false;
    search.multi_cover_config.max_components = 6;
    search.multi_cover_config.exact_state_budget = 100;
    search.multi_cover_config.exact_residual_hall = false;
}

} // namespace

int main() {
    using namespace g001_witness;
    int checks = 0;
    bool ok = true;
    const auto require = [&](bool condition, const std::string &name) {
        checks++;
        if (!condition) {
            std::cerr << "FAIL: " << name << '\n';
            ok = false;
        }
    };

    for (int external : {1, 4, 5, 6, 7}) {
        Configuration configuration;
        require(configuration_from_external(external, configuration),
                "configuration mapping " + std::to_string(external));

        Search frozen(18);
        configure_shallow(frozen);
        const int frozen_mex = initialize_seed(frozen, configuration.mode);
        const Search::Analysis frozen_seed = frozen.analyze();
        require(frozen_seed.valid && frozen_seed.mex == frozen_mex,
                "frozen seed " + configuration.mode);

        WitnessSearch wrapped(configuration,
                              std::filesystem::path("unused-test-witness"));
        configure_shallow(wrapped);
        const int wrapped_mex = initialize_seed(wrapped, configuration.mode);
        const Search::Analysis wrapped_seed = wrapped.analyze();
        require(wrapped_seed.valid && wrapped_seed.mex == wrapped_mex &&
                    wrapped_mex == frozen_mex,
                "wrapped seed " + configuration.mode);

        frozen.rec();
        wrapped.rec_with_witness();
        require(equivalent_shallow_result(frozen, wrapped),
                "frozen recursion parity " + configuration.mode);
        require(!wrapped.witness_saved && !wrapped.witness_io_failed,
                "shallow regression cannot emit witness " +
                    configuration.mode);
    }

    const std::array<std::size_t, 7> expected_small{{0, 0, 1, 1, 2, 0, 1}};
    for (int order = 2; order <= 6; ++order) {
        Search small(order);
        small.rec();
        require(small.solution_topologies.size() == expected_small[order],
                "small-order topology count " + std::to_string(order));
    }

    const auto compare_known_shallow = [&](const std::string &name,
                                           void (*seed)(Search &),
                                           long long expected_frontier,
                                           const std::map<int, long long>
                                               &expected_mex) {
        Search frozen(18);
        configure_partition(frozen, 3, {}, 4);
        seed(frozen);
        Configuration test_configuration{1, "g001_row0"};
        WitnessSearch wrapped(test_configuration,
                              std::filesystem::path("unused-test-witness"));
        configure_partition(wrapped, 3, {}, 4);
        seed(wrapped);
        frozen.rec();
        wrapped.rec_with_witness();
        require(equivalent_shallow_result(frozen, wrapped),
                name + " frozen recursion parity");
        require(wrapped.frontier == expected_frontier &&
                    wrapped.root_valid_branches == expected_frontier &&
                    wrapped.frontier_mex == expected_mex,
                name + " certified first fan-out");
    };
    compare_known_shallow("row1", initialize_row1_seed, 3,
                          {{8, 2}, {10, 1}});
    compare_known_shallow("row7", initialize_row7_seed, 5,
                          {{8, 3}, {9, 2}});

    const std::filesystem::path unexpected_a2_witness =
        std::filesystem::temp_directory_path() /
        ("unexpected-a2-witness." + process_token());
    Search frozen_a2(18);
    configure_partition(frozen_a2, 4, {1, 1}, -1);
    enable_production_cover(frozen_a2);
    initialize_a2_attached_seed(frozen_a2);
    WitnessSearch wrapped_a2({3, "a2_attached"}, unexpected_a2_witness);
    configure_partition(wrapped_a2, 4, {1, 1}, -1);
    enable_production_cover(wrapped_a2);
    initialize_a2_attached_seed(wrapped_a2);
    frozen_a2.rec();
    wrapped_a2.rec_with_witness();
    require(frozen_a2.nodes == 32841 &&
                frozen_a2.solution_topologies.empty(),
            "A2 attached path 1,1 frozen 32,841-node ZERO");
    require(equivalent_shallow_result(frozen_a2, wrapped_a2) &&
                wrapped_a2.nodes == 32841 &&
                wrapped_a2.solution_topologies.empty() &&
                !wrapped_a2.witness_saved && !wrapped_a2.witness_io_failed,
            "A2 attached path 1,1 wrapper parity");
    std::error_code unexpected_ec;
    const bool unexpected_exists =
        std::filesystem::exists(unexpected_a2_witness, unexpected_ec);
    require(!unexpected_ec && !unexpected_exists,
            "A2 ZERO emitted no witness");
    if (unexpected_exists)
        std::filesystem::remove(unexpected_a2_witness, unexpected_ec);

    Configuration configuration;
    require(configuration_from_external(1, configuration),
            "serialization configuration");
    std::vector<Edge> synthetic_edges;
    for (int weight = 1; weight <= 17; ++weight)
        synthetic_edges.push_back({weight - 1, weight, weight});
    std::string error;
    const std::string text =
        serialize_witness(configuration, synthetic_edges, error);
    require(!text.empty() &&
                text.find("LEECH_WITNESS_V1\nconfiguration 1\n"
                          "mode g001_row0\n") == 0 &&
                text.size() >= 4U && text.substr(text.size() - 4U) == "end\n",
            "deterministic witness serialization");

    const std::filesystem::path directory =
        std::filesystem::temp_directory_path() /
        ("g001-witness-layer-test." + process_token());
    std::error_code ec;
    require(std::filesystem::create_directory(directory, ec) && !ec,
            "create private test directory");
    const std::filesystem::path target = directory / "certificate.txt";
    error.clear();
    require(durable_atomic_write_new(target, text, error),
            "durable atomic install");
    std::ifstream saved(target, std::ios::binary);
    const std::string recovered((std::istreambuf_iterator<char>(saved)),
                                std::istreambuf_iterator<char>());
    require(recovered == text, "installed bytes match serialization");
    saved.close();
    error.clear();
    require(!durable_atomic_write_new(target, text, error) &&
                error.find("already exists") != std::string::npos,
            "no-overwrite uniqueness guard");
    ec.clear();
    require(std::filesystem::remove(target, ec) && !ec,
            "remove owned test certificate");
    ec.clear();
    require(std::filesystem::remove(directory, ec) && !ec,
            "remove empty private test directory");

    if (!ok) return 1;
    std::cout << "PASS test_g001_remaining_witness_solver checks="
              << checks << '\n';
    return 0;
}
