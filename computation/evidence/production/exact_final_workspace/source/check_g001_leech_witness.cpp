#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

// Independent, STL-only checker for LEECH_WITNESS_V1 certificates.  It does
// not include or call the search implementation or any pruning layer.

namespace g001_witness_check {

constexpr int kOrder = 18;
constexpr int kEdgeCount = 17;
constexpr int kDistanceCount = 153;
constexpr int kIoExit = 74;
constexpr int kUsageExit = 64;

struct Edge {
    int u = -1;
    int v = -1;
    int weight = -1;
};

struct Certificate {
    int configuration = -1;
    std::string mode;
    int vertices = -1;
    std::vector<Edge> edges;
};

bool expect_token(std::istream &input, const std::string &expected,
                  std::string &error) {
    std::string actual;
    if (!(input >> actual)) {
        error = "expected token '" + expected + "' before end of file";
        return false;
    }
    if (actual != expected) {
        error = "unexpected token where '" + expected + "' was required";
        return false;
    }
    return true;
}

bool checked_int(long long value, int minimum, int maximum, int &result,
                 const std::string &field, std::string &error) {
    if (value < minimum || value > maximum) {
        error = field + " is outside the allowed range";
        return false;
    }
    result = static_cast<int>(value);
    return true;
}

bool parse_certificate(std::istream &input, Certificate &certificate,
                       std::string &error) {
    if (!expect_token(input, "LEECH_WITNESS_V1", error)) return false;
    if (!expect_token(input, "configuration", error)) return false;
    long long configuration = -1;
    if (!(input >> configuration) ||
        !checked_int(configuration, 0, std::numeric_limits<int>::max(),
                     certificate.configuration, "configuration", error)) {
        if (error.empty()) error = "configuration is not an integer";
        return false;
    }
    if (!expect_token(input, "mode", error)) return false;
    if (!(input >> certificate.mode)) {
        error = "mode is missing";
        return false;
    }
    if (!expect_token(input, "vertices", error)) return false;
    long long vertices = -1;
    if (!(input >> vertices) ||
        !checked_int(vertices, 0, std::numeric_limits<int>::max(),
                     certificate.vertices, "vertices", error)) {
        if (error.empty()) error = "vertices is not an integer";
        return false;
    }
    if (!expect_token(input, "edges", error)) return false;
    long long edge_count = -1;
    if (!(input >> edge_count)) {
        error = "edge count is not an integer";
        return false;
    }
    if (edge_count != kEdgeCount) {
        error = "certificate must declare exactly 17 edges";
        return false;
    }

    certificate.edges.clear();
    certificate.edges.reserve(kEdgeCount);
    for (int index = 0; index < kEdgeCount; ++index) {
        if (!expect_token(input, "edge", error)) return false;
        long long u = -1;
        long long v = -1;
        long long weight = -1;
        if (!(input >> u >> v >> weight)) {
            error = "edge " + std::to_string(index) +
                    " does not contain three integers";
            return false;
        }
        Edge edge;
        if (!checked_int(u, 0, kOrder - 1, edge.u, "edge endpoint", error) ||
            !checked_int(v, 0, kOrder - 1, edge.v, "edge endpoint", error) ||
            !checked_int(weight, 1, kDistanceCount, edge.weight,
                         "edge weight", error)) return false;
        certificate.edges.push_back(edge);
    }
    if (!expect_token(input, "end", error)) return false;
    std::string trailing;
    if (input >> trailing) {
        error = "unexpected trailing content";
        return false;
    }
    return true;
}

bool mode_matches_configuration(int configuration, const std::string &mode) {
    switch (configuration) {
    case 1: return mode == "g001_row0";
    case 4: return mode == "g001_row3";
    case 5: return mode == "g001_row4";
    case 6: return mode == "g001_row5";
    case 7: return mode == "g001_row6";
    default: return false;
    }
}

const Edge *edge_of_weight(const std::vector<Edge> &edges, int weight) {
    for (const Edge &edge : edges)
        if (edge.weight == weight) return &edge;
    return nullptr;
}

bool incident(const Edge &left, const Edge &right) {
    return left.u == right.u || left.u == right.v ||
           left.v == right.u || left.v == right.v;
}

bool common_endpoint_of_three(const Edge &first, const Edge &second,
                              const Edge &third) {
    const std::array<int, 2> endpoints{{first.u, first.v}};
    for (int vertex : endpoints) {
        const bool in_second = vertex == second.u || vertex == second.v;
        const bool in_third = vertex == third.u || vertex == third.v;
        if (in_second && in_third) return true;
    }
    return false;
}

bool claimed_configuration_holds(const Certificate &certificate,
                                 std::string &error) {
    const Edge *edge1 = edge_of_weight(certificate.edges, 1);
    const Edge *edge2 = edge_of_weight(certificate.edges, 2);
    const Edge *edge3 = edge_of_weight(certificate.edges, 3);
    const Edge *edge4 = edge_of_weight(certificate.edges, 4);

    bool holds = false;
    switch (certificate.configuration) {
    case 1:
        holds = edge1 && edge2 && !edge3 && edge4 &&
                incident(*edge1, *edge2) && !incident(*edge1, *edge4) &&
                !incident(*edge2, *edge4);
        break;
    case 4:
        holds = edge1 && edge2 && !edge3 && edge4 &&
                common_endpoint_of_three(*edge1, *edge2, *edge4);
        break;
    case 5:
        holds = edge1 && edge2 && edge3 &&
                !incident(*edge1, *edge2) &&
                !incident(*edge1, *edge3) &&
                !incident(*edge2, *edge3);
        break;
    case 6:
        holds = edge1 && edge2 && edge3 &&
                !incident(*edge1, *edge2) &&
                incident(*edge1, *edge3) &&
                !incident(*edge2, *edge3);
        break;
    case 7:
        holds = edge1 && edge2 && edge3 &&
                !incident(*edge1, *edge2) &&
                !incident(*edge1, *edge3) &&
                incident(*edge2, *edge3);
        break;
    default:
        error = "claimed configuration is not one of 1,4,5,6,7";
        return false;
    }
    if (!holds) {
        error = "physical edges of weights 1,2,3,4 do not realize claimed "
                "configuration " +
                std::to_string(certificate.configuration);
        return false;
    }
    return true;
}

struct DisjointSet {
    std::array<int, kOrder> parent{};
    std::array<int, kOrder> rank{};

    DisjointSet() {
        for (int vertex = 0; vertex < kOrder; ++vertex)
            parent[vertex] = vertex;
    }

    int find(int vertex) {
        if (parent[vertex] != vertex)
            parent[vertex] = find(parent[vertex]);
        return parent[vertex];
    }

    bool unite(int left, int right) {
        left = find(left);
        right = find(right);
        if (left == right) return false;
        if (rank[left] < rank[right]) std::swap(left, right);
        parent[right] = left;
        if (rank[left] == rank[right]) rank[left]++;
        return true;
    }
};

bool validate_certificate(const Certificate &certificate, std::string &error) {
    if (!mode_matches_configuration(certificate.configuration,
                                    certificate.mode)) {
        error = "mode does not match the claimed remaining configuration";
        return false;
    }
    if (certificate.vertices != kOrder) {
        error = "certificate must contain exactly 18 vertices";
        return false;
    }
    if (certificate.edges.size() != kEdgeCount) {
        error = "certificate must contain exactly 17 edges";
        return false;
    }

    DisjointSet components;
    int previous_weight = 0;
    std::array<std::vector<std::pair<int, int>>, kOrder> adjacency;
    for (std::size_t index = 0; index < certificate.edges.size(); ++index) {
        const Edge &edge = certificate.edges[index];
        if (edge.u < 0 || edge.u >= kOrder ||
            edge.v < 0 || edge.v >= kOrder || edge.u == edge.v) {
            error = "edge " + std::to_string(index) +
                    " has invalid endpoints";
            return false;
        }
        if (edge.weight <= 0 || edge.weight > kDistanceCount ||
            edge.weight <= previous_weight) {
            error = "edge weights must be positive, distinct, and strictly "
                    "increasing in physical-edge order";
            return false;
        }
        previous_weight = edge.weight;
        if (!components.unite(edge.u, edge.v)) {
            error = "the 17 edges contain a cycle";
            return false;
        }
        adjacency[edge.u].push_back({edge.v, edge.weight});
        adjacency[edge.v].push_back({edge.u, edge.weight});
    }
    const int root = components.find(0);
    for (int vertex = 1; vertex < kOrder; ++vertex) {
        if (components.find(vertex) != root) {
            error = "the 17 edges are disconnected";
            return false;
        }
    }

    std::array<bool, kDistanceCount + 1> seen{};
    int distance_count = 0;
    for (int source = 0; source < kOrder; ++source) {
        std::array<int, kOrder> parent;
        std::array<int, kOrder> distance;
        parent.fill(-2);
        distance.fill(-1);
        parent[source] = -1;
        distance[source] = 0;
        std::vector<int> stack{source};
        while (!stack.empty()) {
            const int vertex = stack.back();
            stack.pop_back();
            for (const auto &step : adjacency[vertex]) {
                const int next = step.first;
                const int weight = step.second;
                if (next == parent[vertex]) continue;
                if (parent[next] != -2) {
                    error = "cycle encountered while computing distances";
                    return false;
                }
                parent[next] = vertex;
                if (distance[vertex] > kDistanceCount - weight) {
                    error = "a pair distance exceeds 153";
                    return false;
                }
                distance[next] = distance[vertex] + weight;
                stack.push_back(next);
            }
        }
        for (int target = source + 1; target < kOrder; ++target) {
            const int value = distance[target];
            if (value < 1 || value > kDistanceCount) {
                error = "a pair distance lies outside 1..153";
                return false;
            }
            if (seen[value]) {
                error = "pair distance " + std::to_string(value) +
                        " occurs more than once";
                return false;
            }
            seen[value] = true;
            distance_count++;
        }
    }
    if (distance_count != kDistanceCount) {
        error = "internal pair-distance count is not 153";
        return false;
    }
    for (int value = 1; value <= kDistanceCount; ++value) {
        if (!seen[value]) {
            error = "pair distance " + std::to_string(value) + " is missing";
            return false;
        }
    }
    return claimed_configuration_holds(certificate, error);
}

std::string make_parseable_non_witness(bool trailing_token = false) {
    std::ostringstream out;
    out << "LEECH_WITNESS_V1\nconfiguration 5\nmode g001_row4\n"
           "vertices 18\nedges 17\n";
    out << "edge 0 1 1\n";
    out << "edge 2 3 2\n";
    out << "edge 4 5 3\n";
    out << "edge 1 2 4\n";
    out << "edge 3 4 5\n";
    for (int weight = 6; weight <= 17; ++weight)
        out << "edge " << weight - 1 << ' ' << weight << ' ' << weight
            << '\n';
    out << "end\n";
    if (trailing_token) out << "junk\n";
    return out.str();
}

int run_self_test() {
    int checks = 0;
    const auto require = [&](bool condition, const std::string &name) {
        checks++;
        if (!condition)
            std::cerr << "SELF_TEST failure: " << name << '\n';
        return condition;
    };

    const auto configuration_fixture = [](int configuration) {
        Certificate certificate;
        certificate.configuration = configuration;
        certificate.vertices = kOrder;
        switch (configuration) {
        case 1:
            certificate.mode = "g001_row0";
            certificate.edges = {{7, 9, 1}, {9, 3, 2}, {12, 14, 4}};
            break;
        case 4:
            certificate.mode = "g001_row3";
            certificate.edges = {{8, 2, 1}, {8, 11, 2}, {8, 17, 4}};
            break;
        case 5:
            certificate.mode = "g001_row4";
            certificate.edges = {{0, 17, 1}, {4, 13, 2}, {6, 9, 3}};
            break;
        case 6:
            certificate.mode = "g001_row5";
            certificate.edges = {{10, 1, 1}, {7, 15, 2}, {1, 3, 3}};
            break;
        case 7:
            certificate.mode = "g001_row6";
            certificate.edges = {{10, 1, 1}, {7, 15, 2}, {15, 3, 3}};
            break;
        default: break;
        }
        return certificate;
    };

    bool ok = true;
    for (int configuration : {1, 4, 5, 6, 7}) {
        Certificate fixture = configuration_fixture(configuration);
        std::string error;
        ok &= require(claimed_configuration_holds(fixture, error),
                      "configuration classifier " +
                          std::to_string(configuration));
    }
    Certificate wrong = configuration_fixture(6);
    wrong.configuration = 7;
    std::string error;
    ok &= require(!claimed_configuration_holds(wrong, error),
                  "configuration 6/7 distinction");

    Certificate parsed;
    std::istringstream input(make_parseable_non_witness());
    error.clear();
    ok &= require(parse_certificate(input, parsed, error),
                  "strict parser accepts canonical syntax");
    error.clear();
    ok &= require(!validate_certificate(parsed, error),
                  "non-Leech tree is rejected");

    Certificate cycle = parsed;
    cycle.edges.back().u = 16;
    cycle.edges.back().v = 0;
    error.clear();
    ok &= require(!validate_certificate(cycle, error),
                  "cycle/disconnection is rejected");

    Certificate unsorted = parsed;
    unsorted.edges[6].weight = unsorted.edges[5].weight;
    error.clear();
    ok &= require(!validate_certificate(unsorted, error),
                  "non-increasing weights are rejected");

    Certificate trailing;
    std::istringstream trailing_input(make_parseable_non_witness(true));
    error.clear();
    ok &= require(!parse_certificate(trailing_input, trailing, error),
                  "trailing tokens are rejected");

    if (!ok) return 1;
    std::cout << "SELF_TEST PASS checks=" << checks << '\n';
    return 0;
}

} // namespace g001_witness_check

int main(int argc, char **argv) {
    using namespace g001_witness_check;
    if (argc == 2 && std::string(argv[1]) == "--self-test")
        return run_self_test();
    if (argc != 2) {
        std::cerr << "Usage: check_g001_leech_witness WITNESS_FILE\n"
                     "       check_g001_leech_witness --self-test\n";
        return kUsageExit;
    }

    std::ifstream input(argv[1], std::ios::binary);
    if (!input) {
        std::cerr << "IO_ERROR cannot open witness file\n";
        return kIoExit;
    }
    input.seekg(0, std::ios::end);
    const std::streamoff file_size = input.tellg();
    if (file_size < 0 || file_size > 65536) {
        std::cerr << "INVALID format: witness file size is unreasonable\n";
        return 1;
    }
    input.seekg(0, std::ios::beg);
    Certificate certificate;
    std::string error;
    if (!parse_certificate(input, certificate, error)) {
        std::cerr << "INVALID format: " << error << '\n';
        return 1;
    }
    if (!validate_certificate(certificate, error)) {
        std::cerr << "INVALID witness: " << error << '\n';
        return 1;
    }
    std::cout << "VALID LEECH_WITNESS_V1 configuration="
              << certificate.configuration << " mode=" << certificate.mode
              << " vertices=18 edges=17 distances=1..153\n";
    return 0;
}
