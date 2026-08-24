#include <algorithm>
#include <array>
#include <iostream>
#include <map>
#include <numeric>
#include <queue>
#include <set>
#include <stdexcept>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

namespace {

constexpr int order=18;
constexpr int target=153;

struct Edge {
    int u;
    int v;
    int w;
};

struct SeedCase {
    std::string mode;
    std::vector<Edge> edges;
    std::vector<int> expected_spectrum;
    int expected_mex;
    std::map<int,int> expected_child_mex;
};

struct Analysis {
    std::array<int,order> component{};
    std::vector<std::vector<int>> vertices;
    std::array<std::array<int,order>,order> distance{};
    std::array<bool,target+1> used{};
    bool valid=true;
    int mex=1;
};

std::vector<std::vector<std::pair<int,int>>>
adjacency(const std::vector<Edge>& edges) {
    std::vector<std::vector<std::pair<int,int>>> adjacent(order);
    for (const Edge& edge:edges) {
        adjacent[edge.u].push_back({edge.v,edge.w});
        adjacent[edge.v].push_back({edge.u,edge.w});
    }
    return adjacent;
}

Analysis analyze(const std::vector<Edge>& edges) {
    Analysis result;
    result.component.fill(-1);
    result.used.fill(false);
    for (auto& row:result.distance) row.fill(-1);
    const auto adjacent=adjacency(edges);

    for (int start=0;start<order;start++) {
        if (result.component[start]>=0) continue;
        const int component_id=static_cast<int>(result.vertices.size());
        result.vertices.push_back({});
        std::queue<int> pending;
        pending.push(start);
        result.component[start]=component_id;
        while (!pending.empty()) {
            const int vertex=pending.front();
            pending.pop();
            result.vertices.back().push_back(vertex);
            for (const auto& [next,weight]:adjacent[vertex]) {
                (void)weight;
                if (result.component[next]<0) {
                    result.component[next]=component_id;
                    pending.push(next);
                }
            }
        }
    }

    for (int source=0;source<order;source++) {
        std::vector<std::tuple<int,int,int>> pending={{source,-1,0}};
        while (!pending.empty()) {
            const auto [vertex,parent,distance]=pending.back();
            pending.pop_back();
            result.distance[source][vertex]=distance;
            for (const auto& [next,weight]:adjacent[vertex]) {
                if (next!=parent) pending.push_back({next,vertex,distance+weight});
            }
        }
    }

    for (int first=0;first<order;first++) {
        for (int second=first+1;second<order;second++) {
            if (result.component[first]!=result.component[second]) continue;
            const int distance=result.distance[first][second];
            if (distance<1 || distance>target || result.used[distance]) {
                result.valid=false;
                continue;
            }
            result.used[distance]=true;
        }
    }
    while (result.mex<=target && result.used[result.mex]) result.mex++;
    return result;
}

std::string rooted_code(
    int vertex,int parent,
    const std::vector<std::vector<std::pair<int,int>>>& adjacent) {
    std::vector<std::string> children;
    for (const auto& [next,weight]:adjacent[vertex]) {
        if (next==parent) continue;
        children.push_back(rooted_code(next,vertex,adjacent)+
                           ":"+std::to_string(weight));
    }
    std::sort(children.begin(),children.end());
    std::string code="(";
    for (const std::string& child:children) code+=child+",";
    code+=")";
    return code;
}

std::string canonical_forest_code(const std::vector<Edge>& edges) {
    const auto adjacent=adjacency(edges);
    std::array<bool,order> seen{};
    std::vector<std::string> component_codes;
    for (int start=0;start<order;start++) {
        if (seen[start]) continue;
        std::vector<int> vertices;
        std::queue<int> pending;
        pending.push(start);
        seen[start]=true;
        while (!pending.empty()) {
            const int vertex=pending.front();
            pending.pop();
            vertices.push_back(vertex);
            for (const auto& [next,weight]:adjacent[vertex]) {
                (void)weight;
                if (!seen[next]) {
                    seen[next]=true;
                    pending.push(next);
                }
            }
        }
        std::string best;
        bool first=true;
        for (const int root:vertices) {
            const std::string candidate=rooted_code(root,-1,adjacent);
            if (first || candidate<best) {
                best=candidate;
                first=false;
            }
        }
        component_codes.push_back(best);
    }
    std::sort(component_codes.begin(),component_codes.end());
    std::string result;
    for (const std::string& code:component_codes) result+="["+code+"]";
    return result;
}

bool cross_block_is_fresh(
    const Analysis& analysis,int first_port,int second_port,int weight) {
    std::array<bool,target+1> fresh{};
    const auto& first_component=
        analysis.vertices[analysis.component[first_port]];
    const auto& second_component=
        analysis.vertices[analysis.component[second_port]];
    for (const int first_vertex:first_component) {
        for (const int second_vertex:second_component) {
            const int distance=analysis.distance[first_vertex][first_port]+
                weight+analysis.distance[second_port][second_vertex];
            if (distance<1 || distance>target || analysis.used[distance] ||
                fresh[distance]) return false;
            fresh[distance]=true;
        }
    }
    return true;
}

std::vector<int> spectrum(const Analysis& analysis) {
    std::vector<int> result;
    for (int distance=1;distance<=target;distance++) {
        if (analysis.used[distance]) result.push_back(distance);
    }
    return result;
}

std::vector<SeedCase> seed_cases() {
    return {
        {"g001_row0",{{0,1,1},{1,2,2},{3,4,4}},{1,2,3,4},5,
            {{6,4},{7,2},{8,2}}},
        {"g001_row3",{{0,1,1},{0,2,2},{0,3,4}},{1,2,3,4,5,6},7,
            {{8,3},{9,1},{10,1}}},
        {"g001_row4",{{0,1,1},{2,3,2},{4,5,3}},{1,2,3},4,
            {{5,4},{6,2},{8,1}}},
        {"g001_row5",{{0,1,1},{3,4,2},{1,2,3}},{1,2,3,4},5,
            {{6,4},{7,2},{10,1}}},
        {"g001_row6",{{0,1,1},{2,3,2},{3,4,3}},{1,2,3,5},4,
            {{6,2},{7,1},{8,1}}}
    };
}

} // namespace

int main() {
    for (const SeedCase& seed:seed_cases()) {
        const Analysis initial=analyze(seed.edges);
        if (!initial.valid || spectrum(initial)!=seed.expected_spectrum ||
            initial.mex!=seed.expected_mex) {
            std::cerr<<"SEED_ORACLE_FAIL mode="<<seed.mode<<"\n";
            return 1;
        }

        std::map<std::string,int> canonical_child_mex;
        long long valid_raw_pairs=0;
        for (int first=0;first<order;first++) {
            for (int second=first+1;second<order;second++) {
                if (initial.component[first]==initial.component[second]) continue;
                if (!cross_block_is_fresh(initial,first,second,initial.mex))
                    continue;
                valid_raw_pairs++;
                std::vector<Edge> child=seed.edges;
                child.push_back({first,second,initial.mex});
                const Analysis child_analysis=analyze(child);
                if (!child_analysis.valid) {
                    std::cerr<<"CHILD_ANALYSIS_FAIL mode="<<seed.mode<<"\n";
                    return 1;
                }
                const std::string code=canonical_forest_code(child);
                auto [where,inserted]=canonical_child_mex.emplace(
                    code,child_analysis.mex);
                if (!inserted && where->second!=child_analysis.mex) {
                    std::cerr<<"CANONICAL_MEX_MISMATCH mode="<<seed.mode<<"\n";
                    return 1;
                }
            }
        }

        std::map<int,int> mex_distribution;
        for (const auto& [code,mex]:canonical_child_mex) {
            (void)code;
            mex_distribution[mex]++;
        }
        if (mex_distribution!=seed.expected_child_mex) {
            std::cerr<<"CHILD_ORBIT_ORACLE_FAIL mode="<<seed.mode<<"\n";
            return 1;
        }
        std::cout<<"ORACLE mode="<<seed.mode
                 <<" seed_mex="<<initial.mex
                 <<" valid_raw_pairs="<<valid_raw_pairs
                 <<" children="<<canonical_child_mex.size()
                 <<" child_mex=";
        for (const auto& [mex,count]:mex_distribution)
            std::cout<<mex<<":"<<count<<",";
        std::cout<<"\n";
    }
    std::cout<<"G001_REMAINING_SEED_ORBIT_ORACLE_OK\n";
    return 0;
}
