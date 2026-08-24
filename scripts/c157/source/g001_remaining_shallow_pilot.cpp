#define main frozen_order18_topology_free_search_main
#include "order18_topology_free_search.cpp"
#undef main

namespace {

bool is_remaining_mode(const std::string& mode) {
    return mode=="g001_row0" || mode=="g001_row3" ||
           mode=="g001_row4" || mode=="g001_row5" ||
           mode=="g001_row6";
}

void print_pilot_usage() {
    std::cout
        <<"Usage: g001_remaining_shallow_pilot --mode "
          "g001_row0|g001_row3|g001_row4|g001_row5|g001_row6 "
          "--stop-edges E [--max-nodes N] [--root-branch I] "
          "[--branch-path i,j,...] "
          "[--multi-edge-cover|--multi-edge-cover-shadow] "
          "[--multi-edge-cover-local-max-components K] "
          "[--multi-edge-cover-max-components K] "
          "[--multi-edge-cover-exact-max-components K] "
          "[--multi-edge-cover-budget N] "
          "[--multi-edge-cover-candidate-cap N] "
          "[--multi-edge-cover-no-hall] "
          "[--multi-edge-cover-no-exact] "
          "[--multi-edge-cover-no-exact-hall] "
          "[--multi-edge-cover-validate]\n";
}

bool parse_nonnegative_int(const std::string& text,int& value) {
    if (text.empty()) return false;
    std::size_t consumed=0;
    try {
        long long parsed=std::stoll(text,&consumed);
        if (consumed!=text.size() || parsed<0 ||
            parsed>std::numeric_limits<int>::max()) return false;
        value=static_cast<int>(parsed);
        return true;
    } catch (...) {
        return false;
    }
}

bool parse_nonnegative_long_long(const std::string& text,long long& value) {
    if (text.empty()) return false;
    std::size_t consumed=0;
    try {
        long long parsed=std::stoll(text,&consumed);
        if (consumed!=text.size() || parsed<0) return false;
        value=parsed;
        return true;
    } catch (...) {
        return false;
    }
}

bool parse_nonnegative_u64(const std::string& text,std::uint64_t& value) {
    if (text.empty() || text.front()=='-') return false;
    std::size_t consumed=0;
    try {
        unsigned long long parsed=std::stoull(text,&consumed);
        if (consumed!=text.size()) return false;
        value=static_cast<std::uint64_t>(parsed);
        return true;
    } catch (...) {
        return false;
    }
}

bool parse_branch_path(const std::string& text,std::vector<int>& path) {
    if (text.empty()) return false;
    std::stringstream stream(text);
    std::string item;
    while (std::getline(stream,item,',')) {
        int branch=-1;
        if (!parse_nonnegative_int(item,branch)) return false;
        path.push_back(branch);
    }
    return !path.empty();
}

int initialize_remaining_seed(Search& search,const std::string& mode) {
    if (mode=="g001_row0") {
        // Adjacent e1,e2; e4 meets neither.  The exposed forest is
        //     0 --1-- 1 --2-- 2       3 --4-- 4
        // with internal spectrum {1,2,3,4}, so the next physical edge is 5.
        search.add_edge(0,1,1);
        search.add_edge(1,2,2);
        search.add_edge(3,4,4);
        return 5;
    }
    if (mode=="g001_row3") {
        // Adjacent e1,e2; e4 meets both.  All three share the center 0.
        // The internal spectrum is {1,2,3,4,5,6}; next physical edge 7.
        search.add_edge(0,1,1);
        search.add_edge(0,2,2);
        search.add_edge(0,3,4);
        return 7;
    }
    if (mode=="g001_row4") {
        // Disjoint e1,e2; e3 meets neither: three weighted dimers.
        // The internal spectrum is {1,2,3}; next physical edge 4.
        search.add_edge(0,1,1);
        search.add_edge(2,3,2);
        search.add_edge(4,5,3);
        return 4;
    }
    if (mode=="g001_row5") {
        // Disjoint e1,e2; e3 meets only e1.
        //     0 --1-- 1 --3-- 2       3 --2-- 4
        // The internal spectrum is {1,2,3,4}; next physical edge 5.
        search.add_edge(0,1,1);
        search.add_edge(3,4,2);
        search.add_edge(1,2,3);
        return 5;
    }
    if (mode=="g001_row6") {
        // Disjoint e1,e2; e3 meets only e2.
        //     0 --1-- 1       2 --2-- 3 --3-- 4
        // The internal spectrum is {1,2,3,5}; next physical edge 4.
        search.add_edge(0,1,1);
        search.add_edge(2,3,2);
        search.add_edge(3,4,3);
        return 4;
    }
    return -1;
}

} // namespace

int main(int argc,char** argv) {
    std::ios::sync_with_stdio(false);
    std::cin.tie(nullptr);

    std::string mode;
    long long max_nodes=0;
    int root_branch=-1;
    int stop_edges=-1;
    std::vector<int> branch_path;
    bool use_multi_edge_cover=false;
    bool shadow_multi_edge_cover=false;
    a2_multi_cover::Config cover_config;

    for (int i=1;i<argc;i++) {
        std::string argument=argv[i];
        auto require_value=[&](const char* option)->std::string {
            if (i+1>=argc) {
                std::cerr<<option<<" requires a value\n";
                std::exit(64);
            }
            return argv[++i];
        };
        if (argument=="--mode") {
            mode=require_value("--mode");
        } else if (argument=="--max-nodes") {
            if (!parse_nonnegative_long_long(require_value("--max-nodes"),
                                             max_nodes)) {
                std::cerr<<"invalid --max-nodes\n";
                return 64;
            }
        } else if (argument=="--root-branch") {
            if (!parse_nonnegative_int(require_value("--root-branch"),
                                       root_branch)) {
                std::cerr<<"invalid --root-branch\n";
                return 64;
            }
        } else if (argument=="--branch-path") {
            if (!parse_branch_path(require_value("--branch-path"),branch_path)) {
                std::cerr<<"invalid --branch-path\n";
                return 64;
            }
        } else if (argument=="--stop-edges") {
            if (!parse_nonnegative_int(require_value("--stop-edges"),
                                       stop_edges)) {
                std::cerr<<"invalid --stop-edges\n";
                return 64;
            }
        } else if (argument=="--multi-edge-cover") {
            use_multi_edge_cover=true;
        } else if (argument=="--multi-edge-cover-shadow") {
            shadow_multi_edge_cover=true;
        } else if (argument=="--multi-edge-cover-local-max-components") {
            if (!parse_nonnegative_int(
                    require_value("--multi-edge-cover-local-max-components"),
                    cover_config.local_max_components)) {
                std::cerr<<"invalid local component limit\n";
                return 64;
            }
        } else if (argument=="--multi-edge-cover-max-components") {
            if (!parse_nonnegative_int(
                    require_value("--multi-edge-cover-max-components"),
                    cover_config.max_components)) {
                std::cerr<<"invalid component limit\n";
                return 64;
            }
        } else if (argument=="--multi-edge-cover-exact-max-components") {
            if (!parse_nonnegative_int(
                    require_value("--multi-edge-cover-exact-max-components"),
                    cover_config.exact_max_components)) {
                std::cerr<<"invalid exact component limit\n";
                return 64;
            }
        } else if (argument=="--multi-edge-cover-budget") {
            if (!parse_nonnegative_u64(
                    require_value("--multi-edge-cover-budget"),
                    cover_config.exact_state_budget)) {
                std::cerr<<"invalid cover budget\n";
                return 64;
            }
        } else if (argument=="--multi-edge-cover-candidate-cap") {
            if (!parse_nonnegative_u64(
                    require_value("--multi-edge-cover-candidate-cap"),
                    cover_config.exact_candidate_cap)) {
                std::cerr<<"invalid candidate cap\n";
                return 64;
            }
        } else if (argument=="--multi-edge-cover-no-hall") {
            cover_config.run_hall=false;
        } else if (argument=="--multi-edge-cover-no-exact") {
            cover_config.run_exact=false;
        } else if (argument=="--multi-edge-cover-no-exact-hall") {
            cover_config.exact_residual_hall=false;
        } else if (argument=="--multi-edge-cover-validate") {
            cover_config.validate_candidates=true;
        } else if (argument=="--help") {
            print_pilot_usage();
            return 0;
        } else {
            std::cerr<<"unsupported pilot argument: "<<argument<<"\n";
            return 64;
        }
    }

    if (!is_remaining_mode(mode)) {
        std::cerr<<"pilot requires one of the five remaining G001 modes\n";
        return 64;
    }
    if (stop_edges<3 || stop_edges>16) {
        std::cerr<<"diagnostic pilot requires --stop-edges in 3..16; "
                    "it cannot run a terminal census\n";
        return 64;
    }
    if (use_multi_edge_cover && shadow_multi_edge_cover) {
        std::cerr<<"choose active or shadow multi-edge cover, not both\n";
        return 64;
    }
    if (root_branch>=0 && !branch_path.empty()) {
        std::cerr<<"choose --root-branch or --branch-path, not both\n";
        return 64;
    }
    if ((root_branch>=0 || !branch_path.empty()) && stop_edges==3) {
        std::cerr<<"a branch selector requires --stop-edges at least 4\n";
        return 64;
    }
    if (branch_path.size()>static_cast<std::size_t>(stop_edges-3)) {
        std::cerr<<"branch path is deeper than the requested frontier\n";
        return 64;
    }
    const auto valid_component_limit=[](int value) {
        return value>=1 && value<=18;
    };
    if (!valid_component_limit(cover_config.local_max_components) ||
        !valid_component_limit(cover_config.max_components) ||
        !valid_component_limit(cover_config.exact_max_components) ||
        cover_config.exact_max_components>cover_config.max_components) {
        std::cerr<<"cover component thresholds must satisfy "
                    "1 <= exact <= max <= 18 and 1 <= local <= 18\n";
        return 64;
    }

    Search search(18);
    search.max_nodes=max_nodes;
    search.use_order18_parity=true;
    search.root_branch=root_branch;
    search.branch_path=branch_path;
    search.branch_path_base_depth=3;
    search.root_branch_depth=3;
    search.stop_edges=stop_edges;
    search.stop_at_first=true;
    search.use_multi_edge_cover=use_multi_edge_cover;
    search.shadow_multi_edge_cover=shadow_multi_edge_cover;
    search.multi_cover_config=cover_config;

    const int expected_seed_mex=initialize_remaining_seed(search,mode);
    const Search::Analysis seed_analysis=search.analyze();
    if (!seed_analysis.valid || seed_analysis.mex!=expected_seed_mex) {
        std::cerr<<"internal seed validation failed for "<<mode
                 <<" expected_mex="<<expected_seed_mex
                 <<" actual_mex="<<seed_analysis.mex<<"\n";
        return 70;
    }

    search.rec();
    search.print_result(mode);
    if (search.limit) return 3;
    if (!search.solution_topologies.empty()) {
        std::cerr<<"unexpected terminal solution in shallow-only pilot\n";
        return 2;
    }
    return 0;
}
