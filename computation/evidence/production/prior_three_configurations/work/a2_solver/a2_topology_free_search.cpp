#include <bits/stdc++.h>
#include "a2_multi_edge_exact_cover.hpp"
#include "a2_multi_edge_exact_cover_optimized.hpp"
#include "a2_multi_edge_stronger_relaxation.hpp"
using namespace std;

// Exact topology-free forced-mex search for Leech trees.
//
// At any prefix, the exposed physical edges form a forest.  T2a says that
// the next physical edge weight is the least positive integer missing from
// the internal distance spectrum of this forest.  Adding that edge merges
// two components, and all newly completed cross distances are known exactly.
// Thus every completion is generated without first choosing a final topology.

struct Bits {
    uint64_t a[3] = {0,0,0};
    bool get(int x) const { return (a[x>>6]>>(x&63))&1ULL; }
    void set(int x) { a[x>>6]|=1ULL<<(x&63); }
};

struct Edge { int u,v,w; };

struct Search {
    int n, target;
    long long max_nodes=0;
    bool use_order18_parity=false;
    bool stop_at_first=false;
    int root_branch=-1;
    int root_valid_branches=0;
    vector<int> branch_path;
    int branch_path_base_depth=4;
    array<int,18> valid_children_max{};
    int stop_edges=-1;
    int attached_equality_r=-1;
    int separate_equality_r=-1;
    bool use_multi_edge_cover=false;
    bool shadow_multi_edge_cover=false;
    a2_multi_cover::Config multi_cover_config;
    a2_multi_cover::Counters multi_cover_counters;
    a2_multi_cover::Checker multi_cover_checker;
    long long multi_cover_shadow_reject=0;
    // 0=off, 1=indexed Hall active, 2=indexed Hall shadow,
    // 3=mex-conditioned self-puncturing active, 4=its shadow mode.
    int stronger_cover_mode=0;
    a2_multi_cover_stronger::Config stronger_cover_config;
    a2_multi_cover_stronger::Counters stronger_cover_counters;
    a2_multi_cover_stronger::Checker stronger_cover_checker;
    long long stronger_cover_shadow_reject=0;
    bool use_exact_pack=false;
    bool shadow_exact_pack=false;
    a2_multi_cover_optimized::Config exact_pack_config;
    a2_multi_cover_optimized::Counters exact_pack_counters;
    a2_multi_cover_optimized::Checker exact_pack_checker;
    long long exact_pack_shadow_reject=0;
    int exact_pack_late_components=0;
    uint64_t exact_pack_late_budget=0;
    uint64_t exact_pack_late_arc_budget=0;
    long long frontier=0;
    map<int,long long> frontier_mex;
    map<int,long long> frontier_odd_count, frontier_third_odd;
    bool limit=false;
    long long nodes=0, accepted=0, generated=0, duplicate=0, collision=0, range_fail=0;
    long long parity_fail=0, diameter_fail=0;
    long long g002_fail=0, cut_lower_fail=0, cut_upper_fail=0;
    long long late_t9a_fail=0;
    vector<Edge> edges;
    vector<pair<int,int>> adj[18];
    unordered_set<string> solution_topologies;
    array<long long,18> depth_nodes{};

    explicit Search(int order): n(order), target(order*(order-1)/2) {
    }

    void add_edge(int u,int v,int w) {
        int id=(int)edges.size();
        edges.push_back({u,v,w});
        adj[u].push_back({v,id}); adj[v].push_back({u,id});
    }

    void pop_edge() {
        Edge e=edges.back(); edges.pop_back();
        adj[e.u].pop_back(); adj[e.v].pop_back();
    }

    string rooted_code(int u,int parent,int parent_weight,bool weighted) const {
        vector<string> parts;
        for (auto [v,id]:adj[u]) if (v!=parent)
            parts.push_back(rooted_code(v,u,edges[id].w,weighted));
        sort(parts.begin(),parts.end());
        string z;
        z.push_back((char)254);
        for (const string& p:parts) z+=p;
        z.push_back((char)255);
        if (parent>=0) z.push_back((char)(weighted?parent_weight:1));
        return z;
    }

    string forest_code(bool weighted=true) const {
        bool vis[18]={};
        vector<string> components;
        for (int s=0;s<n;s++) if (!vis[s]) {
            vector<int> vs, st={s}; vis[s]=true;
            while (!st.empty()) {
                int u=st.back(); st.pop_back(); vs.push_back(u);
                for (auto [v,id]:adj[u]) if (!vis[v]) {
                    vis[v]=true; st.push_back(v);
                }
            }
            string best;
            bool first=true;
            for (int r:vs) {
                string z=rooted_code(r,-1,0,weighted);
                if (first || z<best) { best=move(z); first=false; }
            }
            components.push_back(move(best));
        }
        sort(components.begin(),components.end());
        string z; z.push_back((char)250);
        for (const string& c:components) { z+=c; z.push_back((char)251); }
        z.push_back((char)252);
        return z;
    }

    struct Analysis {
        int comp[18];
        vector<vector<int>> vertices;
        int dist[18][18];
        int hop[18][18];
        Bits used;
        int mex=1;
        bool valid=true;
    };

    Analysis analyze() const {
        Analysis z;
        fill(z.comp,z.comp+n,-1);
        for (int i=0;i<n;i++) for (int j=0;j<n;j++)
            z.dist[i][j]=z.hop[i][j]=-1;
        for (int s=0;s<n;s++) if (z.comp[s]<0) {
            int cid=(int)z.vertices.size();
            z.vertices.push_back({});
            vector<int> st={s}; z.comp[s]=cid;
            while (!st.empty()) {
                int u=st.back(); st.pop_back(); z.vertices.back().push_back(u);
                for (auto [v,id]:adj[u]) if (z.comp[v]<0) {
                    z.comp[v]=cid; st.push_back(v);
                }
            }
        }
        for (int s=0;s<n;s++) {
            struct Item { int u,p,d,h; };
            vector<Item> st={{s,-1,0,0}};
            while (!st.empty()) {
                Item q=st.back(); st.pop_back();
                z.dist[s][q.u]=q.d; z.hop[s][q.u]=q.h;
                for (auto [v,id]:adj[q.u]) if (v!=q.p)
                    st.push_back({v,q.u,q.d+edges[id].w,q.h+1});
            }
        }
        for (int u=0;u<n;u++) for (int v=u+1;v<n;v++)
            if (z.comp[u]==z.comp[v]) {
                int d=z.dist[u][v];
                if (d<1 || d>target || z.used.get(d)) z.valid=false;
                else z.used.set(d);
            }
        while (z.mex<=target && z.used.get(z.mex)) z.mex++;
        return z;
    }

    a2_multi_cover::Input multi_cover_input(const Analysis& z) const {
        a2_multi_cover::Input in;
        in.n=n;
        in.target=target;
        in.mex=z.mex;
        in.components=z.vertices;
        for (int i=0;i<n;i++) for (int j=0;j<n;j++)
            in.distance[i][j]=z.dist[i][j];
        for (int d=1;d<=target;d++) if (!z.used.get(d)) in.missing.set(d);
        return in;
    }

    bool parity_profile_possible(const Analysis& z) const {
        if (!use_order18_parity) return true;
        bool possible[19]={}; possible[0]=true;
        for (const auto& vs:z.vertices) {
            int color[18]; fill(color,color+n,-1);
            int cnt[2]={0,0};
            int root=vs[0]; color[root]=0;
            vector<int> st={root};
            while (!st.empty()) {
                int u=st.back(); st.pop_back(); cnt[color[u]]++;
                for (auto [v,id]:adj[u]) if (color[v]<0) {
                    color[v]=color[u]^(edges[id].w&1); st.push_back(v);
                }
            }
            bool next[19]={};
            for (int k=0;k<=7;k++) if (possible[k])
                for (int flip=0;flip<2;flip++)
                    if (k+cnt[flip]<=7) next[k+cnt[flip]]=true;
            copy(next,next+19,possible);
        }
        return possible[7];
    }

    bool partial_hop_diameter_ok(const Analysis& z) const {
        if (n!=18) return true;
        for (int u=0;u<n;u++) for (int v=u+1;v<n;v++)
            if (z.comp[u]==z.comp[v] && z.hop[u][v]>14) return false;
        return true;
    }

    static long long progression_sum(int first,int count,int power) {
        long long z=0;
        for (int i=0;i<count;i++) {
            long long d=first+2*i;
            z+=power==1?d:power==2?d*d:d*d*d;
        }
        return z;
    }

    bool t9a_channel_ok(int w,int count,int parity) const {
        if (!count) return true;
        int first=((w&1)==parity)?w:w+1;
        if (first+2*(count-1)>153) return false;
        static constexpr long long moment[2][4]={
            {0,5852,596904,68491808},
            {0,5929,608685,70300153}
        };
        for (int p=1;p<=3;p++)
            if (progression_sum(first,count,p)>moment[parity][p]) return false;
        return true;
    }

    // From rank 14 onward only at most four forest components remain.  Choose
    // one coherent 7|11 orientation.  For an exposed edge, every other
    // current component must eventually lie wholly on one side of that edge.
    // We generously allow an independent subset choice for each edge.  If no
    // orientation makes every edge pass G002 and T9a under even this
    // relaxation, no final topology can complete the prefix.
    bool late_t9a_profile_possible(const Analysis& z) const {
        if (n!=18 || (int)edges.size()<14) return true;
        int comps=(int)z.vertices.size();
        int color[18]; fill(color,color+n,-1);
        int cnt[18][2]={{}};
        for (int cid=0;cid<comps;cid++) {
            int root=z.vertices[cid][0]; color[root]=0;
            vector<int> st={root};
            while (!st.empty()) {
                int u=st.back(); st.pop_back(); cnt[cid][color[u]]++;
                for (auto [v,id]:adj[u]) if (color[v]<0) {
                    color[v]=color[u]^(edges[id].w&1); st.push_back(v);
                }
            }
        }
        vector<int> negative_color(comps,0);
        bool any=false;
        function<void(int,int)> choose=[&](int cid,int negatives) {
            if (any || negatives>7) return;
            if (cid==comps) {
                if (negatives!=7) return;
                int sigma[18];
                int mass[18]={};
                for (int v=0;v<n;v++) {
                    int c=z.comp[v];
                    sigma[v]=(color[v]==negative_color[c])?-1:1;
                    mass[c]+=sigma[v];
                }
                for (int id=0;id<(int)edges.size();id++) {
                    const Edge& e=edges[id];
                    int home=z.comp[e.u];
                    bool side[18]={}; side[e.u]=true;
                    vector<int> st={e.u}; int side_size=0, side_mass=0;
                    while (!st.empty()) {
                        int u=st.back(); st.pop_back();
                        side_size++; side_mass+=sigma[u];
                        for (auto [v,j]:adj[u]) if (j!=id && !side[v]) {
                            side[v]=true; st.push_back(v);
                        }
                    }
                    vector<int> outside;
                    for (int c=0;c<comps;c++) if (c!=home) outside.push_back(c);
                    bool edge_ok=false;
                    for (int subset=0;subset<(1<<(int)outside.size());subset++) {
                        int s=side_size,x=side_mass;
                        for (int j=0;j<(int)outside.size();j++) if (subset>>j&1) {
                            int c=outside[j];
                            s+=(int)z.vertices[c].size(); x+=mass[c];
                        }
                        int cut=s*(18-s), kappa=x*(4-x);
                        if (((cut+kappa)&1) || ((cut-kappa)&1)) continue;
                        int even=(cut+kappa)/2, odd=(cut-kappa)/2;
                        if (even<0 || odd<0) continue;
                        int rank1=id+1;
                        if (e.w+cut+(17-rank1)>154) continue;
                        if (!t9a_channel_ok(e.w,even,0) ||
                            !t9a_channel_ok(e.w,odd,1)) continue;
                        edge_ok=true; break;
                    }
                    if (!edge_ok) return;
                }
                any=true; return;
            }
            for (int neg_color=0;neg_color<2;neg_color++) {
                negative_color[cid]=neg_color;
                choose(cid+1,negatives+cnt[cid][neg_color]);
            }
        };
        choose(0,0);
        return any;
    }

    // Necessary final-cut bounds while the topology is still incomplete.
    // Removing an exposed edge splits its current component into sizes a,b.
    // The vertices outside that component may eventually attach on either
    // side, so the final side size lies in [a,n-b].  Optimizing s(n-s) on
    // that interval gives safe bounds for T4 and G002.
    int structural_cut_bounds(const Analysis& z) const {
        long long lower=0, upper=0;
        for (int id=0;id<(int)edges.size();id++) {
            const Edge& e=edges[id];
            bool vis[18]={}; vis[e.u]=true;
            vector<int> st={e.u}; int a=0;
            while (!st.empty()) {
                int u=st.back(); st.pop_back(); a++;
                for (auto [v,j]:adj[u]) if (j!=id && !vis[v]) {
                    vis[v]=true; st.push_back(v);
                }
            }
            int component_size=(int)z.vertices[z.comp[e.u]].size();
            int b=component_size-a;
            int lo=a, hi=n-b;
            auto cut=[&](int s) { return s*(n-s); };
            int minc=min(cut(lo),cut(hi));
            int best=min(max(n/2,lo),hi);
            int maxc=cut(best);
            if (n==18) {
                int rank1=id+1;
                int g002_upper=154-e.w-(17-rank1);
                if (minc>g002_upper) return 1;
            }
            lower+=1LL*minc*e.w;
            upper+=1LL*maxc*e.w;
        }
        int remaining=(n-1)-(int)edges.size();
        vector<int> future;
        for (int d=z.mex;d<=target;d++) if (!z.used.get(d)) future.push_back(d);
        if ((int)future.size()<remaining) return 2;
        long long small=0,large=0;
        for (int i=0;i<remaining;i++) {
            small+=future[i];
            large+=future[future.size()-1-i];
        }
        lower+=1LL*(n-1)*small;
        int maxcut=(n/2)*(n-n/2);
        upper+=1LL*maxcut*large;
        long long checksum=1LL*target*(target+1)/2;
        if (lower>checksum) return 2;
        if (upper<checksum) return 3;
        return 0;
    }

    bool candidate_cross_ok(const Analysis& z,int u,int v,int w) const {
        Bits fresh;
        const auto& A=z.vertices[z.comp[u]];
        const auto& B=z.vertices[z.comp[v]];
        for (int a:A) for (int b:B) {
            int d=z.dist[a][u]+w+z.dist[v][b];
            if (d<1 || d>target) return false;
            if (z.used.get(d) || fresh.get(d)) return false;
            fresh.set(d);
        }
        return true;
    }

    // Necessary even-component profiles at simultaneous equality.  The
    // selected checking mode supplies r and chooses attached q3=13 or
    // separate/nonadjacent q3=9.  All ordinary modes leave both values -1.
    bool equality_profile_possible() const {
        int selected_r=attached_equality_r>=0
            ? attached_equality_r : separate_equality_r;
        if (selected_r<0) return true;
        int odd=0;
        for (const Edge& e:edges) odd+=(e.w&1);
        int even=(int)edges.size()-odd;
        int remaining=17-(int)edges.size();
        if (odd>selected_r || odd+remaining<selected_r ||
            even>17-selected_r) return false;

        int parent[18];
        iota(parent,parent+n,0);
        function<int(int)> find=[&](int x) {
            return parent[x]==x?x:parent[x]=find(parent[x]);
        };
        auto unite=[&](int x,int y) {
            x=find(x); y=find(y);
            if (x!=y) parent[y]=x;
        };
        for (const Edge& e:edges) if (!(e.w&1)) unite(e.u,e.v);

        int size[18]={};
        for (int v=0;v<n;v++) size[find(v)]++;
        int c0=find(0), c1=find(1), c2=find(2), c3=find(3), c4=find(4);
        if (size[c0]!=1 || size[c4]!=1) return false;
        if (separate_equality_r>=0 && size[find(5)]!=1) return false;
        if (c1!=c2 || c2!=c3 || size[c1]!=3) return false;
        for (int v=0;v<n;v++) if (find(v)==v && v!=c1 && size[v]>2)
            return false;
        return true;
    }

    bool rec() {
        nodes++;
        if (max_nodes && nodes>max_nodes) { limit=true; return false; }
        depth_nodes[edges.size()]++;
        Analysis z=analyze();
        if (!z.valid) return false;
        if (!partial_hop_diameter_ok(z)) { diameter_fail++; return false; }
        if (!parity_profile_possible(z)) { parity_fail++; return false; }
        if (!equality_profile_possible()) return false;
        int selected_equality_r=attached_equality_r>=0
            ? attached_equality_r : separate_equality_r;
        if (selected_equality_r>=0 && (int)edges.size()<17) {
            int odd=0;
            for (const Edge& e:edges) odd+=(e.w&1);
            int remaining=17-(int)edges.size();
            int need_odd=selected_equality_r-odd;
            int need_even=remaining-need_odd;
            // In forced-mex order the next edge has parity z.mex.  If that
            // parity's exact equality-profile quota is already exhausted,
            // this prefix cannot have a child in the selected r case.
            if (((z.mex&1) && need_odd==0) ||
                (!(z.mex&1) && need_even==0)) return false;
        }
        if (use_multi_edge_cover || shadow_multi_edge_cover) {
            a2_multi_cover::Outcome cover=multi_cover_checker.check(
                multi_cover_input(z),multi_cover_config,multi_cover_counters);
            if (!cover.possible) {
                if (shadow_multi_edge_cover) multi_cover_shadow_reject++;
                else return false;
            }
        }
        if (stronger_cover_mode) {
            a2_multi_cover_stronger::Config config=stronger_cover_config;
            config.run_mex_conditioned=stronger_cover_mode>=3;
            auto outcome=stronger_cover_checker.check(
                multi_cover_input(z),config,stronger_cover_counters);
            if (!outcome.possible) {
                bool shadow=stronger_cover_mode==2 || stronger_cover_mode==4;
                if (shadow) stronger_cover_shadow_reject++;
                else return false;
            }
        }
        if (use_exact_pack || shadow_exact_pack) {
            auto config=exact_pack_config;
            if (exact_pack_late_components>0 &&
                (int)z.vertices.size()<=exact_pack_late_components) {
                if (exact_pack_late_budget)
                    config.state_budget=exact_pack_late_budget;
                if (exact_pack_late_arc_budget)
                    config.root_arc_comparison_budget=exact_pack_late_arc_budget;
            }
            auto outcome=exact_pack_checker.check(
                multi_cover_input(z),config,exact_pack_counters);
            if (!outcome.possible) {
                if (shadow_exact_pack) exact_pack_shadow_reject++;
                else return false;
            }
        }
        // The late independent T9a relaxation was measured separately and
        // produced zero rejections, so it is not kept in the hot path.
        // The sampled cut relaxation produced no rejection and is omitted
        // from the hot path.  Every prefix has a unique predecessor obtained
        // by deleting its largest physical edge, so separate parent branches
        // cannot reconverge.  The exact orbit reduction below removes the
        // only duplicates, namely symmetric attachment choices in one parent.
        accepted++;

        if (stop_edges>=0 && (int)edges.size()==stop_edges) {
            frontier++;
            frontier_mex[z.mex]++;
            int odd=0,third=-1;
            for (const Edge& e:edges) if (e.w&1) {
                odd++; if (odd==3) third=e.w;
            }
            frontier_odd_count[odd]++;
            frontier_third_odd[third]++;
            return false;
        }

        if ((int)edges.size()==n-1) {
            if (z.mex==target+1) {
                solution_topologies.insert(forest_code(false));
                return stop_at_first;
            }
            return false;
        }
        if (z.mex>target) return false;

        struct Candidate { int score,u,v; };
        vector<Candidate> cand;
        // Exact automorphism-orbit reduction.  Equal unrooted component codes
        // identify interchangeable components; equal rooted codes identify
        // interchangeable attachment ports inside one weighted tree.
        vector<string> component_code(z.vertices.size());
        vector<vector<int>> port_reps(z.vertices.size());
        vector<string> root_signature(n);
        map<string,vector<int>> component_types;
        for (int cid=0;cid<(int)z.vertices.size();cid++) {
            bool first=true;
            map<string,int> roots;
            for (int v:z.vertices[cid]) {
                string rc=rooted_code(v,-1,0,true);
                root_signature[v]=rc;
                if (first || rc<component_code[cid]) {
                    component_code[cid]=rc; first=false;
                }
                roots.emplace(rc,v);
            }
            for (auto &kv:roots) port_reps[cid].push_back(kv.second);
            component_types[component_code[cid]].push_back(cid);
        }
        vector<pair<string,vector<int>>> types(component_types.begin(),component_types.end());
        for (int ta=0;ta<(int)types.size();ta++)
            for (int tb=ta;tb<(int)types.size();tb++) {
                if (ta==tb && types[ta].second.size()<2) continue;
                int ca=types[ta].second[0];
                int cb=ta==tb ? types[tb].second[1] : types[tb].second[0];
                for (int u:port_reps[ca]) for (int v:port_reps[cb]) {
                    if (ta==tb) {
                        if (root_signature[v]<root_signature[u]) continue;
                    }
                    int score=-(int)(z.vertices[ca].size()*z.vertices[cb].size());
                    cand.push_back({score,u,v});
                }
            }
        sort(cand.begin(),cand.end(),[](const Candidate&a,const Candidate&b){
            return tie(a.score,a.u,a.v)<tie(b.score,b.u,b.v);
        });
        int valid_at_node=0;
        for (auto q:cand) {
            generated++;
            if (!candidate_cross_ok(z,q.u,q.v,z.mex)) {
                // The distinction is diagnostic only; both failures are exact.
                const auto& A=z.vertices[z.comp[q.u]];
                const auto& B=z.vertices[z.comp[q.v]];
                bool out=false;
                for (int a:A) for (int b:B)
                    out|=z.dist[a][q.u]+z.mex+z.dist[q.v][b]>target;
                if (out) range_fail++; else collision++;
                continue;
            }
            int branch=valid_at_node++;
            valid_children_max[edges.size()]=max(
                valid_children_max[edges.size()],valid_at_node);
            int path_index=(int)edges.size()-branch_path_base_depth;
            if (path_index>=0 && path_index<(int)branch_path.size() &&
                branch!=branch_path[path_index]) continue;
            int root_depth=attached_equality_r>=0 ? 6
                : (separate_equality_r>=0 ? 5 : 4);
            if ((int)edges.size()==root_depth) {
                root_valid_branches=max(root_valid_branches,valid_at_node);
                if (root_branch>=0 && branch!=root_branch) continue;
            }
            add_edge(q.u,q.v,z.mex);
            bool done=rec();
            pop_edge();
            if (done || limit) return done;
        }
        return false;
    }

    void reset() {
        edges.clear();
        for (int i=0;i<18;i++) adj[i].clear();
    }

    void print_result(const string& mode) const {
        string status=limit?"LIMIT":stop_edges>=0?"FRONTIER":
                      solution_topologies.empty()?"ZERO":"FOUND";
        cout<<"RESULT mode="<<mode
            <<" status="<<status
            <<" nodes="<<nodes<<" states="<<accepted
            <<" generated="<<generated<<" duplicate="<<duplicate
            <<" collision="<<collision<<" range="<<range_fail
            <<" parity="<<parity_fail<<" diameter="<<diameter_fail
            <<" g002="<<g002_fail<<" cutlower="<<cut_lower_fail
            <<" cutupper="<<cut_upper_fail
            <<" late_t9a="<<late_t9a_fail
            <<" solution_topologies="<<solution_topologies.size()<<" depth=";
        for (int i=0;i<n;i++) if (depth_nodes[i]) cout<<i<<":"<<depth_nodes[i]<<",";
        cout<<" root_valid="<<root_valid_branches<<" frontier="<<frontier
            <<" frontier_mex=";
        for (auto [k,c]:frontier_mex) cout<<k<<":"<<c<<",";
        cout<<" frontier_odd=";
        for (auto [k,c]:frontier_odd_count) cout<<k<<":"<<c<<",";
        cout<<" frontier_q3=";
        for (auto [k,c]:frontier_third_odd) cout<<k<<":"<<c<<",";
        if (use_multi_edge_cover || shadow_multi_edge_cover) {
            const auto& c=multi_cover_counters;
            cout<<" multi_cover="<<(use_multi_edge_cover?"on":"shadow")
                <<" cover_checks="<<c.checks
                <<" cover_skipped="<<c.skipped_early
                <<" cover_skipped_full="<<c.skipped_full
                <<" cover_local_slots="<<c.local_component_pair_slots
                <<" cover_local_patterns="<<c.local_port_patterns
                <<" cover_slots="<<c.component_pair_slots
                <<" cover_patterns="<<c.port_patterns
                <<" cover_candidates="<<c.candidate_blocks
                <<" cover_no_candidate="<<c.no_candidate_fail
                <<" cover_hall_fail="<<c.hall_fail
                <<" cover_exact_calls="<<c.exact_calls
                <<" cover_exact_fail="<<c.exact_fail
                <<" cover_exact_pass="<<c.exact_pass
                <<" cover_exact_budget="<<c.exact_budget_pass
                <<" cover_exact_cap="<<c.exact_cap_pass
                <<" cover_exact_states="<<c.exact_states
                <<" cover_exact_hall_fail="<<c.exact_hall_fail
                <<" cover_validation_fail="<<c.validation_fail
                <<" cover_shadow_reject="<<multi_cover_shadow_reject;
        }
        if (stronger_cover_mode) {
            const auto& c=stronger_cover_counters;
            const char* label=stronger_cover_mode==1?"indexed":
                stronger_cover_mode==2?"indexed_shadow":
                stronger_cover_mode==3?"self_puncture":"self_puncture_shadow";
            cout<<" stronger_cover="<<label
                <<" stronger_checks="<<c.checks
                <<" stronger_skipped="<<c.skipped_early
                <<" stronger_families="<<c.families
                <<" stronger_patterns="<<c.port_length_patterns
                <<" stronger_slots="<<c.indexed_slots
                <<" stronger_translation_calls="<<c.translation_matching_calls
                <<" stronger_translation_fail="<<c.translation_matching_fail
                <<" stronger_indexed_calls="<<c.indexed_matching_calls
                <<" stronger_indexed_fail="<<c.indexed_matching_fail
                <<" stronger_owner_blocks="<<c.mex_owner_blocks
                <<" stronger_owner_branches="<<c.mex_owner_branches
                <<" stronger_owner_hall_fail="<<c.mex_owner_hall_fail
                <<" stronger_owner_fail="<<c.mex_owner_fail
                <<" stronger_cap_pass="<<c.cap_pass
                <<" stronger_budget_pass="<<c.budget_pass
                <<" stronger_scans="<<c.matching_edge_scans
                <<" stronger_shadow_reject="<<stronger_cover_shadow_reject;
        }
        if (use_exact_pack || shadow_exact_pack) {
            const auto& c=exact_pack_counters;
            cout<<" exact_pack="<<(use_exact_pack?"on":"shadow")
                <<" pack_checks="<<c.checks
                <<" pack_skipped="<<c.skipped
                <<" pack_no_candidate="<<c.no_candidate_fail
                <<" pack_fail="<<c.exact_fail
                <<" pack_pass="<<c.exact_pass
                <<" pack_unknown="<<c.exact_unknown
                <<" pack_candidates="<<c.generated_candidates
                <<" pack_raw_families="<<c.raw_families
                <<" pack_generic_families="<<c.generic_families
                <<" pack_classes="<<c.symmetry_classes
                <<" pack_symmetry_saved="<<c.symmetry_families_saved
                <<" pack_arc_rounds="<<c.arc_rounds
                <<" pack_arc_comparisons="<<c.arc_comparisons
                <<" pack_arc_removed="<<c.arc_removed
                <<" pack_states="<<c.states
                <<" pack_memo_hits="<<c.memo_hits
                <<" pack_capacity_fail="<<c.local_capacity_fail
                <<" pack_subset_hall_fail="<<c.subset_hall_fail
                <<" pack_shadow_reject="<<exact_pack_shadow_reject;
        }
        cout<<" child_max=";
        for (int i=0;i<n;i++) if (valid_children_max[i])
            cout<<i<<":"<<valid_children_max[i]<<",";
        cout<<"\n";
    }
};

int main(int argc,char**argv) {
    ios::sync_with_stdio(false); cin.tie(nullptr);
    string mode="a2"; long long max_nodes=0;
    int root_branch=-1,stop_edges=-1,equality_r=-1;
    vector<int> branch_path;
    bool use_multi_edge_cover=false,shadow_multi_edge_cover=false;
    a2_multi_cover::Config multi_cover_config;
    int stronger_cover_mode=0;
    a2_multi_cover_stronger::Config stronger_cover_config;
    bool use_exact_pack=false,shadow_exact_pack=false;
    a2_multi_cover_optimized::Config exact_pack_config;
    int exact_pack_late_components=0;
    uint64_t exact_pack_late_budget=0,exact_pack_late_arc_budget=0;
    for (int i=1;i<argc;i++) {
        string s=argv[i];
        if (s=="--mode" && i+1<argc) mode=argv[++i];
        else if (s=="--max-nodes" && i+1<argc) max_nodes=stoll(argv[++i]);
        else if (s=="--root-branch" && i+1<argc) root_branch=stoi(argv[++i]);
        else if (s=="--branch-path" && i+1<argc) {
            string item,input=argv[++i];
            stringstream stream(input);
            while (getline(stream,item,',')) {
                if (item.empty()) { cerr<<"bad branch path\n"; return 64; }
                branch_path.push_back(stoi(item));
            }
        }
        else if (s=="--stop-edges" && i+1<argc) stop_edges=stoi(argv[++i]);
        else if (s=="--equality-r" && i+1<argc) equality_r=stoi(argv[++i]);
        else if (s=="--multi-edge-cover") use_multi_edge_cover=true;
        else if (s=="--multi-edge-cover-shadow") shadow_multi_edge_cover=true;
        else if (s=="--multi-edge-cover-local-max-components" && i+1<argc)
            multi_cover_config.local_max_components=stoi(argv[++i]);
        else if (s=="--multi-edge-cover-max-components" && i+1<argc)
            multi_cover_config.max_components=stoi(argv[++i]);
        else if (s=="--multi-edge-cover-exact-max-components" && i+1<argc)
            multi_cover_config.exact_max_components=stoi(argv[++i]);
        else if (s=="--multi-edge-cover-budget" && i+1<argc)
            multi_cover_config.exact_state_budget=stoull(argv[++i]);
        else if (s=="--multi-edge-cover-candidate-cap" && i+1<argc)
            multi_cover_config.exact_candidate_cap=stoull(argv[++i]);
        else if (s=="--multi-edge-cover-no-hall") multi_cover_config.run_hall=false;
        else if (s=="--multi-edge-cover-no-exact") multi_cover_config.run_exact=false;
        else if (s=="--multi-edge-cover-no-exact-hall")
            multi_cover_config.exact_residual_hall=false;
        else if (s=="--multi-edge-cover-validate")
            multi_cover_config.validate_candidates=true;
        else if (s=="--multi-edge-indexed-hall") stronger_cover_mode=1;
        else if (s=="--multi-edge-indexed-hall-shadow") stronger_cover_mode=2;
        else if (s=="--multi-edge-self-puncture") stronger_cover_mode=3;
        else if (s=="--multi-edge-self-puncture-shadow") stronger_cover_mode=4;
        else if (s=="--multi-edge-stronger-max-components" && i+1<argc)
            stronger_cover_config.max_components=stoi(argv[++i]);
        else if (s=="--multi-edge-owner-cap" && i+1<argc)
            stronger_cover_config.max_mex_owner_blocks=stoull(argv[++i]);
        else if (s=="--multi-edge-matching-budget" && i+1<argc)
            stronger_cover_config.matching_work_budget=stoull(argv[++i]);
        else if (s=="--multi-edge-no-translation-hall")
            stronger_cover_config.run_translation_hall=false;
        else if (s=="--multi-edge-exact-pack") use_exact_pack=true;
        else if (s=="--multi-edge-exact-pack-shadow") shadow_exact_pack=true;
        else if (s=="--multi-edge-exact-pack-max-components" && i+1<argc)
            exact_pack_config.max_components=stoi(argv[++i]);
        else if (s=="--multi-edge-exact-pack-budget" && i+1<argc)
            exact_pack_config.state_budget=stoull(argv[++i]);
        else if (s=="--multi-edge-exact-pack-arc-budget" && i+1<argc)
            exact_pack_config.root_arc_comparison_budget=stoull(argv[++i]);
        else if (s=="--multi-edge-exact-pack-no-arc")
            exact_pack_config.root_arc_consistency=false;
        else if (s=="--multi-edge-exact-pack-subset-classes" && i+1<argc)
            exact_pack_config.dynamic_subset_hall_max_classes=stoi(argv[++i]);
        else if (s=="--multi-edge-exact-pack-late-components" && i+1<argc)
            exact_pack_late_components=stoi(argv[++i]);
        else if (s=="--multi-edge-exact-pack-late-budget" && i+1<argc)
            exact_pack_late_budget=stoull(argv[++i]);
        else if (s=="--multi-edge-exact-pack-late-arc-budget" && i+1<argc)
            exact_pack_late_arc_budget=stoull(argv[++i]);
        else if (s=="--help") {
            cout<<"Usage: a2_topology_free_search "
                  "[--mode a2|a2_separate|a2_attached|a2_attached_equality|"
                  "a2_separate_equality|small] "
                  "[--equality-r R] [--max-nodes N] [--stop-edges E] "
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
                  "[--multi-edge-cover-validate] "
                  "[--multi-edge-indexed-hall|--multi-edge-indexed-hall-shadow|"
                  "--multi-edge-self-puncture|--multi-edge-self-puncture-shadow] "
                  "[--multi-edge-stronger-max-components K] "
                  "[--multi-edge-owner-cap N] "
                  "[--multi-edge-matching-budget N] "
                  "[--multi-edge-no-translation-hall]\n";
            cout<<"       [--multi-edge-exact-pack|"
                  "--multi-edge-exact-pack-shadow] "
                  "[--multi-edge-exact-pack-max-components K] "
                  "[--multi-edge-exact-pack-budget N] "
                  "[--multi-edge-exact-pack-arc-budget N] "
                  "[--multi-edge-exact-pack-no-arc] "
                  "[--multi-edge-exact-pack-subset-classes K] "
                  "[--multi-edge-exact-pack-late-components K] "
                  "[--multi-edge-exact-pack-late-budget N] "
                  "[--multi-edge-exact-pack-late-arc-budget N]\n";
            return 0;
        } else { cerr<<"bad argument\n"; return 64; }
    }
    if (use_multi_edge_cover && shadow_multi_edge_cover) {
        cerr<<"choose either active or shadow multi-edge cover, not both\n";
        return 64;
    }
    if (root_branch>=0 && !branch_path.empty()) {
        cerr<<"choose either --root-branch or --branch-path, not both\n";
        return 64;
    }
    if (use_exact_pack && shadow_exact_pack) {
        cerr<<"choose either active or shadow exact packing, not both\n";
        return 64;
    }
    if (multi_cover_config.local_max_components<1 ||
        multi_cover_config.local_max_components>18 ||
        multi_cover_config.max_components<1 ||
        multi_cover_config.max_components>18 ||
        multi_cover_config.exact_max_components<1 ||
        multi_cover_config.exact_max_components>18) {
        cerr<<"multi-edge component thresholds must be in 1..18\n";
        return 64;
    }
    if (stronger_cover_config.max_components<1 ||
        stronger_cover_config.max_components>18) {
        cerr<<"stronger multi-edge component threshold must be in 1..18\n";
        return 64;
    }
    if (exact_pack_config.max_components<1 ||
        exact_pack_config.max_components>18 ||
        exact_pack_config.dynamic_subset_hall_max_classes<0 ||
        exact_pack_config.dynamic_subset_hall_max_classes>18) {
        cerr<<"invalid exact-packing component/class threshold\n";
        return 64;
    }
    if (exact_pack_late_components<0 || exact_pack_late_components>18) {
        cerr<<"invalid exact-packing late component threshold\n";
        return 64;
    }
    if (mode=="small") {
        const int expected[7]={0,0,1,1,2,0,1};
        for (int n=2;n<=6;n++) {
            Search s(n);
            s.use_multi_edge_cover=use_multi_edge_cover;
            s.shadow_multi_edge_cover=shadow_multi_edge_cover;
            s.multi_cover_config=multi_cover_config;
            s.stronger_cover_mode=stronger_cover_mode;
            s.stronger_cover_config=stronger_cover_config;
            s.use_exact_pack=use_exact_pack;
            s.shadow_exact_pack=shadow_exact_pack;
            s.exact_pack_config=exact_pack_config;
            s.exact_pack_late_components=exact_pack_late_components;
            s.exact_pack_late_budget=exact_pack_late_budget;
            s.exact_pack_late_arc_budget=exact_pack_late_arc_budget;
            s.rec();
            cout<<"SMALL order="<<n<<" topologies="<<s.solution_topologies.size()
                <<" nodes="<<s.nodes;
            if (use_multi_edge_cover || shadow_multi_edge_cover)
                cout<<" cover_no_candidate="<<s.multi_cover_counters.no_candidate_fail
                    <<" cover_hall_fail="<<s.multi_cover_counters.hall_fail
                    <<" cover_exact_fail="<<s.multi_cover_counters.exact_fail
                    <<" cover_exact_unknown="
                    <<s.multi_cover_counters.exact_budget_pass;
            cout<<"\n";
            if ((int)s.solution_topologies.size()!=expected[n]) return 1;
        }
        cout<<"TOPOLOGY_FREE_SMALL_ORDER_OK\n";
        return 0;
    }
    if (mode!="a2" && mode!="a2_separate" && mode!="a2_attached" &&
        mode!="a2_attached_equality" && mode!="a2_separate_equality") {
        cerr<<"invalid mode\n"; return 64;
    }
    if (mode=="a2_attached_equality" && (equality_r<9 || equality_r>13)) {
        cerr<<"a2_attached_equality requires --equality-r 9..13\n";
        return 64;
    }
    if (mode=="a2_separate_equality" &&
        (equality_r<10 || equality_r>14)) {
        cerr<<"a2_separate_equality requires --equality-r 10..14\n";
        return 64;
    }

    Search s(18); s.max_nodes=max_nodes; s.use_order18_parity=true;
    s.use_multi_edge_cover=use_multi_edge_cover;
    s.shadow_multi_edge_cover=shadow_multi_edge_cover;
    s.multi_cover_config=multi_cover_config;
    s.stronger_cover_mode=stronger_cover_mode;
    s.stronger_cover_config=stronger_cover_config;
    s.use_exact_pack=use_exact_pack;
    s.shadow_exact_pack=shadow_exact_pack;
    s.exact_pack_config=exact_pack_config;
    s.exact_pack_late_components=exact_pack_late_components;
    s.exact_pack_late_budget=exact_pack_late_budget;
    s.exact_pack_late_arc_budget=exact_pack_late_arc_budget;
    s.root_branch=root_branch;
    s.branch_path=branch_path;
    s.branch_path_base_depth=(mode=="a2_attached_equality"?6:
        mode=="a2_separate_equality"?5:4);
    s.stop_edges=stop_edges;
    s.stop_at_first=true;
    if (mode=="a2_attached_equality") s.attached_equality_r=equality_r;
    if (mode=="a2_separate_equality") s.separate_equality_r=equality_r;

    if (mode=="a2_attached_equality") {
        // Equality forces weights 8 and 10 to be separate dimers; their
        // prefix has mex 13.
        s.add_edge(0,1,1); s.add_edge(1,2,2); s.add_edge(2,3,4);
        s.add_edge(3,4,5); s.add_edge(5,6,8); s.add_edge(7,8,10);
        s.rec();
    } else if (mode=="a2_separate_equality") {
        // Equality forces x0 and both weight-5 endpoints to be singleton
        // even components; weight 8 is a separate dimer and mex is 9.
        s.add_edge(0,1,1); s.add_edge(1,2,2); s.add_edge(2,3,4);
        s.add_edge(4,5,5); s.add_edge(6,7,8);
        s.rec();
    } else if (mode!="a2_attached") {
        // A2 prefix I: e5 is a separate component from the 1-2-4 chain.
        s.add_edge(0,1,1); s.add_edge(1,2,2); s.add_edge(2,3,4);
        s.add_edge(4,5,5);
        s.rec();
    }

    // A2 prefix II: e5 meets e4 at its far endpoint but meets neither e1 nor e2.
    if (mode!="a2_attached_equality" && mode!="a2_separate_equality" &&
        mode!="a2_separate" &&
        !s.limit && s.solution_topologies.empty()) {
        s.reset();
        s.add_edge(0,1,1); s.add_edge(1,2,2); s.add_edge(2,3,4);
        s.add_edge(3,4,5);
        s.rec();
    }
    s.print_result(mode);
    if (s.limit) return 3;
    return s.solution_topologies.empty()?0:2;
}
