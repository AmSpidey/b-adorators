#include <iostream>
#include <vector>
#include <fstream>
#include <unordered_map>
#include <limits>
#include <queue>
#include <unordered_set>
#include <functional>
#include <thread>
#include <mutex>
#include <algorithm>
#include <condition_variable>
#include <atomic>
#include "blimit.hpp"

#define edge_set first
#define ver_sequence_number second
#define b_num second
#define weight_num second

struct pair_for_at {
    pair_for_at(int i, int i1) : l(i), r(i1) {

    }

    pair_for_at() = default;

    int l;
    int r;
};


typedef int weight;
typedef int neighbour;
typedef int b_number;
typedef int seq_num;
typedef std::pair<neighbour, weight> edge;
typedef std::pair<std::vector<edge>, b_number> vertex;
typedef std::vector<vertex> graph;
typedef std::unordered_map<b_number, seq_num> index_converter;
typedef std::unordered_set<seq_num> ver_queue;
typedef std::unique_lock<std::mutex> loczeq;
typedef std::vector<std::unordered_map<seq_num, weight>> weighing_neighs;

void add_vertex(graph &g, vertex &v) {
    g.push_back(v);
}

edge create_edge(neighbour n, weight w) {
    return {n, w};
}

void find_seq_num(index_converter &i, index_converter::iterator b_seq_b, seq_num &seq_b,
                  index_converter::iterator a_seq_a) {
    if (i.end() == b_seq_b) {
        if (i.end() == a_seq_a) {
            seq_b = i.size() + 1;
        } else {
            seq_b = i.size();
        }
    } else {
        seq_b = b_seq_b->second;
    }
}

void create_edge(index_converter &i, graph &g, weighing_neighs &neighs, b_number a, b_number b, weight w) {
    auto b_seq_b = i.find(b);
    auto a_seq_a = i.find(a);
    seq_num seq_b;
    find_seq_num(i, b_seq_b, seq_b, a_seq_a);

    if (i.end() == a_seq_a) {
        vertex v;
        v.b_num = a;
        v.edge_set.push_back(create_edge(seq_b, w));
        neighs.emplace_back();
        add_vertex(g, v);
        i.emplace(a, g.size() - 1);
        neighs.rbegin()->emplace(seq_b, w);
    } else {
        seq_num seq_a = i.find(a)->ver_sequence_number;
        g[seq_a].edge_set.push_back(create_edge(seq_b, w));
        neighs[seq_a].emplace(seq_b, w);
    }
}

void add_edges(index_converter &i, graph &g, weighing_neighs &neighs, neighbour a, neighbour b, weight w) {
    create_edge(i, g, neighs, a, b, w);
    create_edge(i, g, neighs, b, a, w);
}

bool f_smaller(edge fe, edge se, graph &g) {
    return (fe.weight_num < se.weight_num ||
            (fe.weight_num == se.weight_num &&
             g[fe.first].second < g[se.first].second));
}

void graph_reader(graph &g, weighing_neighs &neighs, const std::string &input_filename) {
    neighbour vertex_a;
    neighbour vertex_b;
    weight w;
    index_converter i;
    std::ifstream file(input_filename);
    while (file.peek() == '#') {
        file.ignore(std::numeric_limits<std::streamsize>::max(), '\n');
    }
    while (file >> vertex_a >> vertex_b >> w) {
        add_edges(i, g, neighs, vertex_a, vertex_b, w);
    }
    std::function<bool(edge, edge)> cmp = [&](edge fe, edge se) {
        return !(f_smaller(fe, se, g));
    };

    for (int j = 0; j <= g.size() - 1; j++) {
        std::sort(g[j].edge_set.begin(), g[j].edge_set.end(), cmp);
    }
}

int b_suitor(graph &g, const weighing_neighs &neighs, unsigned int method, int thread_count) {

    ver_queue Q;
    ver_queue R;

    std::function<bool(edge, edge)> cmp = [&](edge fe, edge se) {
        return !(f_smaller(fe, se, g));
    };
    std::atomic<int> b_sum(0);
    std::vector<std::priority_queue<edge, std::vector<edge>, decltype(cmp)>>
            S(g.size(), std::priority_queue<edge, std::vector<edge>, decltype(cmp)>(cmp));
    std::vector<std::atomic<int>> T(g.size());
    std::vector<int> Best_Choice(g.size());
    std::vector<std::atomic<pair_for_at>> top_and_size(g.size());

    for (int iter = 0; iter < g.size(); iter++) {
        Q.insert(iter);
    }

    std::mutex q_mutex;
    std::mutex r_mutex;
    std::vector<std::mutex> edgy_mutex(g.size());

    auto looper = [&](int queue_size) {
        ver_queue Qt;
        ver_queue Rt;
        std::unique_lock<std::mutex> q_lk(q_mutex);

        for (int iterator = 0; iterator < queue_size; iterator++) {
            Qt.emplace(*Q.begin());
            Q.erase(Q.begin());
        }
        q_lk.unlock();

        while (!Qt.empty()) {

            seq_num u = *Qt.begin();
            Qt.erase(u);
            while (T[u] < bvalue(method, g[u].b_num)) {
                edge curr_max = {-1, -1};
                for (int &j = Best_Choice[u]; j <= g[u].edge_set.size() - 1; j++) {
                    edge v = g[u].edge_set[Best_Choice[u]];
                    if (bvalue(method, g[v.first].b_num) == 0) continue;

                    auto current_top_and_size = top_and_size[v.first].load();
                    if (current_top_and_size.r >= bvalue(method, g[v.first].b_num)) {
                        edge S_last = {current_top_and_size.l, neighs[v.first].at(current_top_and_size.l)};
                        if (!f_smaller(std::make_pair(u, v.second), S_last, g)) {
                            curr_max = v;
                            Best_Choice[u]++;
                            break;
                        }
                    } else {
                        curr_max = v;
                        Best_Choice[u]++;
                        break;
                    }
                }
                edge x = curr_max;

                if (x.first == -1) {
                    break;
                } else {
                    std::unique_lock<std::mutex> v_lk(edgy_mutex[x.first]);

                    bool y_not_null = (S[x.first].size() == bvalue(method, g[x.first].second));

                    if (y_not_null) {
                        edge S_last = S[x.first].top();
                        if (f_smaller(std::make_pair(u, x.second), S_last, g)) {
                            continue;
                        }
                    }
                    auto y = y_not_null ? S[x.first].top() : std::make_pair(-1, -1);

                    if (y_not_null) {
                        S[x.first].pop();
                        if (S[x.first].empty()) {
                            top_and_size[x.first] = pair_for_at(-1, 0);
                        } else {
                            top_and_size[x.first] = pair_for_at(S[x.first].top().first, S[x.first].size());
                        }
                    }
                    S[x.first].emplace(u, x.second);
                    top_and_size[x.first] = pair_for_at(S[x.first].top().first, S[x.first].size());

                    T[u]++;
                    b_sum += x.second;
                    if (y_not_null) {
                        T[y.first]--;
                        b_sum -= y.second;
                        Rt.insert(y.first);
                    }
                }
            }
        }
        loczeq rlock(r_mutex);
        R.insert(Rt.begin(), Rt.end());
    };

    while (!Q.empty()) {
        int stand_size = Q.size() / (thread_count);
        int main_size = Q.size() - stand_size * (thread_count - 1);
        std::vector<std::thread> threads;
        for (int i = 0; i < thread_count - 1; ++i) {
            threads.emplace_back(looper, stand_size);
        }
        looper(main_size);
        for (auto &t : threads) {
            t.join();
        }
        std::swap(Q, R);
    }

    return b_sum / 2;
}

int main(int argc, char *argv[]) {
    if (argc != 4) {
        std::cerr << "usage: " << argv[0] << " thread-count inputfile b-limit" << std::endl;
        return 1;
    }
    int thread_count = std::stoi(argv[1]);
    int b_limit = std::stoi(argv[3]);
    std::string input_filename{argv[2]};
    graph g;
    weighing_neighs neighs_weights;
    graph_reader(g, neighs_weights, input_filename);
    auto start = std::chrono::steady_clock::now();
    for (int iter = 0; iter <= b_limit; iter++) {
        int suited = b_suitor(g, neighs_weights, iter, thread_count);
        std::cout << suited << "\n";
    }
    auto finish = std::chrono::steady_clock::now();
    std::cerr << std::chrono::duration_cast<std::chrono::microseconds>(finish - start).count() << "\n";
}