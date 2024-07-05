#ifndef __PROGTEST__
#include <algorithm>
#include <cassert>
#include <cctype>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <deque>
#include <functional>
#include <iomanip>
#include <iostream>
#include <list>
#include <map>
#include <memory>
#include <numeric>
#include <optional>
#include <queue>
#include <set>
#include <sstream>
#include <stack>
#include <vector>

using namespace std;
using Symbol = char;
using Word = std::vector<Symbol>;

struct Grammar {
    std::set<Symbol> m_Nonterminals;
    std::set<Symbol> m_Terminals;
    std::vector<std::pair<Symbol, std::vector<Symbol>>> m_Rules;
    Symbol m_InitialSymbol;
};
#endif

std::vector<size_t> trace(const Grammar&, const Word&);

std::vector<size_t> trace(const Grammar& grm, const Word& str){
    if (str.empty()){
        vector<size_t> res;
        for(size_t x=0; x<grm.m_Rules.size(); x++){
            if (grm.m_Rules.at(x).first==grm.m_InitialSymbol && grm.m_Rules.at(x).second.empty()){
                res.push_back(x);
                return res;
            }
        }
        return res;
    }
    size_t n=str.size();
    size_t r=grm.m_Nonterminals.size();

    vector<vector<vector<vector<size_t> > > > production = vector<vector<vector<vector<size_t> > > >( (n+1), vector<vector<vector<size_t>>>((n+1), vector<vector<size_t>>(r+1), {}));
    // vector<size_t> production[n+1][n+1][r+1];
    vector<vector<vector<bool> > > P = vector<vector<vector<bool> > >( (n+1), vector<vector<bool> >((n+1), vector<bool>((r+1), false)));
    // bool P[n+1][n+1][r+1];
    for(size_t x=0; x<n+1; x++){
        for(size_t y=0; y<n+1; y++){
            for(size_t z=0; z<r+1; z++){
                P[x][y][z] = false;
                production[x][y][z] = {};
            }
        }
    }
    vector<vector<vector<vector<size_t> > > > back = vector<vector<vector<vector<size_t> > > >( (n+1), vector<vector<vector<size_t>>>((n+1), vector<vector<size_t>>(r+1), {}));
    // vector<size_t> back[n+1][n+1][r+1];
    for(size_t x=0; x<n+1; x++){
        for(size_t y=0; y<n+1; y++){
            for(size_t z=0; z<r+1; z++){
                back[x][y][z] = {};
            }
        }
    }

    vector<Symbol> Nonterminals;
    Nonterminals.resize(r+1);
    size_t ind_non_term=1;
    for(auto x: grm.m_Nonterminals){
        Nonterminals.at(ind_non_term)=x;
        ind_non_term++;
    }
    
    if(Nonterminals.at(1)!=grm.m_InitialSymbol){
        Symbol tmp = Nonterminals.at(1);
        for (size_t i = 1; i < r+1; i++)
        {
            if (Nonterminals.at(i)==grm.m_InitialSymbol){
                Nonterminals.at(1)=grm.m_InitialSymbol;
                Nonterminals.at(i)=tmp;
            }
        }
        
    }

    for(size_t s=1; s<n+1; s++){
        size_t pro=0;
        for(auto x: grm.m_Rules){
            if ((x.second.size()==1) && x.second.at(0)==str.at(s-1)){
                for(size_t v=1; v<r+1; v++){
                    if (Nonterminals.at(v)==x.first){
                        P[1][s][v] = true;
                        production.at(1).at(s).at(v).push_back(pro);
                        // production[1][s][v].push_back(pro);
                        // cout <<"(" << 1 << " " << s << " " << v << "->" << str.at(s-1) << ")" << Nonterminals.at(v) << "->" << str.at(s-1) << endl;
                    }
                }
            }
            pro++;
        }
    }

    for(size_t l=2; l<n+1; l++){
        for(size_t s=1; s<(n+1-l+1); s++){
            for(size_t p=1; p<=(l-1); p++){
                size_t pro=0;
                for(auto x: grm.m_Rules){
                    if (x.second.size()==2){
                        size_t a = SIZE_MAX;
                        size_t b = SIZE_MAX;
                        size_t c = SIZE_MAX;
                        for(size_t y=1; y<r+1; y++){
                            if(Nonterminals.at(y)==x.first){
                                a=y;
                                break;
                            }
                        }
                        for(size_t y=1; y<r+1; y++){
                            if(Nonterminals.at(y)==x.second.at(0)){
                                b=y;
                                break;
                            }
                        }
                        for(size_t y=1; y<r+1; y++){
                            if(Nonterminals.at(y)==x.second.at(1)){
                                c=y;
                                break;
                            }
                        }
                        if((a!=SIZE_MAX) &&(b!=SIZE_MAX) && (c!=SIZE_MAX)){
                            if(P[p][s][b] && P[l-p][s+p][c]){
                                P[l][s][a]=true;
                                back[l][s][a].clear();
                                back[l][s][a].push_back(p);
                                back[l][s][a].push_back(s);
                                back[l][s][a].push_back(b);
                                back[l][s][a].push_back(l-p);
                                back[l][s][a].push_back(s+p);
                                back[l][s][a].push_back(c);
                                production[l][s][a].clear();
                                production[l][s][a].push_back(pro);
                                // cout <<"(" << l << " " << s << " " << a << "->" << p << " " << b << " " << c << ")" << Nonterminals.at(a) << "->" << Nonterminals.at(b) << Nonterminals.at(c) << endl;
                            }
                        }
                    }
                    pro++;
                }
            }
        }
    }

    vector<size_t> res;
    res.clear();
    tuple<size_t,size_t,size_t> root = {n,1,1};
    if ((str.size()==1) && (production[n][1][1].empty()==false)){
        res.push_back(production[n][1][1].at(0));
        return res;
    }
    if (back[get<0>(root)][get<1>(root)][get<2>(root)].empty()){
        return res;
    }
    stack<tuple<size_t,size_t,size_t>> ns;
    ns.push(root);
    while(ns.empty()==false){
        auto curr = ns.top();
        size_t rule_num = production[get<0>(curr)][get<1>(curr)][get<2>(curr)].at(0);
        res.push_back(rule_num);
        ns.pop();

        if (back[get<0>(curr)][get<1>(curr)][get<2>(curr)].size()>=6){
            ns.push({back[get<0>(curr)][get<1>(curr)][get<2>(curr)].at(3), back[get<0>(curr)][get<1>(curr)][get<2>(curr)].at(4), back[get<0>(curr)][get<1>(curr)][get<2>(curr)].at(5)});
        }
        if (back[get<0>(curr)][get<1>(curr)][get<2>(curr)].size()>=3){
            ns.push({back[get<0>(curr)][get<1>(curr)][get<2>(curr)].at(0), back[get<0>(curr)][get<1>(curr)][get<2>(curr)].at(1), back[get<0>(curr)][get<1>(curr)][get<2>(curr)].at(2)});
        }
    }
    return res;
}

#ifndef __PROGTEST__
int main()
{
    // Grammar g4{
    //     {'A', 'B', 'C'},
    //     {'0', '1'},
    //     {
    //         {'A', {'B', 'C'}},
    //         {'A', {'A', 'B'}},
    //         {'A', {'1'}},
    //         {'B', {'A', 'A'}},
    //         {'B', {'0'}},
    //         {'C', {'C', 'B'}},
    //         {'C', {'1'}},
    //         {'C', {'0'}},
    //     },
    //     'A'};
    // trace(g4, {'1', '1', '0', '1', '0', '0'});

    Grammar g0{
        {'A', 'B', 'C', 'S'},
        {'a', 'b'},
        {
            {'S', {'A', 'B'}},
            {'S', {'B', 'C'}},
            {'A', {'B', 'A'}},
            {'A', {'a'}},
            {'B', {'C', 'C'}},
            {'B', {'b'}},
            {'C', {'A', 'B'}},
            {'C', {'a'}},
        },
        'S'};

    assert(trace(g0, {'b', 'a', 'a', 'b', 'a'}) == std::vector<size_t>({0, 2, 5, 3, 4, 6, 3, 5, 7}));
    assert(trace(g0, {'b'}) == std::vector<size_t>({}));
    assert(trace(g0, {'a'}) == std::vector<size_t>({}));
    assert(trace(g0, {}) == std::vector<size_t>({}));
    assert(trace(g0, {'a', 'a', 'a', 'a', 'a'}) == std::vector<size_t>({1, 4, 6, 3, 4, 7, 7, 7, 7}));
    assert(trace(g0, {'a', 'b'}) == std::vector<size_t>({0, 3, 5}));
    assert(trace(g0, {'b', 'a'}) == std::vector<size_t>({1, 5, 7}));
    assert(trace(g0, {'c', 'a'}) == std::vector<size_t>({}));

    Grammar g1{
        {'A', 'B'},
        {'x', 'y'},
        {
            {'A', {}},
            {'A', {'x'}},
            {'B', {'x'}},
            {'A', {'B', 'B'}},
            {'B', {'B', 'B'}},
        },
        'A'};

    assert(trace(g1, {}) == std::vector<size_t>({0}));
    assert(trace(g1, {'x'}) == std::vector<size_t>({1}));
    assert(trace(g1, {'x', 'x'}) == std::vector<size_t>({3, 2, 2}));
    assert(trace(g1, {'x', 'x', 'x'}) == std::vector<size_t>({3, 4, 2, 2, 2}));
    assert(trace(g1, {'x', 'x', 'x', 'x'}) == std::vector<size_t>({3, 4, 4, 2, 2, 2, 2}));
    assert(trace(g1, {'x', 'x', 'x', 'x', 'x'}) == std::vector<size_t>({3, 4, 4, 4, 2, 2, 2, 2, 2}));
    assert(trace(g1, {'x', 'x', 'x', 'x', 'x', 'x'}) == std::vector<size_t>({3, 4, 4, 4, 4, 2, 2, 2, 2, 2, 2}));
    assert(trace(g1, {'x', 'x', 'x', 'x', 'x', 'x', 'x'}) == std::vector<size_t>({3, 4, 4, 4, 4, 4, 2, 2, 2, 2, 2, 2, 2}));
    assert(trace(g1, {'x', 'x', 'x', 'x', 'x', 'x', 'x', 'x'}) == std::vector<size_t>({3, 4, 4, 4, 4, 4, 4, 2, 2, 2, 2, 2, 2, 2, 2}));
    assert(trace(g1, {'x', 'x', 'x', 'x', 'x', 'x', 'x', 'x', 'x'}) == std::vector<size_t>({3, 4, 4, 4, 4, 4, 4, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2}));

    Grammar g2{
        {'A', 'B'},
        {'x', 'y'},
        {
            {'A', {'x'}},
            {'B', {'x'}},
            {'A', {'B', 'B'}},
            {'B', {'B', 'B'}},
        },
        'B'};

    assert(trace(g2, {}) == std::vector<size_t>({}));
    assert(trace(g2, {'x'}) == std::vector<size_t>({1}));
    assert(trace(g2, {'x', 'x'}) == std::vector<size_t>({3, 1, 1}));
    assert(trace(g2, {'x', 'x', 'x'}) == std::vector<size_t>({3, 3, 1, 1, 1}));

    Grammar g3{
        {'A', 'B', 'C', 'D', 'E', 'S'},
        {'a', 'b'},
        {
            {'S', {'A', 'B'}},
            {'S', {'S', 'S'}},
            {'S', {'a'}},
            {'A', {'B', 'S'}},
            {'A', {'C', 'D'}},
            {'A', {'b'}},
            {'B', {'D', 'D'}},
            {'B', {'b'}},
            {'C', {'D', 'E'}},
            {'C', {'b'}},
            {'C', {'a'}},
            {'D', {'a'}},
            {'E', {'S', 'S'}},
        },
        'S'};

    assert(trace(g3, {}) == std::vector<size_t>({}));
    assert(trace(g3, {'b'}) == std::vector<size_t>({}));
    assert(trace(g3, {'a', 'b', 'a', 'a', 'b'}) == std::vector<size_t>({1, 2, 0, 3, 7, 1, 2, 2, 7}));
    assert(trace(g3, {'a', 'b', 'a', 'a', 'b', 'a', 'b', 'a', 'b', 'a', 'a'}) == std::vector<size_t>({1, 1, 0, 4, 8, 11, 12, 0, 5, 6, 11, 11, 0, 4, 9, 11, 7, 11, 7, 2, 2}));
}
#endif

