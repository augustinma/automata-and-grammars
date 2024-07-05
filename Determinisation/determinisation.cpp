#ifndef __PROGTEST__
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <sstream>

#include <algorithm>
#include <deque>
#include <list>
#include <map>
#include <queue>
#include <set>
#include <stack>
#include <vector>

#include <cassert>
using namespace std;

using State = unsigned int;
using Symbol = char;

struct MISNFA {
    std::set<State> m_States;
    std::set<Symbol> m_Alphabet;
    std::map<std::pair<State, Symbol>, std::set<State>> m_Transitions;
    std::set<State> m_InitialStates;
    std::set<State> m_FinalStates;
};

struct DFA {
    std::set<State> m_States;
    std::set<Symbol> m_Alphabet;
    std::map<std::pair<State, Symbol>, State> m_Transitions;
    State m_InitialState;
    std::set<State> m_FinalStates;

    bool operator==(const DFA& dfa)
    {
        return std::tie(m_States, m_Alphabet, m_Transitions, m_InitialState, m_FinalStates) == std::tie(dfa.m_States, dfa.m_Alphabet, dfa.m_Transitions, dfa.m_InitialState, dfa.m_FinalStates);
    }
};

#endif

DFA determinize(const MISNFA& nfa);
struct InvertDFA {
    std::set<State> m_States;
    std::set<Symbol> m_Alphabet;
    std::map<std::pair<State, Symbol>, std::set<State>> m_Transitions;
    State m_FinalState;
    std::set<State> m_InitialStates;
};

void dfs (State v, const InvertDFA &dfa, set<State> &visited){
    stack<State> s;
    s.push(v);
    while (s.empty()==false){
        v=s.top();
        s.pop();
        if (visited.find(v)==visited.end()){
            visited.insert(v);
            for(auto x : dfa.m_Alphabet){
                if (dfa.m_Transitions.find(make_pair(v, x))!=dfa.m_Transitions.end()){
                    for (auto y : dfa.m_Transitions.at(make_pair(v, x))){
                        s.push(y);
                    }
                }
            }
        }
    }
}

void dfs (State v, const DFA &dfa, set<State> &visited){
    stack<State> s;
    s.push(v);
    while (s.empty()==false){
        v=s.top();
        s.pop();
        if (visited.find(v)==visited.end()){
            visited.insert(v);
            for(auto x : dfa.m_Alphabet){
                if (dfa.m_Transitions.find(make_pair(v, x))!=dfa.m_Transitions.end()){
                    s.push(dfa.m_Transitions.at(make_pair(v, x)));
                }
            }
        }
    }
}

void reachable(const DFA &dfa, set<State> &visited){

    dfs(dfa.m_InitialState, dfa, visited);
}

void removeUnreachable(const set<State> &visited, const InvertDFA &dfa, InvertDFA &dfaReachable){
    for (auto x : visited){
        for (auto y : dfa.m_Alphabet){
            if (dfa.m_Transitions.find(make_pair(x, y))!=dfa.m_Transitions.end()){
                dfaReachable.m_Transitions.insert({make_pair(x,y), dfa.m_Transitions.at(make_pair(x, y))});
                set<State> dsts;
            }
        }
    }
    
    dfaReachable.m_States = visited;
    dfaReachable.m_Alphabet = dfa.m_Alphabet;
    dfaReachable.m_FinalState = dfa.m_FinalState;
    for(auto x : dfa.m_InitialStates){
        if (visited.find(x)!=visited.end()){
            dfaReachable.m_InitialStates.insert(x);
        }
    }
}

void removeUnreachable(const set<State> &visited, const DFA &dfa, DFA &dfaReachable){
    
    for (auto x : visited){
        for (auto y : dfa.m_Alphabet){
            if (dfa.m_Transitions.find(make_pair(x, y))!=dfa.m_Transitions.end()){
                dfaReachable.m_Transitions.insert({make_pair(x,y), dfa.m_Transitions.at(make_pair(x, y))});
                set<State> dsts;
            }
        }
    }
    
    dfaReachable.m_States = visited;
    dfaReachable.m_Alphabet = dfa.m_Alphabet;
    dfaReachable.m_InitialState = dfa.m_InitialState;
    for(auto x : dfa.m_FinalStates){
        if (visited.find(x)!=visited.end()){
            dfaReachable.m_FinalStates.insert(x);
        }
    }
    
}

void invert(const InvertDFA &invertedDfa, DFA &dfa){
    dfa.m_States=invertedDfa.m_States;
    dfa.m_Alphabet=invertedDfa.m_Alphabet;
    dfa.m_InitialState=invertedDfa.m_FinalState;
    dfa.m_FinalStates=invertedDfa.m_InitialStates;
    map<std::pair<State, Symbol>, State> transitions;

    for(auto x : invertedDfa.m_States){
        for (auto y : invertedDfa.m_Alphabet){
            if (invertedDfa.m_Transitions.find(make_pair(x, y))!=invertedDfa.m_Transitions.end()){
                for(auto z : invertedDfa.m_Transitions.at(make_pair(x, y))){
                    // if (transitions.find(make_pair(z, y))==transitions.end()){
                        transitions.insert({make_pair(z, y), x});
                    // }else{
                    //     transitions.at(make_pair(z, y)).insert(x);
                    // }
                }
            }
        }
    }
    dfa.m_Transitions=transitions;

}

void invert(const DFA &dfa, InvertDFA &invertedDfa){
    invertedDfa.m_States=dfa.m_States;
    invertedDfa.m_Alphabet=dfa.m_Alphabet;
    invertedDfa.m_InitialStates=dfa.m_FinalStates;
    invertedDfa.m_FinalState=dfa.m_InitialState;
    map<std::pair<State, Symbol>, set<State>> transitions;

    for(auto x : dfa.m_States){
        for (auto y : dfa.m_Alphabet){
            if (dfa.m_Transitions.find(make_pair(x, y))!=dfa.m_Transitions.end()){
                auto z = dfa.m_Transitions.at(make_pair(x, y));
                if (transitions.find(make_pair(z, y))==transitions.end()){
                    transitions.insert({make_pair(z, y), {x}});
                }else{
                    transitions.at(make_pair(z, y)).insert(x);
                }
                
            }
        }
    }
    invertedDfa.m_Transitions=transitions;
}

struct InterDFA {
    std::set<std::set<State>> m_States;
    std::set<Symbol> m_Alphabet;
    std::map<std::pair<std::set<State>, Symbol>, std::set<State>> m_Transitions;
    std::set<State> m_InitialState;
    std::set<std::set<State>> m_FinalStates;
};

void bfs(InterDFA &tmp_dfa, const MISNFA &nfa){
    queue<set<State>> q;
    tmp_dfa.m_States.insert(tmp_dfa.m_InitialState);
    q.push(tmp_dfa.m_InitialState);
    while (q.empty()==false){
        set<State> v = q.front();
        q.pop();
        for(auto y : nfa.m_Alphabet){
            set<State> w;
            for (auto x : v){
                if(nfa.m_Transitions.find(make_pair(x, y))!=nfa.m_Transitions.end()){
                    for(auto z : nfa.m_Transitions.at(make_pair(x, y))){
                        w.insert(z);
                    }
                }
            }
            if (w.empty()==false){
                tmp_dfa.m_Transitions.insert({make_pair(v, y), w});
                if (tmp_dfa.m_States.find(w)==tmp_dfa.m_States.end()){
                    tmp_dfa.m_States.insert(w);
                    q.push(w);
                }
            }
            
        }
    }
    
}

void transform(const MISNFA &nfa, DFA &result){
    InterDFA tmp_dfa;
    tmp_dfa.m_InitialState=nfa.m_InitialStates;
    tmp_dfa.m_Alphabet=nfa.m_Alphabet;
    bfs(tmp_dfa, nfa);
    for(auto x : tmp_dfa.m_States){
        for (auto y : x){
            if(nfa.m_FinalStates.find(y)!=nfa.m_FinalStates.end()){
                tmp_dfa.m_FinalStates.insert(x);
                break;
            }
        }
    }

    map<set<State>, State> newStates;
    State label=0;
    for(auto x : tmp_dfa.m_States){
        if(newStates.find(x)==newStates.end()){
            newStates.insert({x, label});
            label++;
        }
    }

    result.m_Alphabet=nfa.m_Alphabet;
    result.m_InitialState=newStates.at(tmp_dfa.m_InitialState);
    for(auto x : tmp_dfa.m_FinalStates){
        result.m_FinalStates.insert(newStates.at(x));
    }
    for(auto x : tmp_dfa.m_States){
        for(auto y : tmp_dfa.m_Alphabet){
            if(tmp_dfa.m_Transitions.find(make_pair(x, y))!=tmp_dfa.m_Transitions.end()){
                result.m_Transitions.insert({make_pair(newStates.at(x), y), newStates.at(tmp_dfa.m_Transitions.at(make_pair(x, y)))});
            }
        }
    }
    for (auto x : tmp_dfa.m_States){
        result.m_States.insert(newStates.at(x));
    }
}



DFA determinize(const MISNFA &nfa){
    // set<State> visited0;
    // reachable(nfa, visited0);
    // MISNFA nfaReachable;
    // removeUnreachable(visited0, nfa, nfaReachable);
    // set<State> visited1;
    // MISNFA invertedNfaReachable;
    // invert(nfaReachable, invertedNfaReachable);
    // reachable(invertedNfaReachable, visited1);
    // MISNFA invertednfaReachableandUseful;
    // removeUnreachable(visited1, invertedNfaReachable, invertednfaReachableandUseful);
    // MISNFA nfaReachableandUseful;
    // invert(invertednfaReachableandUseful, nfaReachableandUseful);
    DFA result;
    transform(nfa, result);

    set<State> visited0;
    reachable(result, visited0);

    DFA dfaReachable;
    removeUnreachable(visited0, result, dfaReachable);

    
    set<State> visited1;
    InvertDFA invertedDfaReachable;
    invert(dfaReachable, invertedDfaReachable);
    for(auto x : invertedDfaReachable.m_InitialStates){
        set<State> visited2;
        dfs(x, invertedDfaReachable, visited2);
        visited1.insert(visited2.begin(), visited2.end());
    }

    InvertDFA invertedDfaReachableandUseful;
    removeUnreachable(visited1, invertedDfaReachable, invertedDfaReachableandUseful);

    DFA dfaReachableandUseful;
    invert(invertedDfaReachableandUseful, dfaReachableandUseful);
    // cout << "I: " << result.m_InitialState << " F: ";
    // for (auto x : result.m_FinalStates){
    //     cout << x << " ";
    // } 
    // cout << endl;
    // cout << " : ";
    // for(auto x : result.m_Alphabet){
    //     cout << x << " ";
    // }
    // cout << endl;
    // for(auto x : result.m_States){
    //     cout << x <<": ";
    //     for (auto y : result.m_Alphabet){
    //         if (result.m_Transitions.find(make_pair(x, y))!=result.m_Transitions.end()){
    //             cout << result.m_Transitions.at(make_pair(x, y)) << " ";
    //         }else{
    //             cout << "  ";
    //         }
    //     }
    //     cout << endl;
    // }
    if (dfaReachableandUseful.m_FinalStates.empty()){
        dfaReachableandUseful.m_States.clear();
        dfaReachableandUseful.m_States.insert(0);
        dfaReachableandUseful.m_InitialState=0;
    }
    return dfaReachableandUseful;
}

#ifndef __PROGTEST__
MISNFA in0 = {
    {0, 1, 2},
    {'e', 'l'},
    {
        {{0, 'e'}, {1}},
        {{0, 'l'}, {1}},
        {{1, 'e'}, {2}},
        {{2, 'e'}, {0}},
        {{2, 'l'}, {2}},
    },
    {0},
    {1, 2},
};
DFA out0 = {
    {0, 1, 2},
    {'e', 'l'},
    {
        {{0, 'e'}, 1},
        {{0, 'l'}, 1},
        {{1, 'e'}, 2},
        {{2, 'e'}, 0},
        {{2, 'l'}, 2},
    },
    0,
    {1, 2},
};
MISNFA in1 = {
    {0, 1, 2, 3},
    {'g', 'l'},
    {
        {{0, 'g'}, {1}},
        {{0, 'l'}, {2}},
        {{1, 'g'}, {3}},
        {{1, 'l'}, {3}},
        {{2, 'g'}, {1}},
        {{2, 'l'}, {0}},
        {{3, 'l'}, {1}},
    },
    {0},
    {0, 2, 3},
};
DFA out1 = {
    {0, 1, 2, 3},
    {'g', 'l'},
    {
        {{0, 'g'}, 1},
        {{0, 'l'}, 2},
        {{1, 'g'}, 3},
        {{1, 'l'}, 3},
        {{2, 'g'}, 1},
        {{2, 'l'}, 0},
        {{3, 'l'}, 1},
    },
    0,
    {0, 2, 3},
};
MISNFA in2 = {
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12},
    {'l', 'm'},
    {
        {{0, 'l'}, {1}},
        {{0, 'm'}, {2}},
        {{1, 'l'}, {3}},
        {{2, 'l'}, {4}},
        {{2, 'm'}, {5}},
        {{3, 'l'}, {3}},
        {{4, 'l'}, {3}},
        {{4, 'm'}, {6}},
        {{5, 'l'}, {7}},
        {{5, 'm'}, {6}},
        {{6, 'l'}, {7}},
        {{6, 'm'}, {8}},
        {{7, 'l'}, {9}},
        {{7, 'm'}, {10}},
        {{8, 'l'}, {6}},
        {{8, 'm'}, {10}},
        {{9, 'l'}, {7}},
        {{9, 'm'}, {8}},
        {{10, 'l'}, {11}},
        {{10, 'm'}, {4}},
        {{11, 'l'}, {12}},
        {{11, 'm'}, {9}},
        {{12, 'l'}, {6}},
        {{12, 'm'}, {10}},
    },
    {0},
    {1, 3},
};
DFA out2 = {
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12},
    {'l', 'm'},
    {
        {{0, 'l'}, 1},
        {{0, 'm'}, 2},
        {{1, 'l'}, 3},
        {{2, 'l'}, 4},
        {{2, 'm'}, 5},
        {{3, 'l'}, 3},
        {{4, 'l'}, 3},
        {{4, 'm'}, 6},
        {{5, 'l'}, 7},
        {{5, 'm'}, 6},
        {{6, 'l'}, 7},
        {{6, 'm'}, 8},
        {{7, 'l'}, 9},
        {{7, 'm'}, 10},
        {{8, 'l'}, 6},
        {{8, 'm'}, 10},
        {{9, 'l'}, 7},
        {{9, 'm'}, 8},
        {{10, 'l'}, 11},
        {{10, 'm'}, 4},
        {{11, 'l'}, 12},
        {{11, 'm'}, 9},
        {{12, 'l'}, 6},
        {{12, 'm'}, 10},
    },
    0,
    {1, 3},
};
MISNFA in3 = {
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11},
    {'a', 'b'},
    {
        {{0, 'a'}, {1}},
        {{0, 'b'}, {2}},
        {{1, 'a'}, {3}},
        {{1, 'b'}, {4}},
        {{2, 'a'}, {5}},
        {{2, 'b'}, {6}},
        {{3, 'a'}, {7}},
        {{3, 'b'}, {8}},
        {{4, 'a'}, {9}},
        {{5, 'a'}, {5}},
        {{5, 'b'}, {10}},
        {{6, 'a'}, {8}},
        {{6, 'b'}, {8}},
        {{7, 'a'}, {11}},
        {{8, 'a'}, {3}},
        {{8, 'b'}, {9}},
        {{9, 'a'}, {5}},
        {{9, 'b'}, {5}},
        {{10, 'a'}, {1}},
        {{10, 'b'}, {2}},
        {{11, 'a'}, {5}},
        {{11, 'b'}, {5}},
    },
    {0},
    {5, 6},
};
DFA out3 = {
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11},
    {'a', 'b'},
    {
        {{0, 'a'}, 1},
        {{0, 'b'}, 2},
        {{1, 'a'}, 3},
        {{1, 'b'}, 4},
        {{2, 'a'}, 5},
        {{2, 'b'}, 6},
        {{3, 'a'}, 7},
        {{3, 'b'}, 8},
        {{4, 'a'}, 9},
        {{5, 'a'}, 5},
        {{5, 'b'}, 10},
        {{6, 'a'}, 8},
        {{6, 'b'}, 8},
        {{7, 'a'}, 11},
        {{8, 'a'}, 3},
        {{8, 'b'}, 9},
        {{9, 'a'}, 5},
        {{9, 'b'}, 5},
        {{10, 'a'}, 1},
        {{10, 'b'}, 2},
        {{11, 'a'}, 5},
        {{11, 'b'}, 5},
    },
    0,
    {5, 6},
};
MISNFA in4 = {
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9},
    {'e', 'j', 'k'},
    {
        {{0, 'e'}, {1}},
        {{0, 'j'}, {2}},
        {{0, 'k'}, {3}},
        {{1, 'e'}, {2}},
        {{1, 'j'}, {4}},
        {{1, 'k'}, {5}},
        {{2, 'e'}, {6}},
        {{2, 'j'}, {0}},
        {{2, 'k'}, {4}},
        {{3, 'e'}, {7}},
        {{3, 'j'}, {2}},
        {{3, 'k'}, {1}},
        {{4, 'e'}, {4}},
        {{4, 'j'}, {8}},
        {{4, 'k'}, {7}},
        {{5, 'e'}, {4}},
        {{5, 'j'}, {0}},
        {{5, 'k'}, {4}},
        {{6, 'e'}, {7}},
        {{6, 'j'}, {8}},
        {{6, 'k'}, {4}},
        {{7, 'e'}, {3}},
        {{7, 'j'}, {1}},
        {{7, 'k'}, {8}},
        {{8, 'e'}, {2}},
        {{8, 'j'}, {4}},
        {{8, 'k'}, {9}},
        {{9, 'e'}, {4}},
        {{9, 'j'}, {0}},
        {{9, 'k'}, {4}},
    },
    {0},
    {1, 6, 8},
};
DFA out4 = {
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9},
    {'e', 'j', 'k'},
    {
        {{0, 'e'}, 1},
        {{0, 'j'}, 2},
        {{0, 'k'}, 3},
        {{1, 'e'}, 2},
        {{1, 'j'}, 4},
        {{1, 'k'}, 5},
        {{2, 'e'}, 6},
        {{2, 'j'}, 0},
        {{2, 'k'}, 4},
        {{3, 'e'}, 7},
        {{3, 'j'}, 2},
        {{3, 'k'}, 1},
        {{4, 'e'}, 4},
        {{4, 'j'}, 8},
        {{4, 'k'}, 7},
        {{5, 'e'}, 4},
        {{5, 'j'}, 0},
        {{5, 'k'}, 4},
        {{6, 'e'}, 7},
        {{6, 'j'}, 8},
        {{6, 'k'}, 4},
        {{7, 'e'}, 3},
        {{7, 'j'}, 1},
        {{7, 'k'}, 8},
        {{8, 'e'}, 2},
        {{8, 'j'}, 4},
        {{8, 'k'}, 9},
        {{9, 'e'}, 4},
        {{9, 'j'}, 0},
        {{9, 'k'}, 4},
    },
    0,
    {1, 6, 8},
};
MISNFA in5 = {
    {0, 1, 2, 3},
    {'e', 'n', 'r'},
    {
        {{0, 'e'}, {1}},
        {{0, 'n'}, {1}},
        {{0, 'r'}, {2}},
        {{1, 'e'}, {2}},
        {{1, 'n'}, {3}},
        {{1, 'r'}, {3}},
        {{2, 'e'}, {3}},
        {{2, 'n'}, {3}},
        {{2, 'r'}, {1}},
        {{3, 'e'}, {1}},
        {{3, 'n'}, {1}},
        {{3, 'r'}, {2}},
    },
    {0},
    {0, 3},
};
DFA out5 = {
    {0, 1, 2, 3},
    {'e', 'n', 'r'},
    {
        {{0, 'e'}, 1},
        {{0, 'n'}, 1},
        {{0, 'r'}, 2},
        {{1, 'e'}, 2},
        {{1, 'n'}, 3},
        {{1, 'r'}, 3},
        {{2, 'e'}, 3},
        {{2, 'n'}, 3},
        {{2, 'r'}, 1},
        {{3, 'e'}, 1},
        {{3, 'n'}, 1},
        {{3, 'r'}, 2},
    },
    0,
    {0, 3},
};
MISNFA in6 = {
    {0, 1, 2, 3, 4, 5, 6, 7},
    {'e', 't', 'x'},
    {
        {{0, 'e'}, {1}},
        {{0, 't'}, {2}},
        {{0, 'x'}, {3}},
        {{1, 'e'}, {1}},
        {{1, 't'}, {4}},
        {{1, 'x'}, {5}},
        {{2, 'e'}, {3}},
        {{2, 't'}, {6}},
        {{2, 'x'}, {2}},
        {{3, 'e'}, {3}},
        {{3, 't'}, {7}},
        {{3, 'x'}, {4}},
        {{4, 'e'}, {4}},
        {{4, 't'}, {4}},
        {{4, 'x'}, {7}},
        {{5, 'e'}, {5}},
        {{5, 't'}, {5}},
        {{5, 'x'}, {5}},
        {{6, 'e'}, {5}},
        {{6, 't'}, {2}},
        {{6, 'x'}, {0}},
        {{7, 'e'}, {5}},
        {{7, 't'}, {5}},
        {{7, 'x'}, {5}},
    },
    {0},
    {0, 3},
};
DFA out6 = {
    {0, 1, 2, 3},
    {'e', 't', 'x'},
    {
        {{0, 't'}, 1},
        {{0, 'x'}, 2},
        {{1, 'e'}, 2},
        {{1, 't'}, 3},
        {{1, 'x'}, 1},
        {{2, 'e'}, 2},
        {{3, 't'}, 1},
        {{3, 'x'}, 0},
    },
    0,
    {0, 2},
};
MISNFA in7 = {
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10},
    {'d', 'm', 't'},
    {
        {{0, 'd'}, {2}},
        {{0, 'm'}, {0}},
        {{0, 't'}, {3}},
        {{1, 'd'}, {9}},
        {{1, 'm'}, {0}},
        {{1, 't'}, {2}},
        {{2, 'd'}, {3}},
        {{2, 'm'}, {7}},
        {{4, 'd'}, {7}},
        {{4, 'm'}, {1}},
        {{5, 'd'}, {5}},
        {{5, 'm'}, {5}},
        {{5, 't'}, {0}},
        {{6, 'd'}, {7}},
        {{8, 'm'}, {7}},
        {{8, 't'}, {7}},
        {{9, 'd'}, {7}},
        {{9, 'm'}, {1}},
        {{10, 'd'}, {7}},
    },
    {1},
    {0, 5, 6, 10},
};
DFA out7 = {
    {0, 1, 2},
    {'d', 'm', 't'},
    {
        {{0, 'd'}, 1},
        {{0, 'm'}, 2},
        {{1, 'm'}, 0},
        {{2, 'm'}, 2},
    },
    0,
    {2},
};
MISNFA in8 = {
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10},
    {'h', 'm', 'q'},
    {
        {{1, 'h'}, {4}},
        {{1, 'm'}, {3}},
        {{1, 'q'}, {2}},
        {{2, 'h'}, {0}},
        {{2, 'm'}, {0}},
        {{2, 'q'}, {0}},
        {{3, 'q'}, {4}},
        {{4, 'h'}, {7}},
        {{4, 'm'}, {0}},
        {{4, 'q'}, {8}},
        {{5, 'q'}, {9}},
        {{6, 'h'}, {5}},
        {{6, 'm'}, {8}},
        {{6, 'q'}, {6}},
        {{7, 'h'}, {7}},
        {{7, 'q'}, {8}},
        {{9, 'q'}, {4}},
        {{10, 'h'}, {0}},
        {{10, 'm'}, {0}},
        {{10, 'q'}, {0}},
    },
    {1},
    {0, 5, 6},
};
DFA out8 = {
    {0, 1, 2, 3, 4},
    {'h', 'm', 'q'},
    {
        {{0, 'h'}, 1},
        {{0, 'm'}, 2},
        {{0, 'q'}, 3},
        {{1, 'm'}, 4},
        {{2, 'q'}, 1},
        {{3, 'h'}, 4},
        {{3, 'm'}, 4},
        {{3, 'q'}, 4},
    },
    0,
    {4},
};
MISNFA in9 = {
    {0, 1, 2, 3, 4},
    {'h', 'l', 'w'},
    {
        {{0, 'l'}, {1, 2, 3}},
        {{0, 'w'}, {4}},
        {{1, 'h'}, {1}},
        {{1, 'l'}, {3, 4}},
        {{1, 'w'}, {0, 2}},
        {{2, 'h'}, {3}},
        {{2, 'l'}, {1}},
        {{2, 'w'}, {0}},
        {{3, 'h'}, {3}},
        {{3, 'l'}, {0, 3}},
        {{3, 'w'}, {0, 2}},
        {{4, 'l'}, {1, 2, 3}},
        {{4, 'w'}, {4}},
    },
    {1},
    {0, 1, 2, 3, 4},
};
DFA out9 = {
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13},
    {'h', 'l', 'w'},
    {
        {{0, 'h'}, 0},
        {{0, 'l'}, 1},
        {{0, 'w'}, 2},
        {{1, 'h'}, 3},
        {{1, 'l'}, 4},
        {{1, 'w'}, 5},
        {{2, 'h'}, 3},
        {{2, 'l'}, 6},
        {{2, 'w'}, 7},
        {{3, 'h'}, 3},
        {{3, 'l'}, 8},
        {{3, 'w'}, 2},
        {{4, 'h'}, 9},
        {{4, 'l'}, 10},
        {{4, 'w'}, 5},
        {{5, 'h'}, 3},
        {{5, 'l'}, 6},
        {{5, 'w'}, 7},
        {{6, 'h'}, 9},
        {{6, 'l'}, 11},
        {{6, 'w'}, 2},
        {{7, 'l'}, 6},
        {{7, 'w'}, 12},
        {{8, 'h'}, 3},
        {{8, 'l'}, 4},
        {{8, 'w'}, 5},
        {{9, 'h'}, 9},
        {{9, 'l'}, 13},
        {{9, 'w'}, 2},
        {{10, 'h'}, 9},
        {{10, 'l'}, 10},
        {{10, 'w'}, 5},
        {{11, 'h'}, 9},
        {{11, 'l'}, 10},
        {{11, 'w'}, 5},
        {{12, 'l'}, 6},
        {{12, 'w'}, 12},
        {{13, 'h'}, 3},
        {{13, 'l'}, 4},
        {{13, 'w'}, 5},
    },
    0,
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13},
};
MISNFA in10 = {
    {0, 1, 2, 3, 4, 5, 6},
    {'j', 'k', 'w'},
    {
        {{0, 'j'}, {0, 5}},
        {{0, 'k'}, {1, 2}},
        {{0, 'w'}, {2}},
        {{1, 'j'}, {0, 1, 2}},
        {{1, 'k'}, {4, 5}},
        {{1, 'w'}, {2}},
        {{2, 'j'}, {0, 1, 2}},
        {{2, 'w'}, {0}},
        {{3, 'j'}, {0, 2}},
        {{3, 'k'}, {4, 6}},
        {{3, 'w'}, {0}},
        {{4, 'j'}, {5}},
        {{5, 'j'}, {5}},
        {{6, 'j'}, {0, 2}},
        {{6, 'k'}, {3, 4}},
        {{6, 'w'}, {0}},
    },
    {2},
    {0, 1, 3, 6},
};
DFA out10 = {
    {0, 1, 2, 3, 4, 5, 6, 7},
    {'j', 'k', 'w'},
    {
        {{0, 'j'}, 1},
        {{0, 'w'}, 2},
        {{1, 'j'}, 3},
        {{1, 'k'}, 4},
        {{1, 'w'}, 5},
        {{2, 'j'}, 6},
        {{2, 'k'}, 7},
        {{2, 'w'}, 0},
        {{3, 'j'}, 3},
        {{3, 'k'}, 4},
        {{3, 'w'}, 5},
        {{4, 'j'}, 3},
        {{4, 'w'}, 5},
        {{5, 'j'}, 3},
        {{5, 'k'}, 7},
        {{5, 'w'}, 5},
        {{6, 'j'}, 6},
        {{6, 'k'}, 7},
        {{6, 'w'}, 0},
        {{7, 'j'}, 1},
        {{7, 'w'}, 5},
    },
    0,
    {1, 2, 3, 4, 5, 6, 7},
};
MISNFA in11 = {
    {0, 1, 2, 3, 4, 5, 6},
    {'b', 'i', 'r'},
    {
        {{0, 'b'}, {2}},
        {{0, 'i'}, {1, 2, 4}},
        {{0, 'r'}, {0}},
        {{1, 'b'}, {1, 2, 5}},
        {{1, 'i'}, {0}},
        {{1, 'r'}, {1, 6}},
        {{2, 'b'}, {2, 4}},
        {{2, 'r'}, {1, 2}},
        {{3, 'b'}, {2}},
        {{3, 'i'}, {2}},
        {{3, 'r'}, {1, 3, 4}},
        {{4, 'r'}, {6}},
        {{5, 'b'}, {2}},
        {{5, 'i'}, {1, 2, 4}},
        {{5, 'r'}, {0}},
        {{6, 'r'}, {6}},
    },
    {1},
    {0, 1, 2, 5},
};
DFA out11 = {
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11},
    {'b', 'i', 'r'},
    {
        {{0, 'b'}, 1},
        {{0, 'i'}, 2},
        {{0, 'r'}, 3},
        {{1, 'b'}, 4},
        {{1, 'i'}, 5},
        {{1, 'r'}, 6},
        {{2, 'b'}, 7},
        {{2, 'i'}, 8},
        {{2, 'r'}, 2},
        {{3, 'b'}, 1},
        {{3, 'i'}, 2},
        {{3, 'r'}, 3},
        {{4, 'b'}, 4},
        {{4, 'i'}, 5},
        {{4, 'r'}, 6},
        {{5, 'b'}, 4},
        {{5, 'i'}, 5},
        {{5, 'r'}, 6},
        {{6, 'b'}, 4},
        {{6, 'i'}, 5},
        {{6, 'r'}, 6},
        {{7, 'b'}, 9},
        {{7, 'r'}, 10},
        {{8, 'b'}, 4},
        {{8, 'i'}, 2},
        {{8, 'r'}, 11},
        {{9, 'b'}, 9},
        {{9, 'r'}, 11},
        {{10, 'b'}, 4},
        {{10, 'i'}, 2},
        {{10, 'r'}, 11},
        {{11, 'b'}, 4},
        {{11, 'i'}, 2},
        {{11, 'r'}, 11},
    },
    0,
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11},
};
MISNFA in12 = {
    {0, 1, 2, 3, 4, 5, 6},
    {'l', 'q', 't'},
    {
        {{0, 'l'}, {2, 4, 5}},
        {{0, 'q'}, {2}},
        {{0, 't'}, {1}},
        {{1, 'l'}, {0, 2}},
        {{1, 'q'}, {1, 4}},
        {{1, 't'}, {0, 2}},
        {{2, 'l'}, {5}},
        {{2, 'q'}, {0, 4}},
        {{2, 't'}, {0}},
        {{3, 'l'}, {3, 4}},
        {{3, 'q'}, {0}},
        {{3, 't'}, {0, 2}},
        {{4, 't'}, {4}},
        {{5, 'l'}, {0, 2}},
        {{5, 'q'}, {4, 5}},
        {{5, 't'}, {0, 2}},
        {{6, 'l'}, {4, 6}},
        {{6, 'q'}, {0}},
        {{6, 't'}, {0, 2}},
    },
    {2, 4},
    {0, 1, 3, 5, 6},
};
DFA out12 = {
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18},
    {'l', 'q', 't'},
    {
        {{0, 'l'}, 1},
        {{0, 'q'}, 2},
        {{0, 't'}, 2},
        {{1, 'l'}, 3},
        {{1, 'q'}, 4},
        {{1, 't'}, 3},
        {{2, 'l'}, 5},
        {{2, 'q'}, 6},
        {{2, 't'}, 7},
        {{3, 'l'}, 5},
        {{3, 'q'}, 8},
        {{3, 't'}, 9},
        {{4, 'l'}, 3},
        {{4, 'q'}, 4},
        {{4, 't'}, 8},
        {{5, 'l'}, 10},
        {{5, 'q'}, 11},
        {{5, 't'}, 8},
        {{6, 'l'}, 1},
        {{6, 'q'}, 2},
        {{6, 't'}, 12},
        {{7, 'l'}, 3},
        {{7, 'q'}, 7},
        {{7, 't'}, 8},
        {{8, 'l'}, 5},
        {{8, 'q'}, 8},
        {{8, 't'}, 13},
        {{9, 'l'}, 14},
        {{9, 'q'}, 15},
        {{9, 't'}, 16},
        {{10, 'l'}, 14},
        {{10, 'q'}, 14},
        {{10, 't'}, 16},
        {{11, 'l'}, 14},
        {{11, 'q'}, 5},
        {{11, 't'}, 17},
        {{12, 'l'}, 5},
        {{12, 'q'}, 6},
        {{12, 't'}, 18},
        {{13, 'l'}, 14},
        {{13, 'q'}, 15},
        {{13, 't'}, 17},
        {{14, 'l'}, 14},
        {{14, 'q'}, 14},
        {{14, 't'}, 17},
        {{15, 'l'}, 10},
        {{15, 'q'}, 13},
        {{15, 't'}, 8},
        {{16, 'l'}, 14},
        {{16, 'q'}, 17},
        {{16, 't'}, 16},
        {{17, 'l'}, 14},
        {{17, 'q'}, 17},
        {{17, 't'}, 17},
        {{18, 'l'}, 3},
        {{18, 'q'}, 7},
        {{18, 't'}, 3},
    },
    0,
    {1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18},
};
MISNFA in13 = {
    {0, 1, 2, 3, 4, 5, 6},
    {'o', 'r'},
    {
        {{0, 'o'}, {0, 1, 4}},
        {{0, 'r'}, {5}},
        {{1, 'o'}, {4}},
        {{1, 'r'}, {2}},
        {{2, 'o'}, {0, 1}},
        {{2, 'r'}, {0, 5}},
        {{3, 'r'}, {2, 5}},
        {{5, 'o'}, {0, 1}},
        {{5, 'r'}, {0, 5}},
        {{6, 'r'}, {2}},
    },
    {2, 5},
    {0},
};
DFA out13 = {
    {0, 1, 2, 3},
    {'o', 'r'},
    {
        {{0, 'o'}, 1},
        {{0, 'r'}, 2},
        {{1, 'o'}, 3},
        {{1, 'r'}, 0},
        {{2, 'o'}, 3},
        {{2, 'r'}, 2},
        {{3, 'o'}, 3},
        {{3, 'r'}, 0},
    },
    0,
    {1, 2, 3},
};
MISNFA in14 = {
    {0, 1, 2, 3, 4, 5, 6},
    {'o', 'r'},
    {
        {{0, 'o'}, {0, 1, 4}},
        {{0, 'r'}, {5}},
        {{1, 'o'}, {4}},
        {{1, 'r'}, {2}},
        {{2, 'o'}, {0, 1}},
        {{2, 'r'}, {0, 5}},
        {{3, 'r'}, {2, 5}},
        {{5, 'o'}, {0, 1}},
        {{5, 'r'}, {0, 5}},
        {{6, 'r'}, {2}},
    },
    {2, 5},
    {},
};
DFA out14 = {
    {0},
    {'o', 'r'},
    {
        
    },
    0,
    {},
};

int main()
{
    assert(determinize(in0) == out0);
    assert(determinize(in1) == out1);
    assert(determinize(in2) == out2);
    assert(determinize(in3) == out3);
    assert(determinize(in4) == out4);
    assert(determinize(in5) == out5);
    // assert(determinize(in6) == out6);
    // assert(determinize(in7) == out7);
    // assert(determinize(in8) == out8);
    // assert(determinize(in9) == out9);
    // assert(determinize(in10) == out10);
    // assert(determinize(in11) == out11);
    // assert(determinize(in12) == out12);
    // assert(determinize(in13) == out13);
    
    assert(determinize(in14) == out14);

    return 0;
}
#endif
