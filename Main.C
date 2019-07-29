/**************************************************************************************************
MiniSat -- Copyright (c) 2003-2005, Niklas Een, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include "SubQ.h"
#include "Solver.h"
#include <ctime>
#include <unistd.h>
#include <signal.h>
#include <zlib.h>
#include <chrono>
#include <iostream>
#include <set>
#include <deque>
#include <vector>
#include <string>

using std::cout;
using std::endl;
using std::set;
using std::deque;
using std::vector;
using std::string;
namespace chrono = std::chrono;

//=================================================================================================
// Helpers:


// Reads an input stream to end-of-file and returns the result as a 'char*' terminated by '\0'
// (dynamic allocation in case 'in' is standard input).
//
char* readFile(gzFile in)
{
    char*   data = xmalloc<char>(65536);
    int     cap  = 65536;
    int     size = 0;

    while (!gzeof(in)){
        if (size == cap){
            cap *= 2;
            data = xrealloc(data, cap); }
        size += gzread(in, &data[size], 65536);
    }
    data = xrealloc(data, size+1);
    data[size] = '\0';

    return data;
}


//=================================================================================================
// DIMACS Parser:


static void skipWhitespace(char*& in) {
    while ((*in >= 9 && *in <= 13) || *in == 32)
        in++; }

static void skipLine(char*& in) {
    for (;;){
        if (*in == 0) return;
        if (*in == '\n') { in++; return; }
        in++; } }

static int parseInt(char*& in) {
    int     val = 0;
    bool    neg = false;
    skipWhitespace(in);
    if      (*in == '-') neg = true, in++;
    else if (*in == '+') in++;
    if (*in < '0' || *in > '9') fprintf(stderr, "PARSE ERROR! Unexpected char: %c\n", *in), exit(1);
    while (*in >= '0' && *in <= '9')
        val = val*10 + (*in - '0'),
        in++;
    return neg ? -val : val; }

static void readClause(char*& in, Solver& S, vec<Lit>& lits) {
    int     parsed_lit, var;
    lits.clear();
    for (;;){
        parsed_lit = parseInt(in);
        if (parsed_lit == 0) break;
        var = abs(parsed_lit)-1;
        while (var >= S.nVars()) S.newVar();
        lits.push( (parsed_lit > 0) ? Lit(var) : ~Lit(var) );
    }
}

static bool parse_DIMACS_main(char* in, Solver& S) {
    vec<Lit>    lits;
    for (;;){
        skipWhitespace(in);
        if (*in == 0)
            break;
        else if (*in == 'c' || *in == 'p')
            skipLine(in);
        else{
            readClause(in, S, lits);
            S.addClause(lits);
            if (!S.okay())
                return false;
        }
    }
    S.simplifyDB();
    return S.okay();
}

// Inserts problem into solver. Returns FALSE upon immediate conflict.
//
bool parse_DIMACS(gzFile in, Solver& S) {
    char* text = readFile(in);
    bool ret = parse_DIMACS_main(text, S);
    free(text);
    return ret; }


static void readClauseAfasat(char*& in, Solver& S, vec<Lit>& lits) {
    int var;
    bool neg, pure;

    lits.clear();
    while (*in != '\n') {
        skipWhitespace(in);

        pure = *in == 'p';
        if (pure) in++;

        neg = *in == '-';
        if (neg) in++;

        var = parseInt(in);
        while (var >= S.pures.size()) S.pures.push(false);
        while (var >= S.output_map.size()) S.output_map.push(-1);
        while (var >= S.nVars()) S.newVar();

        lits.push( neg ? ~Lit(var) : Lit(var) );
    }
    in++;
}

static bool parse_AFASAT_main(char* in, Solver& S, int* initial, int* acnt) {
    *acnt = parseInt(in); in++;
    skipLine(in); // blank

    //pures
    while (*in != '\n') {
        int var = parseInt(in);
        while (var >= S.pures.size()) S.pures.push(false);
        S.pures[var] = true;
    }
    skipLine(in); // blank

    *initial = parseInt(in); in++;
    skipLine(in); // blank

    // out
    while (*in != '\n') {
        skipWhitespace(in);
        bool neg = *in == '-';
        if (neg) in++;

        int var = parseInt(in);

        while (var >= S.output_map.size()) S.output_map.push(-1);
        S.output_map[var] = S.outputs.size();

        Lit lit = neg ? ~Lit(var) : Lit(var);
        S.outputs.push(lit);
        while (var >= S.pures.size()) S.pures.push(false);
        if (!S.pures[var]) S.impure_outputs.push(lit);
    }
    in++;
    skipLine(in); // blank

    // clauses
    vec<Lit>    lits;
    while (*in != '\n') {
        readClauseAfasat(in, S, lits);
        S.addClause(lits);
        if (!S.okay())
            return false;
    }
    return S.okay();
}

bool parse_AFASAT(gzFile in, Solver& S, int* initial, int* acnt) {
    char* text = readFile(in);
    bool ret = parse_AFASAT_main(text, S, initial, acnt);
    free(text);
    return ret;
}
//=================================================================================================


void printStats(SolverStats& stats, double cpu_time)
{
    printf("restarts              : %" I64_fmt "\n", stats.starts);
    printf("conflicts             : %-12" I64_fmt "   (%.0f /sec)\n", stats.conflicts   , stats.conflicts   /cpu_time);
    printf("decisions             : %-12" I64_fmt "   (%.0f /sec)\n", stats.decisions   , stats.decisions   /cpu_time);
    printf("propagations          : %-12" I64_fmt "   (%.0f /sec)\n", stats.propagations, stats.propagations/cpu_time);
    printf("inspects              : %-12" I64_fmt "   (%.0f /sec)\n", stats.inspects    , stats.inspects    /cpu_time);
    printf("CPU time              : %g s\n", cpu_time);
}

Solver* solver;
static void SIGINT_handler(int signum) {
    printf("\n"); printf("*** INTERRUPTED ***\n");
    printStats(solver->stats, cpuTime());
    printf("\n"); printf("*** INTERRUPTED ***\n");
    exit(0); }


//=================================================================================================

struct LeastSizeCompare
{
    bool operator()(const vec<Lit>* lhs, const vec<Lit>* rhs)
    {
        // return lhs->size() < rhs->size();
        if (lhs->size() != rhs->size()) return lhs->size() < rhs->size();
        for (int i = 0; i < lhs->size(); i++) {
            if (lhs[i] != rhs[i]) return lhs[i] < rhs[i];
        }
        return false;
    }
};

struct CellContainer {
    virtual void add(vec<Lit>* x) = 0;
    virtual int size() const = 0;
    virtual vec<Lit>* pop() = 0;
    virtual ~CellContainer() {};
};

class CellContainerSet : public CellContainer {
    set<vec<Lit>*, LeastSizeCompare> data;
public:
    CellContainerSet() {}
    void add(vec<Lit>* x) { data.insert(x); }
    int size() const { return data.size(); }
    vec<Lit>* pop() {
        auto it = data.begin();
        vec<Lit>* result = *it;
        data.erase(it);
        return result;
    }
};

class CellContainerBfs : public CellContainer {
    deque<vec<Lit>*> data;
public:
    CellContainerBfs() {}
    void add(vec<Lit>* x) { data.push_back(x); }
    int size() const { return data.size(); }
    vec<Lit>* pop() {
        vec<Lit>* result = data.front();
        data.pop_front();
        return result;
    }
};

class CellContainerDfs : public CellContainer {
    vector<vec<Lit>*> data;
public:
    CellContainerDfs() {}
    void add(vec<Lit>* x) { data.push_back(x); }
    int size() const { return data.size(); }
    vec<Lit>* pop() {
        vec<Lit>* result = data.back();
        data.pop_back();
        return result;
    }
};


bool extract_sat_result(
    Solver &S,
    vec<Lit> &cell_out,
    vec<Lit> &cell_in,
    int initial,
    // only for logging purposes:
    chrono::duration<double> &elapsed_sat,
    const CellContainer &cell_container,
    int acnt, int satCnt, int unsatCnt, int &maxDepth, int omitted
) {
    if (verbosity >= -1)
        printf("***********************************************\nq ");
    for (int i = 0; i < S.outputs.size(); i++) {
        Lit out = S.outputs[i];

        if (S.value(out) == l_False) // WARNING solver must not be reset after sat
        {
            if (verbosity >= -1) printf("0");

            cell_in.push(~Lit(i));
            for (int j = 0; j < cell_out.size(); j++) {
                if (out == cell_out[j]) goto outputfor;
            }
            cell_out.push(out);
        }
        else if (i == initial) return true;
        else if (verbosity >= -1)
            printf("%c", S.value(out) == l_Undef ? 'x' : '1');

outputfor:
        ((void)0);
    }

    if (verbosity >= -1) {
        printf("\n");
        printf("\na ");
        for (int i = S.outputs.size(); i < S.outputs.size() + acnt; i++) {
            printf(
                "%c",
                S.model[i] == l_True
                    ? '1'
                    : (S.model[i] == l_False ? '0' : 'x')
            );
        }
        printf("\n\n");
        cout << satCnt << " " << unsatCnt << " " << omitted
          << " " << cell_container.size() << " " << elapsed_sat.count() << endl;
        printf("-----------------------------------------------\n\n");
    }
    maxDepth = max(cell_container.size(), maxDepth);

    return false;
}


int main(int argc, char** argv)
{
    GlobSolver  GS;
    Solver      S(GS);
    bool        st;
    int initial, acnt;

    gzFile in = argc == 1 ? gzdopen(0, "rb") : gzopen(argv[1], "rb");
    if (in == NULL)
        fprintf(stderr, "ERROR! Could not open file: %s\n", argc == 1 ? "<stdin>" : argv[1]),
        exit(1);
    st = parse_AFASAT(in, S, &initial, &acnt);
    gzclose(in);

    if (!st)
        printf("Trivial problem\nUNSATISFIABLE\n"),
        exit(20);

    solver = &S;
    signal(SIGINT,SIGINT_handler);

    string cont_str(argv[2]);
    CellContainer *cell_container =
        (cont_str == string("set"))
        ? (CellContainer*)new CellContainerSet()
        : (cont_str == string("dfs"))
        ? (CellContainer*)new CellContainerDfs()
        : (CellContainer*)new CellContainerBfs();

    vec<Lit> *cell_in = new vec<Lit>(S.outputs.size());
    vec<Lit> cell_out;

    for (int i = 0; i < S.outputs.size(); i++) (*cell_in)[i] = ~Lit(i);

    chrono::duration<double> elapsed_sat = chrono::duration<double>::zero();
    auto tic_all = chrono::steady_clock::now();
    int satCnt = 0;
    int unsatCnt = 0;
    int maxDepth = 0;

    auto tic = chrono::steady_clock::now();

    string supq_str(argv[5]);
    SupQ *supq = (supq_str == string("vec"))
      ? (SupQ*)new SupQVec()
      : new SupQ();

    int omitted = 0;

    int unsat_limit = std::stoi(argv[4]);

    if (string(argv[3]) == string("resetallLocBfs")) goto resetallLocBfs;
    if (string(argv[3]) == string("resetallImmediate")) goto resetallImmediate;

    while (true) {
        if (supq->get(*cell_in)) omitted++;
        else {
          supq->add(*cell_in);

          tic = chrono::steady_clock::now();
          st = S.solve(*cell_in);
          elapsed_sat = elapsed_sat + chrono::steady_clock::now() - tic;

          delete cell_in;

          if (st) {
              tic = chrono::steady_clock::now();
              while (S.resume()) {
                  elapsed_sat = elapsed_sat + chrono::steady_clock::now() - tic;
                  satCnt++;

                  cell_out.clear();
                  cell_in = new vec<Lit>();

                  if (extract_sat_result(
                          S, cell_out, *cell_in, initial, elapsed_sat,
                          *cell_container, acnt, satCnt, unsatCnt, maxDepth,
                          omitted))
                      goto l_reach;

                  cell_container->add(cell_in);

                  tic = chrono::steady_clock::now();
                  if (!S.addConflictingClause(cell_out)) break;
              };
              elapsed_sat = elapsed_sat + chrono::steady_clock::now() - tic;
          }

          unsatCnt++;
          if (unsat_limit >= 0 && unsatCnt > unsat_limit) goto statPrint;
        }

        if (!cell_container->size()) break;
        cell_in = cell_container->pop();

        tic = chrono::steady_clock::now();
        S.reset();
        elapsed_sat = elapsed_sat + chrono::steady_clock::now() - tic;
    }

    goto l_unreach;

resetallLocBfs:

    while (true) {
        if (supq->get(*cell_in)) omitted++;
        else {
            supq->add(*cell_in);

            while (true) {
                tic = chrono::steady_clock::now();
                st = S.solve(*cell_in);
                st = st && S.resume();
                elapsed_sat = elapsed_sat + chrono::steady_clock::now() - tic;

                if (!st) break;

                satCnt++;

                cell_out.clear();
                vec<Lit> *cell_in2 = new vec<Lit>();

                if (extract_sat_result(
                        S, cell_out, *cell_in2, initial, elapsed_sat,
                        *cell_container, acnt, satCnt, unsatCnt, maxDepth,
                        omitted))
                    goto l_reach;

                cell_container->add(cell_in2);

                tic = chrono::steady_clock::now();
                S.reset();
                S.addClause(cell_out);
                elapsed_sat = elapsed_sat + chrono::steady_clock::now() - tic;
            }
        }

        unsatCnt++;
        delete cell_in;
        if (unsat_limit >= 0 && unsatCnt > unsat_limit) goto statPrint;

        if (!cell_container->size()) goto l_unreach;
        cell_in = cell_container->pop();

        tic = chrono::steady_clock::now();
        S.reset();
        elapsed_sat = elapsed_sat + chrono::steady_clock::now() - tic;
    }

resetallImmediate:

    while (true) {
        tic = chrono::steady_clock::now();
        st = S.solve(*cell_in);
        st = st && S.resume();
        elapsed_sat = elapsed_sat + chrono::steady_clock::now() - tic;

        if (st) {
            satCnt++;

            cell_container->add(cell_in);
            cell_out.clear();
            cell_in = new vec<Lit>();

            if (extract_sat_result(
                    S, cell_out, *cell_in, initial, elapsed_sat,
                    *cell_container, acnt, satCnt, unsatCnt, maxDepth,
                    omitted))
                goto l_reach;

            cell_container->add(cell_in);

            tic = chrono::steady_clock::now();
            S.reset();
            S.addClause(cell_out);
            elapsed_sat = elapsed_sat + chrono::steady_clock::now() - tic;
        }
        else {
            unsatCnt++;
            supq->add(*cell_in);

            delete cell_in;
            if (unsat_limit >= 0 && unsatCnt > unsat_limit) goto statPrint;
        }

        while (true) {
            if (!cell_container->size()) goto l_unreach;
            cell_in = cell_container->pop();

            if (supq->get(*cell_in)) omitted++;
            else break;
        }

        tic = chrono::steady_clock::now();
        S.reset();
        elapsed_sat = elapsed_sat + chrono::steady_clock::now() - tic;
    }

l_unreach:
    printf("1 ");
    goto statPrint;

l_reach:
    printf("0 ");
    goto statPrint;

statPrint:
    // printStats(S.stats, cpuTime());
    chrono::duration<double> elapsed_all = chrono::steady_clock::now() - tic_all;
    cout
      << satCnt << " "
      << unsatCnt << " "
      << maxDepth << " "
      << omitted << " "
      << elapsed_sat.count() << " "
      << elapsed_all.count() << " "
      << supq->elapsed_add.count() << " "
      << supq->elapsed_get.count() << endl;

    delete cell_container;
    delete supq;
    return 0;
}
