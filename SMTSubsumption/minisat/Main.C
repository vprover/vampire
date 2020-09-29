/******************************************************************************************[Main.C]
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

#include "Solver.h"
#include <ctime>
#include <unistd.h>
#include <signal.h>
#include <zlib.h>


//=================================================================================================
// BCNF Parser:


#define CHUNK_LIMIT 1048576

static void parse_BCNF(cchar* filename, Solver& S)
{
    FILE*   in = fopen(filename, "rb");
    if (in == NULL) fprintf(stderr, "ERROR! Could not open file: %s\n", filename), exit(1);

    char    header[16];
    fread(header, 1, 16, in);
    if (strncmp(header, "BCNF", 4) != 0) fprintf(stderr, "ERROR! Not a BCNF file: %s\n", filename), exit(1);
    if (*(int*)(header+4) != 0x01020304) fprintf(stderr, "ERROR! BCNF file in unsupported byte-order: %s\n", filename), exit(1);

    int      n_vars    = *(int*)(header+ 8);
    //int    n_clauses = *(int*)(header+12);
    int*     buf       = xmalloc<int>(CHUNK_LIMIT);
    int      buf_sz;
    vec<Lit> c;

    for (int i = 0; i < n_vars; i++) S.newVar();

    for(;;){
        int n = fread(&buf_sz, 4, 1, in);
        if (n != 1) break;
        assert(buf_sz <= CHUNK_LIMIT);
        fread(buf, 4, buf_sz, in);

        int* p = buf;
        while (*p != -1){
            int size = *p++;
            c.clear();
            c.growTo(size);
            for (int i = 0; i < size; i++)
                c[i] = toLit(p[i]);
            p += size;

            S.addClause(c);     // Add clause.
            if (!S.okay()){
                xfree(buf); fclose(in);
                return; }
        }
    }

    xfree(buf);
    fclose(in);
}


//=================================================================================================
// DIMACS Parser:


class StreamBuffer {
    gzFile  in;
    char    buf[CHUNK_LIMIT];
    int     pos;
    int     size;

    void assureLookahead() {
        if (pos >= size) {
            pos  = 0;
            size = gzread(in, buf, sizeof(buf)); } }

public:
    StreamBuffer(gzFile i) : in(i), pos(0), size(0) {
        assureLookahead(); }

    int  operator *  () { return (pos >= size) ? EOF : buf[pos]; }
    void operator ++ () { pos++; assureLookahead(); }
};

//- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

template<class B>
static void skipWhitespace(B& in) {
    while ((*in >= 9 && *in <= 13) || *in == 32)
        ++in; }

template<class B>
static void skipLine(B& in) {
    for (;;){
        if (*in == EOF) return;
        if (*in == '\n') { ++in; return; }
        ++in; } }

template<class B>
static int parseInt(B& in) {
    int     val = 0;
    bool    neg = false;
    skipWhitespace(in);
    if      (*in == '-') neg = true, ++in;
    else if (*in == '+') ++in;
    if (*in < '0' || *in > '9') fprintf(stderr, "PARSE ERROR! Unexpected char: %c\n", *in), exit(3);
    while (*in >= '0' && *in <= '9')
        val = val*10 + (*in - '0'),
        ++in;
    return neg ? -val : val; }

template<class B>
static void readClause(B& in, Solver& S, vec<Lit>& lits) {
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

template<class B>
static void parse_DIMACS_main(B& in, Solver& S) {
    vec<Lit> lits;
    for (;;){
        skipWhitespace(in);
        if (*in == EOF)
            break;
        else if (*in == 'c' || *in == 'p')
            skipLine(in);
        else
            readClause(in, S, lits),
            S.addClause(lits);
    }
}

// Inserts problem into solver.
//
static void parse_DIMACS(gzFile input_stream, Solver& S) {
    StreamBuffer in(input_stream);
    parse_DIMACS_main(in, S); }


//=================================================================================================


void printStats(SolverStats& stats)
{
    double  cpu_time = cpuTime();
    int64   mem_used = memUsed();
    reportf("restarts              : %"I64_fmt"\n", stats.starts);
    reportf("conflicts             : %-12"I64_fmt"   (%.0f /sec)\n", stats.conflicts   , stats.conflicts   /cpu_time);
    reportf("decisions             : %-12"I64_fmt"   (%.0f /sec)\n", stats.decisions   , stats.decisions   /cpu_time);
    reportf("propagations          : %-12"I64_fmt"   (%.0f /sec)\n", stats.propagations, stats.propagations/cpu_time);
    reportf("conflict literals     : %-12"I64_fmt"   (%4.2f %% deleted)\n", stats.tot_literals, (stats.max_literals - stats.tot_literals)*100 / (double)stats.max_literals);
    if (mem_used != 0) reportf("Memory used           : %.2f MB\n", mem_used / 1048576.0);
    reportf("CPU time              : %g s\n", cpu_time);
}

Solver* solver;
static void SIGINT_handler(int signum) {
    reportf("\n"); reportf("*** INTERRUPTED ***\n");
    printStats(solver->stats);
    reportf("\n"); reportf("*** INTERRUPTED ***\n");
    exit(1); }


//=================================================================================================
// Main:


int main(int argc, char** argv)
{
    Solver      S;

    if (argc == 2 && (strcmp(argv[1], "-h") == 0 || strcmp(argv[1], "--help") == 0))
        reportf("USAGE: %s <input-file> <result-output-file>\n  where the input may be either in plain/gzipped DIMACS format or in BCNF.\n", argv[0]),
        exit(0);

    if (argc >= 2 && strlen(argv[1]) >= 5 && strcmp(&argv[1][strlen(argv[1])-5], ".bcnf") == 0)
        parse_BCNF(argv[1], S);
    else{
        if (argc == 1)
            reportf("Reading from standard input... Use '-h' or '--help' for help.\n");

        gzFile in = (argc == 1) ? gzdopen(0, "rb") : gzopen(argv[1], "rb");
        if (in == NULL)
            fprintf(stderr, "ERROR! Could not open file: %s\n", argc == 1 ? "<stdin>" : argv[1]),
            exit(1);
        parse_DIMACS(in, S);
        gzclose(in);
    }
    FILE* res = (argc >= 3) ? fopen(argv[2], "wb") : NULL;

    if (!S.okay()){
        if (res != NULL) fprintf(res, "UNSAT\n"), fclose(res);
        reportf("Trivial problem\n");
        reportf("UNSATISFIABLE\n");
        exit(20);
    }

    S.verbosity = 1;
    solver = &S;
    signal(SIGINT,SIGINT_handler);
    signal(SIGHUP,SIGINT_handler);

    S.solve();
    printStats(S.stats);
    reportf("\n");
    reportf(S.okay() ? "SATISFIABLE\n" : "UNSATISFIABLE\n");

    if (res != NULL){
        if (S.okay()){
            fprintf(res, "SAT\n");
            for (int i = 0; i < S.nVars(); i++)
                if (S.model[i] != l_Undef)
                    fprintf(res, "%s%s%d", (i==0)?"":" ", (S.model[i]==l_True)?"":"-", i+1);
            fprintf(res, " 0\n");
        }else
            fprintf(res, "UNSAT\n");
        fclose(res);
    }

    exit(S.okay() ? 10 : 20);     // (faster than "return", which will invoke the destructor for 'Solver')
}
