////////////////////////////////////////////////////////////////////////////
//                                                                      
//  This file contains the code of the heuristic EST described in  
//  E.G. Birgin, P. Feofiloff, C.G. Fernandes, E.L. de Melo, M.T.I. Oshiro, 
//  D.P. Ronconi, 
//  "A MILP model for an extended version of the Flexible Job Shop Problem", 
//  submitted, 2012.
//                                                                      
////////////////////////////////////////////////////////////////////////////

// We are given a dag (acyclic digraph) (V, A).  The vertices of the
// dag are also known as operations and the arcs are known as (hard)
// precedence constraints.
//
// We are also given a set {0,..,numm-1} of machines.  For each 
// vertex v and machine k, we have strictly positive processing 
// time Prt[v][k].  If v cannot be processed on machine k, we 
// have Prt[v][k] == infinite. Of course, for each vertex v there 
// is at least one machine k such that Prt[v][k] < infinite.
//
// Let uu[0..n-1] be a topological ordering of V in the dag (V, A).
// (Hence, for every (uu[i],uu[j]) in A we have i < j.) Let 
// ff[0..n-1] be the corresponding machine assignment: uu[i] is to 
// be processed on machine ff[i]. 
// The selection defined by uu and ff is the set Y of all ordered 
// pairs (uu[i],uu[j]) such that i < j and ff[i] == ff[j].
// The digraph (V, A+Y) is, of course, a dag.
//
// The length of a path (v0,..,vj,w) in dag (V, A+Y) is the sum
// p[v0] + .. + p[vj], where p[vi] = Prt[vi][k] and k is the machine
// that has been assigned to vi.
//
// Our goal: find uu[0..n-1] and ff[0..n-1] such that the makespan 
// mks(A+Y) of (V, A+Y) is reasonably small.

// We construct a solution uu[0..n-1], ff[0..n-1] greedily.
// In each iteration, we choose a pair (uu[q],ff[q]) 
// whose execution can start the earliest 
// (based on uu[0..q-1], ff[0..q-1]).
// When there is a tie, we choose a pair (uu[q],ff[q]) 
// that will maximize the longest path from uu[q] 
// based on the arcs in A and the mean processing times.


#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>
#include <time.h>
#include <iostream>
#include <vector>

using namespace std;

// Macros
////////////////////////////////////////////////////////////////////
#define MAX(A,B) (((A) > (B)) ? (A) : (B))
#define Free(A) {free((A)); (A) = NULL;}
#define INPUTBUFFERSIZE 128


// Global variables 
////////////////////////////////////////////////////////////////////

// The vertices of the digraph are represented by objects of type 
// vertex.  The vertices of our digraph are 0,..,n-1.
#define vertex int
int n;

// The digraph (V, A) has numA arcs (i.e., numA = |A|).
int numA;

// Machines are objects of type machine.  The machines are 
// 0,1,..,numm-1.
#define machine int
int numm;

// The adjacency matrix of the digraph is Adj[0..n-1][0..n-1].
// For each pair (v,w) of vertices, Adj[v][w] is
//   'A' if (v,w) is an arc
//   ' ' otherwise (for example, if v == w).
vector<vector<char>> Adj;

// Prt[v][k] is the processing time of vertex v on machine k.
// We assume Prt[v][k] > 0 for all v and all k and Prt[v][k] 
// is infinite iff v cannot be processed on machine k.
#define dtime double
#define time int
vector<vector<int>> Prt;

// Infinite ia a number larger than the sum_v max_k Prt[v][k], 
// where the sum is over all the vertices v and 
// max is over all the machines that can process v.
int infinite;

// Array uu[0..n-1] is a topological ordering of the vertices of 
// dag (V, A).  Array ff[0..n-1] is the corresponding machine
// assignment: uu[i] will be processed on machine ff[i].
// (Of course Prt[uu[i]][ff[i]] < infinite.)
vector<vertex> uu;
vector<machine> ff;

// For i = 0,..,n-1, st[i] and ct[i] are the starting and completion
// times of operation uu[i] in the schedule defines by uu[] an ff[].
vector<int> st, ct;

// The makespan determined by uu[0..n-1] and ff[0..n-1].
int mks;

// Messages
char MESSG[256];



// Prototypes of functions
////////////////////////////////////////////////////////////////////
void EST_Heuristic(void);
vector<double> LongestPathsFrom(vector<vector<char>> adj, vector<double> meanprt);
void PrintAdj(char** aa);
void Print(char* MESSG);
void* Malloc(unsigned int nbytes);
void ReadAndPrepareData(void);
void FillBuffer(char buffer[]);


////////////////////////////////////////////////////////////////////
// Program
////////////////////////////////////////////////////////////////////

int main(void) {
    int i;
    ReadAndPrepareData();

    uu = vector<int>(n);
    ff = vector<int>(n);
    st = vector<int>(n);
    ct = vector<int>(n);
    EST_Heuristic();
    sprintf_s(MESSG, "mks=%d\n", mks);
    Print(MESSG);
    printf("\n i uu[i] ff[i] st[i] ct[i]\n");
    for (i = 0; i < n; ++i)
        printf("%2d %5d %5d %5d %5d\n", i, uu[i], ff[i], st[i], ct[i]);

    ff.end();
    uu.end();
    st.end();
    ct.end();
    return EXIT_SUCCESS;
}


// Earliest Starting Time heuristic.  Receives dag (V, A) and 
// processing times Prt[][].  Computes a permutation uu[0..n-1] 
// of V and a corresponding machine assignment ff[0..n-1].
// The function returns the makespan of the dag (V, A+Y),
// with Y being defined by uu[] and ff[].
// Global constants used: Adj, n, numm, 
// Prt[0..n-1][0..numm-1], infinite.
// Global variables computed: uu[0..n-1], ff[0..n-1], 
// st[0..n-1], ct[0..n-1], mks.
//
void EST_Heuristic(void) {
    vertex v, w, xx;
    machine k, ll;
    vector<double> meanprt;
    int i, q;
    vector<int> U; // characteristic vector of the set {uu[1],..,uu[q-1]} in V
    vector<int> rdy, avl;
    time earlst;
    vector<double> lpfrom;
    dtime maxlpfrom;
    meanprt = vector<double>(n);
    for (v = 0; v < n; ++v) {
        int howmany = 0;
        meanprt[v] = 0.0;
        for (k = 0; k < numm; ++k) {
            if (Prt[v][k] < infinite) {
                meanprt[v] += Prt[v][k];
                howmany++;
            }
        }
        meanprt[v] /= howmany;
    }
    // meanprt[v] is the mean processing time of v
    lpfrom = LongestPathsFrom(Adj, meanprt);
    for (w = 0; w < n; ++w)
        lpfrom[w] += meanprt[w];
    // lpfrom[w] is the largest sum of the form
    // meaprt[x_1] + meanprt[x_2] + ... + meanprt[x_r]
    // where (w,x_1,x_2,...,x_r) is a (directed) path
    meanprt.end();
    U = vector<int>(n);
    for (v = 0; v < n; ++v) U[v] = 0;
    for (q = 0; q < n; ++q) uu[q] = -99999; // for debugging
    avl = vector<int>(numm);
    for (k = 0; k < numm; ++k) avl[k] = 0;
    rdy = vector<int>(n);
    mks = 0;
    // main loop
    for (q = 0; q < n; ++q) {
        // we already have a sequence uu[0..q-1] of vertices
        // and a corresponding sequence ff[0..q-1] of machines
        // machine k will be available at time avl[k]
        for (w = 0; w < n; ++w) {
            if (U[w] == 0) {
                rdy[w] = 0;
                for (i = 0; i < q; ++i)
                    if (Adj[uu[i]][w] == 'A')
                        rdy[w] = MAX(rdy[w], ct[i]);
                for (v = 0; v < n; ++v)
                    if (U[v] == 0 && Adj[v][w] == 'A')
                        rdy[w] = infinite;
                // rdy[w] is the moment w is ready for processing
                // (i.e., all pre-requisite operations are done)
                // if rdy[w] == infinite then w is not ready
            }
        }
        earlst = infinite;
        maxlpfrom = -1.0; // to appease compiler
        xx = -1; // to appease compiler
        ll = -1; // to appease compiler
        for (w = 0; w < n; ++w) {
            if (U[w] == 1 || rdy[w] == infinite) continue;
            for (k = 0; k < numm; ++k) {
                time t;
                if (Prt[w][k] == infinite) continue;
                t = MAX(rdy[w], avl[k]);
                if (earlst > t || (earlst == t && maxlpfrom < lpfrom[w])) {
                    earlst = t;
                    xx = w;
                    ll = k;
                    maxlpfrom = lpfrom[w];
                }
            }
        }
        // (xx,ll) is the best candidade for (uu[q],ff[q])
        // its starting time is earlst
        U[xx] = 1;
        uu[q] = xx;
        ff[q] = ll;
        st[q] = earlst;
        ct[q] = earlst + Prt[xx][ll];
        avl[ll] = ct[q];
        mks = MAX(mks, ct[q]);
    }
    U.end();
    rdy.end();
    avl.end();
    lpfrom.end();
}


// This function receives a digraph (V, A) represented by matrix Adj.
// It returns NULL if (V, A) is not a dag.
// Otherwise, returns array lpfrom[0..n-1] such that, 
// for each vertex v, lpfrom[v] is the cost of a maximum-cost path 
// among those starting at v.  The costs are relative to meanprt.
// Global variables used: n. 
//
vector<double> LongestPathsFrom(vector<vector<char>> Adj, vector<double> meanprt) {
    vector<double> lpfrom;
    vertex v, w;
    vector<int> outdeg(n);
    vector<int> queue(n);
    int start, end; // queue[start..end-1] is a queue of vertices
    start = end = 0;
    for (v = 0; v < n; ++v) {
        outdeg[v] = 0;
        for (w = 0; w < n; ++w)
            if (Adj[v][w] == 'A')
                ++outdeg[v];
        if (outdeg[v] == 0)
            queue[end++] = v;
    }
    // now outdeg[v] is the outdegree of v
    
    lpfrom = vector<double>(n); 
    for (w = 0; w < n; ++w)
        lpfrom[w] = 0;
    while (start < end) {
        w = queue[start++];
        for (v = 0; v < n; ++v) {
            if (Adj[v][w] != 'A') continue;
            if (lpfrom[v] < lpfrom[w] + meanprt[w])
                lpfrom[v] = lpfrom[w] + meanprt[w];
            if (--outdeg[v] == 0)
                queue[end++] = v;
        }
    }
    outdeg.end();
    queue.end();
    if (end < n)
        exit(-1);
    return lpfrom;
}



////////////////////////////////////////////////////////////////////
// Run-of-the-mill tools
////////////////////////////////////////////////////////////////////

// This function reads the data and 
// sets global variables (n, numA, numm, Adj[][], Prt[][], etc.)
//
void ReadAndPrepareData(void) {
    int i, j;
    vertex v, w;
    machine k;
    char buffer[INPUTBUFFERSIZE];
    do
        FillBuffer(buffer);
    while (buffer[0] == '#' || buffer[0] == '\n');
    sscanf_s(buffer, "%d %d %d", &n, &numA, &numm);
    sprintf_s(MESSG, "\n");
    //sprintf_s
    // read adjacency matrix 
    Adj = vector<vector<char>>(n);
    for (v = 0; v < n; ++v) {
        Adj[v] = vector<char>(n);
        for (w = 0; w < n; ++w)
            Adj[v][w] = ' ';
    }
    i = 0;
    while (i < numA) {
        FillBuffer(buffer);
        if (buffer[0] != '#') {
            sscanf_s(buffer, "%d %d", &v, &w);
            if (v == w) {
                sprintf_s(MESSG, "*** No loops, please!\n\n");
                Print(MESSG);
                exit(EXIT_FAILURE);
            }
            if (Adj[v][w] == 'A') {
                sprintf_s(MESSG, "*** Repeated arc %d-%d\n", v, w);
                Print(MESSG);
                exit(EXIT_FAILURE);
            }
            Adj[v][w] = 'A';
            i++;
        }
    }
    //
    // read machines and processing times
    Prt = vector<vector<int>>(n);
    for (v = 0; v < n; ++v) {
        Prt[v] = vector<int>(numm);
        for (k = 0; k < numm; ++k)
            Prt[v][k] = -1; // will be later replaced by infinite
    }
    v = 0;
    while (v < n) {
        machine mchnv;
        int prtv;
        int hm;
        char c1;

        c1 = getchar();
        while (c1 == '#' || c1 == '\n') {
            if (c1 != '\n') scanf_s(" %*[^\n] ");
            c1 = getchar();
        }
        ungetc(c1, stdin);
        scanf_s("%d", &hm); // how many machines for this vertex v 
        if (hm <= 0) {
            sprintf_s(MESSG, "*** No machine specified for %d\n", v);
            Print(MESSG);
            exit(EXIT_FAILURE);
        }
        for (j = 0; j < hm; ++j) {
            scanf_s("%d %d", &mchnv, &prtv);
            if (mchnv < 0 || mchnv >= numm) {
                sprintf_s(MESSG, "*** Machine %d out of range\n", mchnv);
                Print(MESSG);
                exit(EXIT_FAILURE);
            }
            if (prtv <= 0) {
                sprintf_s(MESSG, "*** Processing times must be positive\n");
                Print(MESSG);
                exit(EXIT_FAILURE);
            }
            Prt[v][mchnv] = prtv;
        }
        ++v;
    }
    // compute value of infinite
    infinite = 1;
    for (v = 0; v < n; ++v) {
        int largest = 0;
        for (k = 0; k < numm; ++k)
            if (Prt[v][k] != -1 && largest < Prt[v][k])
                largest = Prt[v][k];
        infinite += largest;
    }
    if (infinite > INT_MAX / 100) {
        sprintf_s(MESSG, "\n*** Sum of processing times greater than %d\n",
            INT_MAX / 100);
        Print(MESSG);
        exit(EXIT_FAILURE);
    }

    for (v = 0; v < n; ++v)
        for (k = 0; k < numm; ++k)
            if (Prt[v][k] == -1)
                Prt[v][k] = infinite;
}


// Reads a line of characters from the keyboard into a buffer and returns
// the buffer as a string (i.e., with a '\0' in place of the '\n'). 
// The line can have at most INPUTBUFFERSIZE characters 
// (not counting the final '\n').
//
void FillBuffer(char buffer[]) {
    int k, ch;
    k = 0;
    while ((ch = getc(stdin)) != '\n' && ch != EOF) {
        if (k >= INPUTBUFFERSIZE) {
            sprintf_s(MESSG, "*** Input line longer than %d\n", INPUTBUFFERSIZE);
            Print(MESSG);
            exit(EXIT_FAILURE);
        }
        buffer[k++] = ch;
    }
    buffer[k] = '\0';
}


// Prints adjacency matrix aa[0..n-1][0..n-1].
// For each vertex v, prints array aa[v].
// Global variable used: n.
//
void PrintAdj(char** aa) {
    vertex v, w;
    for (v = 0; v < n; v++) {
        printf("%2d:", v);
        for (w = 0; w < n; w++)
            if (aa[v][w] != ' ')
                printf(" %2d", w);
        printf("\n");
    }
    fflush(stdout);
}


// Prints message messg to stdout and stderr.
//
void Print(char* MESSG) {
    fprintf(stderr, "%s", MESSG);
    printf("%s", MESSG);
    fflush(stdout);
}


void* Malloc(unsigned int nbytes) {
    void* ptr;
    ptr = malloc(nbytes);
    if (ptr == NULL) {
        sprintf_s(MESSG, "*** malloc returned NULL!\n");
        Print(MESSG);
        exit(EXIT_FAILURE);
    }
    return ptr;
}