/***************************************************************************************[Solver.cc]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

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

#include <math.h>
#include <bits/stdc++.h>
#include "minisat/mtl/Alg.h"
#include "minisat/mtl/Sort.h"
#include "minisat/utils/System.h"
#include "minisat/core/Solver.h"
#include <semaphore.h>
#include <chrono>

using namespace Minisat;
using namespace std;


//=================================================================================================
// Options:


static const char*   _cat = "CORE";
static DoubleOption  opt_var_decay         (_cat, "var-decay",   "The variable activity decay factor",            0.95,     DoubleRange(0, false, 1, false));
static DoubleOption  opt_clause_decay      (_cat, "cla-decay",   "The clause activity decay factor",              0.999,    DoubleRange(0, false, 1, false));
static DoubleOption  opt_random_var_freq   (_cat, "rnd-freq",    "The frequency with which the decision heuristic tries to choose a random variable", 0, DoubleRange(0, true, 1, true));
static DoubleOption  opt_random_seed       (_cat, "rnd-seed",    "Used by the random variable selection",         91648253, DoubleRange(0, false, HUGE_VAL, false));
static IntOption     opt_ccmin_mode        (_cat, "ccmin-mode",  "Controls conflict clause minimization (0=none, 1=basic, 2=deep)", 2, IntRange(0, 2));
static IntOption     opt_phase_saving      (_cat, "phase-saving", "Controls the level of phase saving (0=none, 1=limited, 2=full)", 2, IntRange(0, 2));
static BoolOption    opt_rnd_init_act      (_cat, "rnd-init",    "Randomize the initial activity", false);
static BoolOption    opt_luby_restart      (_cat, "luby",        "Use the Luby restart sequence", true);
static IntOption     opt_restart_first     (_cat, "rfirst",      "The base restart interval", 100, IntRange(1, INT32_MAX));
static DoubleOption  opt_restart_inc       (_cat, "rinc",        "Restart interval increase factor", 2, DoubleRange(1, false, HUGE_VAL, false));
static DoubleOption  opt_garbage_frac      (_cat, "gc-frac",     "The fraction of wasted memory allowed before a garbage collection is triggered",  0.20, DoubleRange(0, false, HUGE_VAL, false));
static IntOption     opt_min_learnts_lim   (_cat, "min-learnts", "Minimum learnt clause limit",  0, IntRange(0, INT32_MAX));


//=================================================================================================
// Constructor/Destructor:



Solver::Solver():
    verbosity        (0)
  , var_decay        (opt_var_decay)
  , iter(0)
  , clause_decay     (opt_clause_decay)
  , random_var_freq  (opt_random_var_freq)
  , random_seed      (opt_random_seed)
  , luby_restart     (opt_luby_restart)
  , ccmin_mode       (opt_ccmin_mode)
  , phase_saving     (opt_phase_saving)
  , rnd_pol          (false)
  , rnd_init_act     (opt_rnd_init_act)
  , garbage_frac     (opt_garbage_frac)
  , min_learnts_lim  (opt_min_learnts_lim)
  , restart_first    (opt_restart_first)
  , restart_inc      (opt_restart_inc)
  , inter(0)
  , learntsize_factor((double)1/(double)3), learntsize_inc(1.1)
  , learntsize_adjust_start_confl (100)
  , learntsize_adjust_inc         (1.5)
  , solves(0), starts(0), decisions(0), rnd_decisions(0), propagations(0), conflicts(0)
  , dec_vars(0), num_clauses(0), num_learnts(0), clauses_literals(0), learnts_literals(0), max_literals(0), tot_literals(0)
  , watches            (WatcherDeleted(ca))
  , order_heap         (VarOrderLt(activity))
  , ok                 (true)
  , cla_inc            (1)
  , var_inc            (1)
  , qhead              (0)
  , simpDB_assigns     (-1)
  , simpDB_props       (0)
  , progress_estimate  (0)
  , remove_satisfied   (true)
  , next_var           (0)
  , conflict_budget    (-1)
  , propagation_budget (-1)
  , asynch_interrupt   (false)
  , sumPercentage      (0)
  , averageActivity    (0)
  , gcEvents           (0)
  , curr_restarts      (0)
{ 
    sem_init(&propagationDone,false,0);
    sem_init(&calculationDone,false,1);
    waitingThreads = 0;
}

Solver::Solver(string& logFile,string& outputFile):Solver(){
    this->logFile = fopen(logFile.c_str(),"wb");
    if (!this->logFile){
        cerr << "In Constructor Error opening log File " << endl;
        _exit(404);
    }
    this->outputFile = fopen(outputFile.c_str(),"wb");
    if (!this->outputFile){
        cerr << "In Constructor Error opening outputFile " << endl;
        _exit(404);
    }
    this->vizFlag = true;
}

Solver::~Solver(){
    if (vizFlag){
        fclose(logFile);
        fclose(outputFile);
    }
}


//=================================================================================================
// Minor methods:


// Creates a new SAT variable in the solver. If 'decision' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
//
Var Solver::newVar(lbool upol, bool dvar){
    Var v;
    if (free_vars.size() > 0){
        v = free_vars.last();
        free_vars.pop();
    }
    else v = next_var++;
    watches  .init(mkLit(v, false));
    watches  .init(mkLit(v, true ));
    assigns  .insert(v, l_Undef);
    vardata  .insert(v, mkVarData(CRef_Undef, 0));
    activity .insert(v, rnd_init_act ? drand(random_seed) * 0.00001 : 0);
    seen     .insert(v, 0);
    polarity .insert(v, true);
    user_pol .insert(v, upol);
    decision .reserve(v);
    trail    .capacity(v+1);
    setDecisionVar(v, dvar);
    return v;
}


// Note: at the moment, only unassigned variable will be released (this is to avoid duplicate
// releases of the same variable).
void Solver::releaseVar(Lit l){
    if (value(l) == l_Undef){
        addClause(l);
        released_vars.push(var(l));
    }
}


bool Solver::addClause_(vec<Lit>& ps){
    assert(decisionLevel() == 0);
    if (!ok) return false;
    sort(ps);
    Lit p; int i, j;
    for (i = j = 0, p = lit_Undef; i < ps.size(); i++)
        if (value(ps[i]) == l_True || ps[i] == ~p)
            return true;
        else if (value(ps[i]) != l_False && ps[i] != p)
            ps[j++] = p = ps[i];
    ps.shrink(i - j);

    if (ps.size() == 0) return ok = false;
    else if (ps.size() == 1){
        uncheckedEnqueue(ps[0]);
        return ok = (propagate() == CRef_Undef);
    }
    else{
        CRef cr = ca.alloc(ps, false);
        clauses.push(cr);
        attachClause(cr);
    }

    return true;
}


void Solver::attachClause(CRef cr){
    const Clause& c = ca[cr];
    assert(c.size() > 1);
    watches[~c[0]].push(Watcher(cr, c[1]));
    watches[~c[1]].push(Watcher(cr, c[0]));
    if (c.learnt()) {
        num_learnts++, learnts_literals += c.size();
        //TEMPLATE BEGIN LEARNT CLAUSE STATISTICES ATTACH
    }
    else {
        num_clauses++, clauses_literals += c.size();
        //TEMPLATE BEGIN ORIGINAL CLAUSE STATISTICS ATTACH
    }
    //TEMPLATE BEGIN GENERAL CLAUSE STATISTICS ATTACH
}


void Solver::detachClause(CRef cr, bool strict){
    const Clause& c = ca[cr];
    assert(c.size() > 1);
    if (strict){
        remove(watches[~c[0]], Watcher(cr, c[1]));
        remove(watches[~c[1]], Watcher(cr, c[0]));
    }else{
        watches.smudge(~c[0]);
        watches.smudge(~c[1]);
    }

    if (c.learnt()) {
        num_learnts--, learnts_literals -= c.size();
        //TEMPLATE BEGIN LEARNT CLAUSE STATISTICS DETACH
    }
    else {
        num_clauses--, clauses_literals -= c.size();
        //TEMPLATE END ORIGINAL CLAUSE STATISTICS DETACH
    }
    //TEMPLATE GENERAL CLAUSE STATISTICS DETACH
}


void Solver::removeClause(CRef cr) {
    Clause& c = ca[cr];
    detachClause(cr);
    if (locked(c)) vardata[var(c[0])].reason = CRef_Undef;
    c.mark(1); 
    ca.free(cr);
}


bool Solver::satisfied(const Clause& c) const {
    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) == l_True) return true;
    return false; 
}


void Solver::cancelUntil(int level) {
    if (decisionLevel() > level){
        for (int c = trail.size()-1; c >= trail_lim[level]; c--){
            Var      x  = var(trail[c]);
            assigns [x] = l_Undef;
            if (phase_saving > 1 || (phase_saving == 1 && c > trail_lim.last()))
                polarity[x] = sign(trail[c]);
            insertVarOrder(x); 
        }
        qhead = trail_lim[level];
        trail.shrink(trail.size() - trail_lim[level]);
        trail_lim.shrink(trail_lim.size() - level);
    } 
}

void Solver::get_clause_variable_ratio(){
    mtx.lock();
        waitingThreads++;
    mtx.unlock();
    sem_wait(&propagationDone);
    long vars = 0,clause = 0;
    for (int i = 0;i < nVars();i++) seenx[i]=0;
    for (int i = 0; i < clauses.size();i++){
        const Clause& c = ca[clauses[i]];
        vec<Var> curr_clause;
        bool flag = false;
        for (int j = 0;j < c.size();j++){
            Var v = var(c[j]);
            if (assigns[v] == l_Undef){
                if (!seenx[v]) {
                    curr_clause.push(v);
                    seenx[v]=1;
                    vars++;
                }
            }
            if (value(c[j]) == l_True){
                flag = true;
                break;
            }
        }
        if (flag){
            for (int i = 0;i < curr_clause.size();i++) {
                seenx[curr_clause[i]] = 0;
                vars--;
            }
        }
        else clause++;
    }
    (threadedTimestamp.size()==0)?threadedTimestamp.push(1):threadedTimestamp.push(threadedTimestamp.last()+1);
    clauseVariableRatioVector.push((double)clause/vars);
    sem_post(&calculationDone);
    mtx.lock();
        waitingThreads--;
    mtx.unlock();
}


//=================================================================================================
// Major methods:


Lit Solver::pickBranchLit(){
    Var next = var_Undef;
    if (drand(random_seed) < random_var_freq && !order_heap.empty()){
        next = order_heap[irand(random_seed,order_heap.size())];
        if (value(next) == l_Undef && decision[next]) rnd_decisions++; 
    }
    while (next == var_Undef || value(next) != l_Undef || !decision[next]){
        if (order_heap.empty()){
            next = var_Undef;
            break;
        }
        else next = order_heap.removeMin();
    }
    if (next == var_Undef) return lit_Undef;
    else if (user_pol[next] != l_Undef) return mkLit(next, user_pol[next] == l_True);
    else if (rnd_pol) return mkLit(next, drand(random_seed) < 0.5);
    else return mkLit(next, polarity[next]);
}


/*_________________________________________________________________________________________________
|
|  analyze : (confl : Clause*) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
|  
|  Description:
|    Analyze conflict and produce a reason clause.
|  
|    Pre-conditions:
|      * 'out_learnt' is assumed to be cleared.
|      * Current decision level must be greater than root level.
|  
|    Post-conditions:
|      * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
|      * If out_learnt.size() > 1 then 'out_learnt[1]' has the greatest decision level of the 
|        rest of literals. There may be others from the same level though.
|  
|________________________________________________________________________________________________@*/


void Solver::analyze(CRef confl, vec<Lit>& out_learnt, int& out_btlevel){
    int pathC = 0;
    Lit p     = lit_Undef;
    out_learnt.push();      
    int index   = trail.size() - 1;
    do{
        assert(confl != CRef_Undef); 
        Clause& c = ca[confl];
        if (c.learnt()) claBumpActivity(c);

        for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++){
            Lit q = c[j];

            if (!seen[var(q)] && level(var(q)) > 0){
                varBumpActivity(var(q));
                seen[var(q)] = 1;
                if (level(var(q)) >= decisionLevel()) pathC++;
                else out_learnt.push(q);
            }
        }
        while (!seen[var(trail[index--])]);
        p     = trail[index+1];
        confl = reason(var(p));
        seen[var(p)] = 0;
        pathC--;

    }
    while (pathC > 0);
    out_learnt[0] = ~p;

    int i, j;
    out_learnt.copyTo(analyze_toclear);
    if (ccmin_mode == 2){
        for (i = j = 1; i < out_learnt.size(); i++)
            if (reason(var(out_learnt[i])) == CRef_Undef || !litRedundant(out_learnt[i]))
                out_learnt[j++] = out_learnt[i];
        
    }
    else if (ccmin_mode == 1){
        for (i = j = 1; i < out_learnt.size(); i++){
            Var x = var(out_learnt[i]);

            if (reason(x) == CRef_Undef)
                out_learnt[j++] = out_learnt[i];
            else{
                Clause& c = ca[reason(var(out_learnt[i]))];
                for (int k = 1; k < c.size(); k++)
                    if (!seen[var(c[k])] && level(var(c[k])) > 0){
                        out_learnt[j++] = out_learnt[i];
                        break; 
                    }
            }
        }
    }
    else i = j = out_learnt.size();

    max_literals += out_learnt.size();
    out_learnt.shrink(i - j);
    tot_literals += out_learnt.size();

    if (out_learnt.size() == 1) out_btlevel = 0;
    else{
        int max_i = 1;
        for (int i = 2; i < out_learnt.size(); i++)
            if (level(var(out_learnt[i])) > level(var(out_learnt[max_i]))) max_i = i;
        Lit p             = out_learnt[max_i];
        out_learnt[max_i] = out_learnt[1];
        out_learnt[1]     = p;
        out_btlevel       = level(var(p));
    }

    for (int j = 0; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0;    // ('seen[]' is now cleared)
}


// Check if 'p' can be removed from a conflict clause.
bool Solver::litRedundant(Lit p){
    enum { seen_undef = 0, seen_source = 1, seen_removable = 2, seen_failed = 3 };
    assert(seen[var(p)] == seen_undef || seen[var(p)] == seen_source);
    assert(reason(var(p)) != CRef_Undef);

    Clause* c = &ca[reason(var(p))];
    vec<ShrinkStackElem>& stack = analyze_stack;
    stack.clear();

    for (uint32_t i = 1; ; i++){
        if (i < (uint32_t)c->size()){
            Lit l = (*c)[i];
            if (level(var(l)) == 0 || seen[var(l)] == seen_source || seen[var(l)] == seen_removable){
                continue; 
            }
            if (reason(var(l)) == CRef_Undef || seen[var(l)] == seen_failed){
                stack.push(ShrinkStackElem(0, p));
                for (int i = 0; i < stack.size(); i++)
                    if (seen[var(stack[i].l)] == seen_undef){
                        seen[var(stack[i].l)] = seen_failed;
                        analyze_toclear.push(stack[i].l);
                    }
                    
                return false;
            }
            stack.push(ShrinkStackElem(i, p));
            i  = 0;
            p  = l;
            c  = &ca[reason(var(p))];
        }
        else{
            if (seen[var(p)] == seen_undef){
                seen[var(p)] = seen_removable;
                analyze_toclear.push(p);
            }
            if (stack.size() == 0) break;
            i  = stack.last().i;
            p  = stack.last().l;
            c  = &ca[reason(var(p))];

            stack.pop();
        }
    }
    return true;
}


/*_________________________________________________________________________________________________
|
|  analyzeFinal : (p : Lit)  ->  [void]
|  
|  Description:
|    Specialized analysis procedure to express the final conflict in terms of assumptions.
|    Calculates the (possibly empty) set of assumptions that led to the assignment of 'p', and
|    stores the result in 'out_conflict'.
|________________________________________________________________________________________________@*/


void Solver::analyzeFinal(Lit p, LSet& out_conflict){
    out_conflict.clear();
    out_conflict.insert(p);

    if (decisionLevel() == 0) return;

    seen[var(p)] = 1;

    for (int i = trail.size()-1; i >= trail_lim[0]; i--){
        Var x = var(trail[i]);
        if (seen[x]){
            if (reason(x) == CRef_Undef){
                assert(level(x) > 0);
                out_conflict.insert(~trail[i]);
            }
            else{
                Clause& c = ca[reason(x)];
                for (int j = 1; j < c.size(); j++)
                    if (level(var(c[j])) > 0)
                        seen[var(c[j])] = 1;
            }
            seen[x] = 0;
        }
    }
    seen[var(p)] = 0;
}


void Solver::uncheckedEnqueue(Lit p, CRef from){
    assert(value(p) == l_Undef);
    assigns[var(p)] = lbool(!sign(p));
    vardata[var(p)] = mkVarData(from, decisionLevel());
    trail.push_(p);
}


/*_________________________________________________________________________________________________
|
|  propagate : [void]  ->  [Clause*]
|  
|  Description:
|    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
|    otherwise CRef_Undef.
|  
|    Post-conditions:
|      * the propagation queue is empty, even if there was a conflict.
|________________________________________________________________________________________________@*/

CRef Solver::propagate(){
    CRef    confl     = CRef_Undef;
    int     num_props = 0;

    while (qhead < trail.size()){
        Lit            p   = trail[qhead++];    
        vec<Watcher>&  ws  = watches.lookup(p);
        Watcher        *i, *j, *end;
        num_props++;
        for (i = j = (Watcher*)ws, end = i + ws.size(); i != end;){
            Lit blocker = i->blocker;
            if (value(blocker) == l_True){
                *j++ = *i++; 
                continue; 
            }
            CRef     cr        = i->cref;
            Clause&  c         = ca[cr];
            Lit      false_lit = ~p;
            if (c[0] == false_lit) c[0] = c[1], c[1] = false_lit;
            assert(c[1] == false_lit);
            i++;
            Lit     first = c[0];
            Watcher w     = Watcher(cr, first);
            if (first != blocker && value(first) == l_True){
                *j++ = w; continue; 
            }

            for (int k = 2; k < c.size(); k++){
                if (value(c[k]) != l_False){
                    c[1] = c[k]; c[k] = false_lit;
                    watches[~c[1]].push(w);
                    goto NextClause; 
                }
            }

            *j++ = w;
            if (value(first) == l_False){
                confl = cr;
                qhead = trail.size();
                while (i < end) *j++ = *i++;
            }
            else uncheckedEnqueue(first, cr);
            NextClause:;
        }
        ws.shrink(i - j);
    }
    propagations += num_props;
    simpDB_props -= num_props;
    return confl;
}


/*_________________________________________________________________________________________________
|
|  reduceDB : ()  ->  [void]
|  
|  Description:
|    Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
|    clauses are clauses that are reason to some assignment. Binary clauses are never removed.
|________________________________________________________________________________________________@*/

struct reduceDB_lt { 
    ClauseAllocator& ca;
    reduceDB_lt(ClauseAllocator& ca_) : ca(ca_) {}
    bool operator () (CRef x, CRef y) { 
        return ca[x].size() > 2 && (ca[y].size() == 2 || ca[x].activity() < ca[y].activity()); 
    } 
};


void Solver::reduceDB(){
    int     i, j;
    double  extra_lim = cla_inc / learnts.size(); 
    sort(learnts, reduceDB_lt(ca));
    for (i = j = 0; i < learnts.size(); i++){
        Clause& c = ca[learnts[i]];
        if (c.size() > 2 && !locked(c) && (i < learnts.size() / 2 || c.activity() < extra_lim))
            removeClause(learnts[i]);
        else
            learnts[j++] = learnts[i];
    }
    learnts.shrink(i - j);
    checkGarbage();
}


void Solver::removeSatisfied(vec<CRef>& cs){
    int i, j;
    for (i = j = 0; i < cs.size(); i++){
        Clause& c = ca[cs[i]];
        if (satisfied(c)) removeClause(cs[i]);
        else{
            assert(value(c[0]) == l_Undef && value(c[1]) == l_Undef);
            for (int k = 2; k < c.size(); k++){
                if (value(c[k]) == l_False){
                    c[k--] = c[c.size()-1];
                    c.pop();
                }
            }
            cs[j++] = cs[i];
        }
    }
    cs.shrink(i - j);
}


void Solver::rebuildOrderHeap(){
    vec<Var> vs;
    for (Var v = 0; v < nVars(); v++){
        if (decision[v] && value(v) == l_Undef)
            vs.push(v);
    }
    order_heap.build(vs);
}

Lit Solver::fetchFirstClauseLiterals(int idx){
    return ca[clauses[0]][idx];
}


/*_________________________________________________________________________________________________
|
|  simplify : [void]  ->  [bool]
|  
|  Description:
|    Simplify the clause database according to the current top-level assigment. Currently, the only
|    thing done here is the removal of satisfied clauses, but more things can be put here.
|________________________________________________________________________________________________@*/

bool Solver::simplify(){
    assert(decisionLevel() == 0);
    if (!ok || propagate() != CRef_Undef) return ok = false;
    if (nAssigns() == simpDB_assigns || (simpDB_props > 0)) return true;
    removeSatisfied(learnts);
    if (remove_satisfied){     
        removeSatisfied(clauses);

        // TODO: what todo in if 'remove_satisfied' is false?
        // Remove all released variables from the trail:
        for (int i = 0; i < released_vars.size(); i++){
            assert(seen[released_vars[i]] == 0);
            seen[released_vars[i]] = 1;
        }

        int i, j;
        for (i = j = 0; i < trail.size(); i++)
            if (seen[var(trail[i])] == 0) trail[j++] = trail[i];
        trail.shrink(i - j);
        qhead = trail.size();

        for (int i = 0; i < released_vars.size(); i++) seen[released_vars[i]] = 0;
        append(released_vars, free_vars);
        released_vars.clear();
    }
    checkGarbage();
    rebuildOrderHeap();

    simpDB_assigns = nAssigns();
    simpDB_props   = clauses_literals + learnts_literals;   
    return true;
}


/*_________________________________________________________________________________________________
|
|  search : (nof_conflicts : int) (params : const SearchParams&)  ->  [lbool]
|  
|  Description:
|    Search for a model the specified number of conflicts. 
|    NOTE! Use negative value for 'nof_conflicts' indicate infinity.
|  
|  Output:
|    'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
|    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
|    if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
|________________________________________________________________________________________________@*/

lbool Solver::search(int nof_conflicts){
    assert(ok);
    int         backtrack_level;
    int         conflictC = 0;
    vec<Lit>    learnt_clause;
    starts++;

    for (;;){
        if (vizFlag && waitingThreads) sem_wait(&calculationDone);
        CRef confl = propagate();
        if (vizFlag) sem_post(&propagationDone);
        if (confl != CRef_Undef){
            conflicts++; conflictC++;
            if (decisionLevel() == 0) return l_False;
            learnt_clause.clear();
            analyze(confl, learnt_clause, backtrack_level);
            cancelUntil(backtrack_level);
            if (learnt_clause.size() == 1) uncheckedEnqueue(learnt_clause[0]);
            else{
                CRef cr = ca.alloc(learnt_clause,true);
                learnts.push(cr);
                attachClause(cr);
                claBumpActivity(ca[cr]);
                uncheckedEnqueue(learnt_clause[0],cr);
            }
            varDecayActivity();
            claDecayActivity();
            if (--learntsize_adjust_cnt == 0){
                learntsize_adjust_confl *= learntsize_adjust_inc;
                learntsize_adjust_cnt    = (int)learntsize_adjust_confl;
                max_learnts             *= learntsize_inc;
                if (verbosity >= 1){
                    if (!vizFlag){
                        printf("| %9d | %7d %8d %8d | %8d %8d %6.0f | %6.3f %% |\n", 
                           (int)conflicts, 
                           (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]), nClauses(), (int)clauses_literals, 
                           (int)max_learnts, nLearnts(), (double)learnts_literals/nLearnts(), progressEstimate()*100);
                    }
                    else{
                        fprintf(logFile,"| %9d | %7d %8d %8d | %8d %8d %6.0f | %6.3f %% |\n", 
                           (int)conflicts, 
                           (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]), nClauses(), (int)clauses_literals, 
                           (int)max_learnts, nLearnts(), (double)learnts_literals/nLearnts(), progressEstimate()*100);
                        fflush(logFile);
                    }
                }
            }

        }
        else{
            if ((nof_conflicts >= 0 && conflictC >= nof_conflicts) || !withinBudget()){
                progress_estimate = progressEstimate();
                cancelUntil(0);
                return l_Undef; 
            }

            if (decisionLevel() == 0 && !simplify()) return l_False;
            if (learnts.size()-nAssigns() >= max_learnts) reduceDB();

            Lit next = lit_Undef;
            while (decisionLevel() < assumptions.size()){
                Lit p = assumptions[decisionLevel()];
                if (value(p) == l_True){
                    newDecisionLevel();
                }
                else if (value(p) == l_False){
                    analyzeFinal(~p, conflict);
                    return l_False;
                }
                else{
                    next = p;
                    break;
                }
            }

            if (next == lit_Undef){
                decisions++;
                next = pickBranchLit();
                if (next == lit_Undef) return l_True;
                averageActivity += activity[var(next)];
            }

            newDecisionLevel();
            uncheckedEnqueue(next);
        }
    }
}


double Solver::progressEstimate() const{
    double  progress = 0;
    double  F = 1.0 / nVars();
    for (int i = 0; i <= decisionLevel(); i++){
        int beg = i == 0 ? 0 : trail_lim[i - 1];
        int end = i == decisionLevel() ? trail.size() : trail_lim[i];
        progress += pow(F, i) * (end - beg);
    }
    return progress / nVars();
}

/*
  Finite subsequences of the Luby-sequence:

  0: 1
  1: 1 1 2
  2: 1 1 2 1 1 2 4
  3: 1 1 2 1 1 2 4 1 1 2 1 1 2 4 8
  ...
*/

static double luby(double y, int x){

    // Find the finite subsequence that contains index 'x', and the
    // size of that subsequence:
    int size, seq;
    for (size = 1, seq = 0; size < x+1; seq++, size = 2*size+1);

    while (size-1 != x){
        size = (size-1)>>1;
        seq--;
        x = x % size;
    }

    return pow(y, seq);
}

// NOTE: assumptions passed in member-variable 'assumptions'.
lbool Solver::solve_(){
    model.clear();
    conflict.clear();
    if (!ok) return l_False;
    solves++;
    max_learnts = nClauses() * learntsize_factor;
    if (max_learnts < min_learnts_lim) max_learnts = min_learnts_lim;

    learntsize_adjust_confl   = learntsize_adjust_start_confl;
    learntsize_adjust_cnt     = (int)learntsize_adjust_confl;
    lbool   status            = l_Undef;

    if (verbosity >= 1){
        if (!vizFlag){
            printf("============================[ Search Statistics ]==============================\n");
            printf("| Conflicts |          ORIGINAL         |          LEARNT          | Progress |\n");
            printf("|           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |\n");
            printf("===============================================================================\n");
        }
        else{
            fprintf(logFile,"============================[ Search Statistics ]==============================\n");
            fprintf(logFile,"| Conflicts |          ORIGINAL         |          LEARNT          | Progress |\n");
            fprintf(logFile,"|           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |\n");
            fprintf(logFile,"===============================================================================\n");
            fflush(logFile);
        }
    }

    if (vizFlag) {for (int i = 0; i < nVars();i++) seenx.insert(i,false);}
    while (status == l_Undef){
        double rest_base = luby_restart ? luby(restart_inc, curr_restarts) : pow(restart_inc, curr_restarts);
        status = search(rest_base * restart_first);
        if (!withinBudget()) break;
        curr_restarts++;
    }

    if (verbosity >= 1){
        if (!vizFlag) printf("===============================================================================\n");
        else {
            fprintf(logFile,"===============================================================================\n");
            fflush(logFile);
        }
    }


    if (status == l_True){
        model.growTo(nVars());
        for (int i = 0; i < nVars(); i++) model[i] = value(i);
    }
    else if (status == l_False && conflict.size() == 0) ok = false;

    cancelUntil(0);
    return status;
}

bool Solver::implies(const vec<Lit>& assumps, vec<Lit>& out){
    trail_lim.push(trail.size());
    for (int i = 0; i < assumps.size(); i++){
        Lit a = assumps[i];

        if (value(a) == l_False){
            cancelUntil(0);
            return false;
        }
        else if (value(a) == l_Undef) uncheckedEnqueue(a);
    }

    unsigned trail_before = trail.size();
    bool     ret          = true;
    if (propagate() == CRef_Undef){
        out.clear();
        for (int j = trail_before; j < trail.size(); j++)
            out.push(trail[j]);
    }else
        ret = false;
    
    cancelUntil(0);
    return ret;
}

//=================================================================================================
// Writing CNF to DIMACS:
// 
// FIXME: this needs to be rewritten completely.

static Var mapVar(Var x, vec<Var>& map, Var& max){
    if (map.size() <= x || map[x] == -1){
        map.growTo(x+1, -1);
        map[x] = max++;
    }
    return map[x];
}


void Solver::toDimacs(FILE* f, Clause& c, vec<Var>& map, Var& max)
{
    if (satisfied(c)) return;

    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) != l_False)
            fprintf(f, "%s%d ", sign(c[i]) ? "-" : "", mapVar(var(c[i]), map, max)+1);
    fprintf(f, "0\n");
}


void Solver::toDimacs(const char *file, const vec<Lit>& assumps){
    FILE* f = fopen(file, "wr");
    if (f == NULL) fprintf(stderr, "could not open file %s\n", file), exit(1);
    toDimacs(f, assumps);
    fclose(f);
}


void Solver::toDimacsLearnt(const char *file){
    if (file == NULL) {
        fprintf(stderr, "could not open file \n");
        return;
    }
    char c[100]; 
    strcpy(c, file);
    char num[60];
    sprintf(num,"%d",iter);
    strcat(c, num);
    char* x = ".cnf";
    strcat(c,x);
    FILE* f = fopen(c,"wr");
    for (int i = 0; i < clauses.size();i++){
        CRef& c = clauses[i];
        Clause& clause = ca[c];
        for (int j = 0; j < clause.size();j++) fprintf(f,"%s%d ",sign(clause[j])?"-":"",1+var(clause[j]));
        fprintf(f, "0\n");
    }
    iter++;
}

void Solver::toDimacs(FILE* f, const vec<Lit>& assumps){

    if (!ok){
        fprintf(f, "p cnf 1 2\n1 0\n-1 0\n");
        return; 
    }
    vec<Var> map; Var max = 0;
    int cnt = 0;
    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]]))
            cnt++;
        
    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]])){
            Clause& c = ca[clauses[i]];
            for (int j = 0; j < c.size(); j++)
                if (value(c[j]) != l_False) mapVar(var(c[j]), map, max);
        }

    cnt += assumps.size();

    fprintf(f, "p cnf %d %d\n", max, cnt);

    for (int i = 0; i < assumps.size(); i++){
        assert(value(assumps[i]) != l_False);
        fprintf(f, "%s%d 0\n", sign(assumps[i]) ? "-" : "", mapVar(var(assumps[i]), map, max)+1);
    }

    for (int i = 0; i < clauses.size(); i++)
        toDimacs(f, ca[clauses[i]], map, max);

    if (verbosity > 0)
        printf("Wrote DIMACS with %d variables and %d clauses.\n", max, cnt);
}


void Solver::printStats() const{
    double cpu_time = cpuTime();
    double mem_used = memUsedPeak();
    printf("restarts              : %"PRIu64"\n", starts);
    printf("conflicts             : %-12"PRIu64"   (%.0f /sec)\n", conflicts   , conflicts   /cpu_time);
    printf("decisions             : %-12"PRIu64"   (%4.2f %% random) (%.0f /sec)\n", decisions, (float)rnd_decisions*100 / (float)decisions, decisions   /cpu_time);
    printf("propagations          : %-12"PRIu64"   (%.0f /sec)\n", propagations, propagations/cpu_time);
    printf("conflict literals     : %-12"PRIu64"   (%4.2f %% deleted)\n", tot_literals, (max_literals - tot_literals)*100 / (double)max_literals);
    if (mem_used != 0) printf("Memory used           : %.2f MB\n", mem_used);
    printf("CPU time              : %g s\n", cpu_time);
}


//=================================================================================================
// Garbage Collection methods:

void Solver::relocAll(ClauseAllocator& to)
{
    // All watchers:
    //
    watches.cleanAll();
    for (int v = 0; v < nVars(); v++)
        for (int s = 0; s < 2; s++){
            Lit p = mkLit(v, s);
            vec<Watcher>& ws = watches[p];
            for (int j = 0; j < ws.size(); j++)
                ca.reloc(ws[j].cref, to);
        }

    // All reasons:
    //
    for (int i = 0; i < trail.size(); i++){
        Var v = var(trail[i]);
        if (reason(v) != CRef_Undef && (ca[reason(v)].reloced() || locked(ca[reason(v)]))){
            assert(!isRemoved(reason(v)));
            ca.reloc(vardata[v].reason, to);
        }
    }

    // All learnt:
    //
    int i, j;
    for (i = j = 0; i < learnts.size(); i++)
        if (!isRemoved(learnts[i])){
            ca.reloc(learnts[i], to);
            learnts[j++] = learnts[i];
        }
    learnts.shrink(i - j);

    // All original:
    //
    for (i = j = 0; i < clauses.size(); i++)
        if (!isRemoved(clauses[i])){
            ca.reloc(clauses[i], to);
            clauses[j++] = clauses[i];
        }
    clauses.shrink(i - j);
}

void Solver::bindFirstClauseVariables(vec<Lit> &lit){
    for (int i = 0; i < lit.size(); i++)  firstClauseVariables.insert(var(lit[i]),true);
}

void Solver::garbageCollect(){
    ClauseAllocator to(ca.size() - ca.wasted()); 
    relocAll(to);
    if (verbosity >= 2)
        printf("|  Garbage collection:   %12d bytes => %12d bytes             |\n", ca.size()*ClauseAllocator::Unit_Size, to.size()*ClauseAllocator::Unit_Size);
    to.moveTo(ca);
}
