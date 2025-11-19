/*****************************************************************************************[Main.cc]
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

#include <errno.h>
#include <zlib.h>

#include "minisat/utils/System.h"
#include "minisat/utils/ParseUtils.h"
#include "minisat/utils/Options.h"
#include "minisat/core/Dimacs.h"
#include "minisat/core/Solver.h"
#include <thread>
#include <chrono>
#include <atomic>
#include "matplotlibcpp.h"
#include "semaphore.h"
#include "json.hpp"
#include <filesystem>
#include <fstream>

using json = nlohmann::json;
using namespace Minisat;
using namespace std;

namespace plt = matplotlibcpp;

//=================================================================================================


static Solver* solver;
// Terminate by notifying the solver and back out gracefully. This is mainly to have a test-case
// for this feature of the Solver as it may take longer than an immediate call to '_exit()'.
static void SIGINT_interrupt(int) { solver->interrupt(); }

static void SIGINT_exit(int) {
    printf("\n"); 
    printf("*** INTERRUPTED ***\n");
    if (solver->verbosity > 0){
        solver->printStats();
        printf("\n"); printf("*** INTERRUPTED ***\n"); 
    }
    _exit(1); 
}


std::atomic<bool> stopFlag(false);
std::vector<Solver*> solvers;
sem_t pauseSem;


/*void analyzeAverageProportions(){
    while (!stopFlag){
        plt::clf();
        for (int i = 0; i < solvers.size(); i++){
            if (!solvers[i]->solved){
                solvers[i]->averageProportion.push_back((double)solvers[i]->sumPercentage/solvers[i]->globalLearnts);
                if (solvers[i]->timestamps.empty()) solvers[i]->timestamps.push_back(1);
                else solvers[i]->timestamps.push_back((solvers[i]->timestamps).back()+1);
            }
            const std::map<std::string,std::string> opts = {{"label",solvers[i]->name}};
            plt::plot(solvers[i]->timestamps,solvers[i]->averageProportion,opts);
            plt::legend({{"loc", "upper left"}});
        }
        plt::title(" Graph For comparison ");
        plt::pause(0.01);
        std::this_thread::sleep_for(std::chrono::seconds(2));
    }
    plt::clf();
    for (int i = 0; i < solvers.size();i++) plt::plot(solvers[i]->timestamps,solvers[i]->averageProportion);
    plt::title("comparative_graph");
    plt::save("final_graph");
    plt::close;
    sem_post(&pauseSem1);
}

void doPLotting(){
    plt::figure_size(1200, 800);
    while (!stopFlag){
        plt::clf();
        // ----- SUBPLOT 1 -----
        plt::subplot(1,2,1);
        for (int i = 0; i < solvers.size(); i++){
            if (!solvers[i]->solved){
                if (solvers[i]->timestamps.empty()) solvers[i]->timestamps.push_back(1);
                else solvers[i]->timestamps.push_back(solvers[i]->timestamps.back() + 1);
                solvers[i]->unitProps.push_back(solvers[i]->unitPropagations);
                solvers[i]->averageProportion.push_back((double)solvers[i]->sumPercentage / solvers[i]->globalLearnts);
            }
            const std::map<std::string,std::string> opts = {{"label", solvers[i]->name}};
            plt::plot(solvers[i]->timestamps, solvers[i]->unitProps, opts);
        }
        plt::legend({{"loc", "upper left"}});

        // ----- SUBPLOT 2 -----
        plt::subplot(1,2,2);
        for (int i = 0; i < solvers.size(); i++){
            const std::map<std::string,std::string> opts = {{"label", solvers[i]->name}};
            plt::plot(solvers[i]->timestamps, solvers[i]->averageProportion, opts);
        }
        plt::legend({{"loc", "upper left"}});
        plt::pause(0.01);
        std::this_thread::sleep_for(std::chrono::seconds(2));
    }
    plt::clf();
    plt::subplot(1,2,1);
    for (auto &s : solvers) plt::plot(s->timestamps, s->unitProps);
    plt::subplot(1,2,2);
    for (auto &s : solvers) plt::plot(s->timestamps, s->averageProportion);
    plt::save("final_graph");
    plt::close();
    sem_post(&pauseSem);
}


void analyzeUnitProps(){
    while (!stopFlag){
        plt::clf();
        for (int i = 0; i < solvers.size(); i++){
            if (!solvers[i]->solved){
                solvers[i]->unitProps.push_back(solvers[i]->unitPropagations);
                if (solvers[i]->timestamps.empty()) solvers[i]->timestamps.push_back(1);
                else solvers[i]->timestamps.push_back((solvers[i]->timestamps).back()+1);
            }
            const std::map<std::string,std::string> opts = {{"label",solvers[i]->name}};
            plt::plot(solvers[i]->timestamps,solvers[i]->unitProps,opts);
            plt::legend({{"loc", "upper left"}});
        }
        plt::title(" Graph For comparison ");
        plt::pause(0.01);
        std::this_thread::sleep_for(std::chrono::seconds(2));
    }
    plt::clf();
    for (int i = 0; i < solvers.size();i++) plt::plot(solvers[i]->timestamps,solvers[i]->unitProps);
    plt::title("comparative_graph");
    plt::save("final_graph");
    plt::close;
    sem_post(&pauseSem);
}*/

struct bounded_metrics{
    std::string metricName;
    bool bounded;
    int upper_bound;
};

typedef struct bounded_metrics bounded_metric;
struct metrics{bool flags[11];};
vector<string> options = {"nDecisions","nUnitProps","nConflicts","clauseDatabaseSize","gcEvents","learnt_clause_count","restartEvents","avg_lbd","backjumpDistance","conflictDecisionLevel","avgTopKActivity"};
struct metrics metric;
uint32_t active_metrics;

bool createIfNotExists(string& dir){
    if (filesystem::exists(dir)){
        if (filesystem::is_directory(dir)) return true;
        else{
            cerr << "File with given name already exists exiting" << endl;
            return false;
        }
    }
    else{
        int code = mkdir(dir.c_str(),0777);
        return !code;
    }
}

void parseMetrics(json& configMetrics,bool& flag,string& option_name){
    if (configMetrics.contains(option_name)) {
        flag = configMetrics[option_name].get<bool>();
        active_metrics++;
    }
    else flag = false;
}

//easy statistics minisat already tracks them
inline void updateTimestamp(Solver* S){(!S->timestamps.size()) ? S->timestamps.push(1) : S->timestamps.push((S->timestamps).last()+1);}
inline void updateDecisions(Solver* S){if (metric.flags[0]) S->decisionVector.push(S->decisions);}
inline void updateUnitProps(Solver* S){if (metric.flags[1]) S->unitPropsVector.push(S->propagations);}
inline void updateConflictsCount(Solver* S){if (metric.flags[2]) S->conflictVector.push(S->conflicts);}
inline void updateClauseDBSize(Solver* S){if (metric.flags[3]) S->clauseDBVector.push(S->num_clauses + S->num_learnts);}
inline void updateGCEvents(Solver* S){if (metric.flags[4]) S->gcEventsVector.push(S->gcEvents);}
inline void updateLearntClauses(Solver* S){if (metric.flags[5]) S->learntClausesVector.push(S->num_learnts);}
inline void updateRestartEvents(Solver* S){if (metric.flags[6]) S->restartEventsVector.push(S->curr_restarts);}

//data accessors for different stats
inline const vec<double>& getDecisionVector(const Solver* S)    {return S->decisionVector;}
inline const vec<double>& getUnitPropVector(const Solver* S)    {return S->unitPropsVector;}
inline const vec<double>& getConflictVector(const Solver* S)    {return S->conflictVector;}
inline const vec<double>& getClauseDBVector(const Solver* S)    {return S->clauseDBVector;}
inline const vec<double>& getGCEventsVector(const Solver* S)    {return S->gcEventsVector;}
inline const vec<double>& getLearntClauseVector(const Solver* S){return S->learntClausesVector;}
inline const vec<double>& getRestartEventVector(const Solver* S){return S->restartEventsVector;}


//generalized vector for all functions
using dataAccessorFunction = const vec<double>& (*)(const Solver* S);
const vector<dataAccessorFunction> dataAccessor = {getDecisionVector,getUnitPropVector,getConflictVector,getClauseDBVector,getGCEventsVector,getLearntClauseVector,getRestartEventVector};

//custom statistics
void plotMetrics(string path){
    int cols = ceil(sqrt(active_metrics));
    int rows = ceil((double)active_metrics/cols);
    plt::figure_size(1200,800);
    while (!stopFlag){
        int idx = 1;
        plt::clf();
        for (int i = 0; i < solvers.size();i++){
            if (!solvers[i]->solved){
                updateTimestamp(solvers[i]);
                updateDecisions(solvers[i]);
                updateUnitProps(solvers[i]);
                updateConflictsCount(solvers[i]);
                updateGCEvents(solvers[i]);
                updateLearntClauses(solvers[i]);
                updateRestartEvents(solvers[i]);
            }
        }
        for (int metric_no = 0; metric_no < 7; metric_no++){
            if (metric.flags[metric_no]){
                plt::subplot(rows,cols,idx++);
                plt::title(options[metric_no]);
                for (int i = 0; i < solvers.size();i++) plt::plot(solvers[i]->timestamps,dataAccessor[metric_no](solvers[i]));
                plt::legend({{"loc", "upper left"}});
            }
        }
        plt::suptitle("SAT Metrics Visualizer");
        plt::pause(0.01);
        this_thread::sleep_for(std::chrono::seconds(2));
    }
    plt::clf();
    int idx = 1;
    for (int metric_no = 0; metric_no < 7; metric_no++){
        if (metric.flags[metric_no]){
            plt::subplot(rows,cols,idx++);
            plt::title(options[metric_no]);
            for (int i = 0; i < solvers.size();i++) plt::plot(solvers[i]->timestamps,dataAccessor[metric_no](solvers[i]));
            plt::legend({{"loc", "upper left"}});
        }
    }
    plt::title("Metric Comparison Graph");
    plt::save(path);
    plt::close;
    sem_post(&pauseSem);
}



int main(int argc, char** argv){
    try {
        vector<thread> threads;
        json config;
        ifstream file("config.json");
        sem_init(&pauseSem,false,0);

        if (!file.is_open()){
            cerr << "Unable to open input json file" << endl;
            _exit(404);
        }

        file >> config;

        int cpu_lim = (config.contains("cpu_lim")) ? config["cpu_lim"].get<int>():0;
        int mem_lim = (config.contains("mem_lim")) ? config["mem_lim"].get<int>():0;
        bool verbosity = (config.contains("verbosity") ? config["verbosity"].get<bool>():true);

        string logDirectory,outDirectory,graphDirectory,graphFile;

        logDirectory = (config.contains("output") && config["output"].contains("log_directory")) ? config["output"]["log_directory"] : "output" ;
        outDirectory = (config.contains("output") && config["output"].contains("result_directory")) ? config["output"]["result_directory"] : "output" ;
        graphDirectory = (config.contains("output") && config["output"].contains("graph_directory")) ? config["output"]["graph_directory"] : "output" ;
        graphFile  = (config.contains("output") && config["output"].contains("graph_file")) ? config["output"]["graph_file"] : "final_graph";

        bool f1 = createIfNotExists(logDirectory);
        bool f2 = createIfNotExists(outDirectory);
        bool f3 = createIfNotExists(graphDirectory);

        if (!f1 || !f2 || !f3){
            cerr << "Exiting visualizer! Fatal Error, Unable to create logDirectory/outputDirectory/graphDirectory" << endl;
            _exit(404);
        }

        assert(config.contains("metrics"));
        for (int i = 0; i < options.size();i++) parseMetrics(config["metrics"],metric.flags[i],options[i]);

        auto solverFunction = [&](Solver* S)->void{
            if (cpu_lim != 0) limitTime(cpu_lim);
            if (mem_lim != 0) limitMemory(mem_lim);
            if (!S->simplify()){
                printf("UNSATISFIABLE\n");
                exit(20);
            }
            vec<Lit> dummy;
            lbool ret = S -> solveLimited(dummy);
            printf(ret == l_True ? "SATISFIABLE\n" : ret == l_False ? "UNSATISFIABLE\n" : "INDETERMINATE\n");
            S -> solved = true;
        };

        if (!file.is_open()){
            cerr << " Error opening File " << std::endl;
            _exit(404);
        }


        for (auto &cnf : config["cnf_files"]){
            string path = cnf["path"];
            string default_log_file = path + "_stats.log";
            string logFile = ((cnf.contains("log_file"))?cnf["log_file"].get<string>():default_log_file);
            std::replace(default_log_file.begin(),default_log_file.end(),'\\','_');
            logFile = logDirectory + "/" + logFile;
            string default_output_file = path + "_result.cnf";
            std::replace(default_output_file.begin(),default_output_file.end(),'\\','_');
            string outputFile = ((cnf.contains("result_file"))?cnf["result_file"].get<string>():default_output_file);
            outputFile = outDirectory + "/" + outputFile;
            Solver* S = new Solver(logFile,outputFile);
            S->verbosity = true;
            gzFile in = gzopen(path.c_str(),"rb");
            if (in == NULL){
                printf("ERROR! Could not open file: %s\n",path);
                _exit(404);
            }
            parse_DIMACS(in, *S, false);
            gzclose(in);
            solvers.push_back(S);
            threads.emplace_back(solverFunction,S); 
        }

        std::string full_path = graphDirectory + graphFile;
        std::thread t1(plotMetrics,full_path);

        signal(SIGINT,[](int sig){
            stopFlag = true;
            for (auto it : solvers) it -> interrupt();
            sem_wait(&pauseSem);
            _exit(1);
        });

        for (int i = 0; i < threads.size();i++) threads[i].join();
        stopFlag = true;
        sem_wait(&pauseSem);
        for (auto S : solvers) delete S;
        printf(" All Simulations Over \n");
    } 
    catch (OutOfMemoryException&){
        printf("===============================================================================\n");
        printf("INDETERMINATE\n");
        exit(0);
    }
}
