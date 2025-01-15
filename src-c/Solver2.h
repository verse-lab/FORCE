#ifndef SOLVER_H
#define SOLVER_H

#include "basics.h"
#include "preprocessing.h"
#include "Helper.h"
#include "InvEncoder.h"
#include "StringProcessor.h"
#include <clingo.hh>

#define COLUMN_COMPRESSION_THRESHOLD 70 //TODO!
#define BOUND_MAX_OR_COLUMN_THREDHOLD 75
#define INV_HOLD_ON_CSV -1
#define DISJ_STORE_CUTOFF_SIZE 4
#define OPTIONAL_QUANTIFIED_VARIABLE_CUTOFF_SIZE 5

#define O2O 1
#define DEBUG 0
class Solver;

class FO_Propagator : public Clingo::Propagator
{
    bool dnf;
    map<int, pair<int, int>> lit_to_aspoutno;
    map<int, int> lit_to_aspvar;
    map<int, int> lit_to_aspexists;
    map<int,set<int>> one2one;
    map<qalter_t, set<inv_lit_t>> checked;
    Solver &csv_reader;
    Config &config;
    map<int, string> &var_to_type;
    bool check_assignment(const Clingo::Assignment &assignment);

public:
    FO_Propagator(Solver &reader, Config &c, bool b)
        : csv_reader(reader), config(c), lit_to_aspoutno(), lit_to_aspvar(), var_to_type(*(new map<int, string>())), dnf(b), one2one(), checked() {};
    void assign_var_to_type(map<int, string> &v2t) { var_to_type = v2t; }
    void init(Clingo::PropagateInit &init) override;
    void check(Clingo::PropagateControl &control) override;
    void assign_one2one(map<int,set<int>> &o2o) { 
		one2one = o2o; 
	}
};

class Solver
{
private:
	// not used for ours, but for further Houdini
	map<vars_t, map<vector<bool>, vector<vector<int>>>> self_mapped_predicates_dict;  // second key is is_ordered_unique
	map<vars_t, map<pair<int,int>, map<vector<vector<int>>, vector<int>>>> self_mapped_new_predicates_each_mapping;
	void find_strengthen_safety_invs();

	void precompute_vars_self_mapping(const vars_t& vars, const qalter_t& qalter);
	void calc_self_mapped_predicates_each_mapping();

	map<inst_t, DataMatrix> inst_data_mat_dict;
	map<vector<int>, map<inst_t, DataMatrix>> inst_data_mat_dict_each_leading_forall;  // key vector<int> is the list of variable numbers for each leading forall type
	map<inst_t, map<string, int>> inst_p_to_idx_dict;

	
	map<vars_t, vector<vector<qalter_t>>> vars_qalter_exists_number;
	vector<vector<vector<vector<int>>>> n_into_k;
	bool column_compression_on, py_column_compression_detected;
	void check_config_well_formed() const;
	void calc_predicates_dict();
	void calc_varinp_and_ptoidx();
	void calc_single_type_mappings();
	void calc_single_type_self_mappings();
	void calc_column_indices_dict();
	void calc_lowhighvars_column_indices_dict();
	void calc_inst_data_mat_dict_each_leading_forall();
	void precompute_vars_self_mapping_bulk();
	void reduce_predicates(vector<string>& old_predicates, vector<string>& new_predicates, int type_index, int var_index_to_remove) const;
	void calc_vars_traversal_order();
	void calc_vars_qalters_exists_number();
	

	bool check_if_qfree_dnf_formula_holds_on_data_line(const int* data_line, const vector<vector<int>>& candidate_inv_as_data_indices) const;
	
	bool flyvy;
	Clingo::Control clause;
    Clingo::Control dnf;
	map<vars_t, vector<int>> pred_idx;
	int current_grounded{0};
    int lit_num{0};
    int cube_num{0};
	map<int, string> var_to_type;
	tuple<int, int, vars_t> clause_setting;
    vector<int> dnf_setting; 
    bool init_dnf;
	map<int,set<int>> o2o;
	FO_Propagator clause_propagator;
    FO_Propagator dnf_propagator;

	Timer solve_timer;
    Timer ground_timer;
    Timer other_timer;

	void prepare_clingo(Clingo::StringSpan args);
	void clause_search();
	void dnf_search();
	void model_to_formula(const Clingo::SymbolVector &formula, vars_t &vars, vector<pair<Clingo::Symbol, Clingo::Symbol>> &inv, vars_t &exist_vars);
	void model_to_clause(const Clingo::SymbolVector &formula, vars_t &vars, vector<pair<Clingo::Symbol, Clingo::Symbol>> &inv, vars_t &exist_vars);
	void ground_invs_clause(const vector<vector<pair<Clingo::Symbol, Clingo::Symbol>>> &invs, const vector<vars_t> &exists_vars, const vector<vars_t> &used_vars, bool final_clause);
	void ground_dnf(const vector<vector<pair<Clingo::Symbol, Clingo::Symbol>>> &invs, const vector<vars_t> &exists_vars);
	void set_clause_setting(int num_exists, int len, vars_t vars);
	void set_dnf_setting(vector<int>& formula_size);
	void from_csv_to_predicates(vector<string> &predicates);



protected:  // visible to derived class InvRefiner
	int num_types;
	string problem_name;
	int formula_size_increase_times, template_increase_times;
	string input_ivy_file, default_output_ivy_inv_file;
	StringProcessor processor;
	Helper helper;
	InvEncoder encoder;
	Config config;
	vars_t template_sizes;
	vector<vars_t> vars_traversal_order;//TODO: what is the one_to_one_exists?
	map<vars_t, vector<string>> predicates_dict;
	bool cutoff;
	
	// nested array, dimensions are 1) type index, 2) number of quantified variables of this type, 3) instance size at this type, 4) unique/ordered
	// the four indices above jointy point to a list of mappings, {ID1 -> id2, ID2 -> id3} can be one mapping, mappings are sorted by alphabetical order
	vector<vector<vector<map<bool, vector<map<string, string>>>>>> single_type_mappings;
	vector<vector<vector<vector<vector<int>>>>> single_type_self_mappings;
	// a nested dict, the keys are 1) quantified variables, 2) instance size, 3) unique/ordered or not for each type, 4) index of single_type_mapping for each type and respective (1)(2)(3)
	map<vars_t, map<inst_t, map<vector<bool>, map<vector<int>, vector<int>>>>> column_indices_dict;
	// a nested dict, the keys are 1) higher quantified variables, 2) lower (i.e., subset) quantified variables, the value is the index of each higher predicate in the lower predicate list (-1 if not exists)
	map<vars_t, map<vars_t, map<vector<bool>, vector<vector<int>>>>> lowhighvars_column_indices_dict;
	map<vars_t, map<string, vector<int>>> var_in_p_dict;
	map<vars_t, map<string, int>> p_to_idx_dict;
	// invs_dict: key: subtemplate; value: checked invariants
	map<vars_t, map<qalter_t, inv_set_t>> invs_dict;
	vector<tuple<vars_t, qalter_t, string>> solver_more_invs;
	int check_if_inv_on_csv(const vars_t& vars, const qalter_t& qalter, const inst_t& inst, const inv_t& candidate_inv, const DataMatrix& data_mat, const map<vector<int>, vector<int>>& one_column_indices_dict) const;
	void add_permuted_candidates(inv_set_t& formula_set, const vars_t& vars, const vector<bool>& is_unique_ordered, const inv_t& candidate_inv);
	void calc_deuniqued_invs(const vars_t& vars, const qalter_t& qalter, vector<inv_set_t>& deuniqued_invs); //TODO: by ASP or?

public:
	bool check_invariant(const vars_t& vars, const qalter_t& qalter, const inv_t &candidate_inv); //opt: use the queue to parallelise

	map<inst_t, vector<string>> inst_predicates_dict;
	int get_pred_idx(const vars_t& vars, const int& idx);
	Solver(string problem, int template_increase, int num_attempt, bool is_forall_only, bool cutoff, bool fix);
	void early_preparations();
	void auto_solve();
	void encode_and_output(const string& outfile, map<int, tuple<vars_t, qalter_t, inv_t>>& id_to_inv, const vector<tuple<vars_t, qalter_t, string>>& more_invs = {});
};

#endif
