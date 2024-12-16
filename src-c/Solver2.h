#ifndef SOLVER_H
#define SOLVER_H

#include "basics.h"
#include "preprocessing.h"
#include "Helper.h"
#include "InvEncoder.h"
#include "StringProcessor.h"

#define COLUMN_COMPRESSION_THRESHOLD 50
#define BOUND_MAX_OR_COLUMN_THREDHOLD 75
#define INV_HOLD_ON_CSV -1
#define MAX_POS_EXISTS 3 //TODO!
#define DISJ_STORE_CUTOFF_SIZE 4
#define OPTIONAL_QUANTIFIED_VARIABLE_CUTOFF_SIZE 5

class Solver
{
private:
	// not used for ours, but for further Houdini
	map<vars_t, map<vector<bool>, vector<vector<int>>>> self_mapped_predicates_dict;  // second key is is_ordered_unique
	map<vars_t, map<pair<int,int>, map<vector<vector<int>>, vector<int>>>> self_mapped_new_predicates_each_mapping;

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
	void enumerate_dnf(const vars_t& vars, const qalter_t& qalter, inv_set_t& inv_results);

	bool check_if_qfree_dnf_formula_holds_on_data_line(const int* data_line, const vector<vector<int>>& candidate_inv_as_data_indices) const;


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
	vector<vars_t> vars_traversal_order;
	map<vars_t, vector<string>> predicates_dict;
	map<inst_t, vector<string>> inst_predicates_dict;
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
	int check_if_inv_on_csv(const vars_t& vars, const qalter_t& qalter, const inst_t& inst, const inv_t& candidate_inv, const DataMatrix& data_mat, const map<vector<int>, vector<int>>& one_column_indices_dict) const;
	void add_permuted_candidates(inv_set_t& formula_set, const vars_t& vars, const vector<bool>& is_unique_ordered, const inv_t& candidate_inv);
	void calc_deuniqued_invs(const vars_t& vars, const qalter_t& qalter, vector<inv_set_t>& deuniqued_invs); //TODO: by ASP or?

public:
	Solver(string problem, int template_increase, int num_attempt, bool is_forall_only);
	void early_preparations();
	void auto_solve();
	void encode_and_output(const string& outfile, map<int, tuple<vars_t, qalter_t, inv_t>>& id_to_inv, const vector<tuple<vars_t, qalter_t, string>>& more_invs = {});
};

#endif
