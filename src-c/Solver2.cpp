#include "Solver2.h"

Solver::Solver(string problem, int template_increase, int num_attempt, bool is_forall_only) : processor(config), helper(config, processor), encoder(config, processor)
{
	problem_name = problem;
	template_increase_times = template_increase;
	formula_size_increase_times = num_attempt;
	string csv_file_base = "../traces/" + problem + "_" + std::to_string(template_increase) + "/";
	string config_file = "../configs/" + problem + "_" + std::to_string(template_increase) + ".txt";
	config.max_literal = 0;
	config.max_exists = 0;
	config.max_ored_clauses = 0;
	config.max_anded_literals = 0;
	config.max_pos_exists = MAX_POS_EXISTS;
	config.one_to_one_exists = false;
	config.hard = false;
	read_config(config_file, &config);
	// round-robin template increase
	if (is_forall_only)
	{
		config.max_ored_clauses = config.max_ored_clauses + formula_size_increase_times;
		config.max_literal = config.max_literal + formula_size_increase_times;
		config.max_anded_literals = 1;
		config.max_exists = 0;
	}
	else
	{
		config.max_literal = config.max_literal + (formula_size_increase_times + 3) / 4;
		config.max_ored_clauses = config.max_ored_clauses + (formula_size_increase_times + 2) / 4;
		config.max_anded_literals = config.max_anded_literals + (formula_size_increase_times + 1) / 4;
		config.max_exists = config.max_exists + formula_size_increase_times / 4;
	}
	cout << "current formula size: max-literal=" << config.max_literal << ", max-ored-clauses=" << config.max_ored_clauses << ", max-anded-literals=" << config.max_anded_literals << ", max-exists=" << config.max_exists << ", template-increase=" << template_increase << endl;
	num_types = config.type_order.size();
	processor.initialize();
	check_config_well_formed();
	for (const string& type_name : config.type_order)
	{
		template_sizes.push_back(config.template_vars_map[type_name].size());
	}
	for (const inst_t& curr_instance_size : config.instance_sizes)
	{
		string instance_size_str;
		for (int number : curr_instance_size)
		{
			instance_size_str += std::to_string(number) + "-";
		}
		instance_size_str.pop_back();
		string csv_file = csv_file_base + instance_size_str + ".csv";
		read_trace(csv_file, inst_predicates_dict[curr_instance_size], inst_data_mat_dict[curr_instance_size]);
		add_negation(inst_data_mat_dict[curr_instance_size]);
	}
	column_compression_on = false;
	py_column_compression_detected = false;
	input_ivy_file = "../protocols/" + problem + "/" + problem + ".ivy";
	default_output_ivy_inv_file = "../outputs/" + problem_name + "/" + problem_name + "_" + (is_forall_only ? "f" : "e") + std::to_string(template_increase) + "_inv" + ".ivy";
}

void Solver::check_config_well_formed() const
{
	assert(int(config.template_vars_map.size()) == num_types);
	assert(int(config.type_abbrs.size()) == num_types);
	for (const string& type_name : config.type_order)
	{
		assert(config.template_vars_map.find(type_name) != config.template_vars_map.end());
		assert(config.type_abbrs.find(type_name) != config.type_abbrs.end());
		const string& type_abbr = config.type_abbrs.at(type_name);
		const vector<string>& type_vars = config.template_vars_map.at(type_name);
		for (int i = 0; i < int(type_vars.size()); i++)
		{
			assert(type_vars[i] == type_abbr + std::to_string(i + 1));
		}
	}
}

void Solver::calc_predicates_dict()
{
	predicates_dict[template_sizes] = inst_predicates_dict[template_sizes];
	if (inst_predicates_dict[template_sizes].size() > COLUMN_COMPRESSION_THRESHOLD)
	{
		if (config.max_exists > 0)
		{
			column_compression_on = true;
			processor.column_compression(template_sizes, inst_predicates_dict.at(template_sizes), predicates_dict[template_sizes]);
		}
	}

	int total_num_predicates = predicates_dict[template_sizes].size();
	int num_optional_qauntified_variables = std::accumulate(template_sizes.begin(), template_sizes.end(), 0) - num_types;
	bool memory_explosion_expected = ((total_num_predicates > COLUMN_COMPRESSION_THRESHOLD) && (config.max_ored_clauses >= DISJ_STORE_CUTOFF_SIZE || num_optional_qauntified_variables >= OPTIONAL_QUANTIFIED_VARIABLE_CUTOFF_SIZE))
		|| ((total_num_predicates > COLUMN_COMPRESSION_THRESHOLD*3/4) && (config.max_ored_clauses > DISJ_STORE_CUTOFF_SIZE || num_optional_qauntified_variables > OPTIONAL_QUANTIFIED_VARIABLE_CUTOFF_SIZE));
	if (memory_explosion_expected)
	{
		cout << "Exiting for memory safety..." << endl;
		exit(-1);
	}
	if (predicates_dict.at(template_sizes).size() > BOUND_MAX_OR_COLUMN_THREDHOLD)
	{
		cout << "Too many predicates (" << predicates_dict.at(template_sizes).size() << ") that can appear in the invariants. Bounding initial max_ored_clauses to <=2." << endl;
		config.max_literal = min2(config.max_literal, 2);
	}

	for (int type_index = 0; type_index < num_types; type_index++)
	{
		const string& type_name = config.type_order[type_index];
		const vector<string>& curr_group = config.template_vars_map[type_name];
		map<vars_t, vector<string>> curr_predicates_dict = predicates_dict; // cannot reassign reference in C++
		for (int var_index = curr_group.size() - 1; var_index > 0; var_index--)
		{
			// TODO-long-term: support for one-to-one mapping
			map<vars_t, vector<string>> new_predicates_dict;
			for (map<vars_t, vector<string>>::iterator it = curr_predicates_dict.begin(); it != curr_predicates_dict.end(); it++)
			{
				const vars_t& vars = it->first;
				vector<string>& predicates = it->second;
				vector<string> new_predicates;
				reduce_predicates(predicates, new_predicates, type_index, var_index);
				vars_t new_vars = vars;
				new_vars[type_index]--;
				new_predicates_dict[new_vars] = new_predicates;
			}
			predicates_dict.insert(new_predicates_dict.begin(), new_predicates_dict.end());
			curr_predicates_dict = new_predicates_dict;
		}
	}

	if (config.one_to_one_exists)
	{
		vector<vars_t> vars_to_remove;
		for (const auto& it : predicates_dict)
		{
			const vars_t& vars = it.first;
			if (vars[config.one_to_one.in_type] != vars[config.one_to_one.out_type]) vars_to_remove.push_back(vars);
		}
		for (const vars_t& vars : vars_to_remove) predicates_dict.erase(vars);
	}

	// ensures that predicates_dict and inst_predicates_dict agree on the number of predicates for each variable set / instance size
	for (map<vars_t, vector<string>>::iterator it = predicates_dict.begin(); it != predicates_dict.end(); it++)
	{
		const vars_t& vars = it->first;
		const vector<string>& predicates = it->second;
		if (inst_predicates_dict.find(vars) != inst_predicates_dict.end())
		{
			if (column_compression_on)
			{
				assert(predicates.size() <= inst_predicates_dict[vars].size());
			}
			else
			{
				assert(predicates.size() == inst_predicates_dict[vars].size());
			}
		}
	}
}

void Solver::calc_varinp_and_ptoidx()
{
	for (map<vars_t, vector<string>>::iterator it = predicates_dict.begin(); it != predicates_dict.end(); it++)
	{
		const vars_t& vars = it->first;
		const vector<string>& predicates = it->second;
		map<string, vector<int>> var_in_p;
		map<string, int> p_to_idx;
		processor.parse_predicates(predicates, var_in_p, p_to_idx);
		var_in_p_dict[vars] = var_in_p;
		p_to_idx_dict[vars] = p_to_idx;
	}

	for (map<inst_t, vector<string>>::iterator it = inst_predicates_dict.begin(); it != inst_predicates_dict.end(); it++)
	{
		const inst_t& inst = it->first;
		const vector<string>& predicates = it->second;
		map<string, vector<int>> var_in_p;
		map<string, int> p_to_idx;
		processor.parse_predicates(predicates, var_in_p, p_to_idx);
		inst_p_to_idx_dict[inst] = p_to_idx;
	}
}

void Solver::calc_single_type_mappings()
{
	single_type_mappings.resize(num_types);
	vector<int> max_instance_each_type(num_types, 1);
	for (const inst_t& inst : config.instance_sizes)
	{
		for (int i = 0; i < num_types; i++)
		{
			if (inst[i] > max_instance_each_type[i]) max_instance_each_type[i] = inst[i];
		}
	}
	single_type_mappings.resize(num_types);
	for (int type_index = 0; type_index < num_types; type_index++)
	{
		int max_vars = template_sizes[type_index];
		int max_inst = max_instance_each_type[type_index];
		string type_abbr = config.type_abbrs[config.type_order[type_index]];
		single_type_mappings[type_index].resize(max_vars + 1);
		for (int i = 1; i <= max_vars; i++)
		{
			single_type_mappings[type_index][i].resize(max_inst + 1);
			for (int j = 1; j <= max_inst; j++)
			{
				vector<map<string, string>> vars_mappings_true;
				helper.calc_vars_mapping(type_index, i, j, true, vars_mappings_true);
				single_type_mappings[type_index][i][j][true] = vars_mappings_true;
				vector<map<string, string>> vars_mappings_false;
				helper.calc_vars_mapping(type_index, i, j, false, vars_mappings_false);
				single_type_mappings[type_index][i][j][false] = vars_mappings_false;
			}
		}
	}
}

void Solver::calc_single_type_self_mappings()
{
	single_type_self_mappings.resize(num_types);
	for (int type_index = 0; type_index < num_types; type_index++)
	{
		int max_vars = template_sizes[type_index];
		string type_abbr = config.type_abbrs[config.type_order[type_index]];
		single_type_self_mappings[type_index].resize(max_vars + 1);
		for (int i = 1; i <= max_vars; i++)
		{
			single_type_self_mappings[type_index][i].resize(max_vars + 1);
			for (int j = 1; j <= i; j++)
			{
				vector<vector<int>> vars_mappings;
				helper.calc_vars_self_mapping(i, j, vars_mappings);
				single_type_self_mappings[type_index][i][j] = vars_mappings;
			}
		}
	}
}

void Solver::calc_column_indices_dict()
{
	processor.destruct_inst_predicates_dict(inst_predicates_dict);
	processor.destruct_predicates_dict(predicates_dict);
	int counter1 = 0, counter2 = 0, counter3 = 0;
	bool asymmetric_relation_warning_sent = false;
	for (const auto& it1 : predicates_dict)
	{
		const vars_t& vars = it1.first;
		// cout << "vars: " << vec_to_str(vars) << endl;
		const vector<vector<int>>& discretized_predicates = processor.get_discretized_predicates(vars);
		int number_predicates = discretized_predicates.size();
		for (const auto& it2 : inst_predicates_dict)
		{
			counter1++;
			const inst_t& inst = it2.first;
			// cout << "inst: " << vec_to_str(inst) << endl;
			const map<vector<int>, int> discretized_inst_predicates_index_map = processor.get_discretized_inst_predicates_index_map(inst);
			int number_inst_predicates = discretized_inst_predicates_index_map.size();
			vector<vector<bool>> all_is_unique_ordereds;
			helper.get_all_is_unique_ordereds(num_types, all_is_unique_ordereds);
			for (const vector<bool>& is_unique_ordered : all_is_unique_ordereds)
			{
				counter2++;
				// reconstruct single_type_mappings using vector of ints instead of map of strings
				vector<vector<vector<int>>> vectorized_mapping_list_each_type;
				for (int i = 0; i < num_types; i++)
				{
					// further optimization possible (get rid of strings)
					const vector<map<string, string>>& this_type_mapping_list = single_type_mappings[i][vars[i]][inst[i]][is_unique_ordered[i]];
					vector<vector<int>> vectorized_mapping_list;
					for (const map<string, string>& this_type_mapping : this_type_mapping_list)
					{
						assert(int(this_type_mapping.size()) == vars[i]);
						vector<int> vectorized_mapping(vars[i] + 1);
						for (const auto& it : this_type_mapping)
						{
							vectorized_mapping[*(it.first.end() - 1) - '0'] = *(it.second.end() - 1) - '0';
						}
						vectorized_mapping_list.push_back(vectorized_mapping);
					}
					vectorized_mapping_list_each_type.push_back(vectorized_mapping_list);
				}

				vector<int> vars_mappings_size_each_type;
				long long total_num_mappings = 1;
				for (int i = 0; i < num_types; i++)
				{
					int vars_mappings_size_this_type = single_type_mappings[i][vars[i]][inst[i]][is_unique_ordered[i]].size();
					vars_mappings_size_each_type.push_back(vars_mappings_size_this_type);
					total_num_mappings *= vars_mappings_size_this_type;
				}
				// loop over each global variable mapping (e.g., N1 -> N2, N2 -> N2, T1 -> T1)
				for (long long index_number = 0; index_number < total_num_mappings; index_number++)
				{
					counter3++;
					vector<int> mapping_indices_each_type(num_types);
					long long q = index_number;
					for (int i = num_types-1; i >= 0; i--)
					{
						mapping_indices_each_type[i] = q % vars_mappings_size_each_type[i];
						q = q / vars_mappings_size_each_type[i];
					}
					if (config.one_to_one_exists && mapping_indices_each_type[config.one_to_one.in_type] != mapping_indices_each_type[config.one_to_one.out_type]) continue;
					vector<vector<int>> mapping_each_type;
					for (int type_index = 0; type_index < num_types; type_index++)
					{
						int mapping_index = mapping_indices_each_type[type_index];
						mapping_each_type.push_back(vectorized_mapping_list_each_type[type_index][mapping_index]);
					}

					// codes below calculate column_indices_dict[vars][inst][is_unique_ordered][mapping_indices_each_type]
					// 					cout<<"vars: "<<vec_to_str(vars)<<endl;
					// cout<<"inst: "<<vec_to_str(inst)<<endl;
					// cout<<"mapping_each_type: ";
					// for(auto const& mapping: mapping_each_type){
					// 	cout<<vec_to_str(mapping)<<" ";
					// }
					// cout<<endl;
					vector<int> column_indices;
					column_indices.reserve(number_predicates * 2);
					for (const vector<int> &discretized_p : discretized_predicates)
					{
						// cout<<"discretized_p: "<<vec_to_str(discretized_p)<<endl;
						int remapped_predicate_index = processor.mapcall(vars, inst, discretized_p, mapping_each_type);
						if (remapped_predicate_index == INVALID_PREDICATE_COLUMN && !column_compression_on && !asymmetric_relation_warning_sent)
						{
							cout << "Warning! Asymmetric predicate group " << processor.get_sketch_by_id(discretized_p[0]) << " found in samples" << endl;
							py_column_compression_detected = true;
							asymmetric_relation_warning_sent = true;
						}
						column_indices.push_back(remapped_predicate_index);
					}
					for (int i = 0; i < number_predicates; i++)
					{
						column_indices.push_back(column_indices[i] + number_inst_predicates);
					}
					column_indices_dict[vars][inst][is_unique_ordered][mapping_indices_each_type] = column_indices;
				}
			}
		}
	}
}

void Solver::calc_lowhighvars_column_indices_dict()
{
	// compared with column_indices_dict, which connects predicates_dict.at(vars) to csv columns of various instance sizes and is used to check candidate invariants on data matrices
	// lowhighvars_column_indices_dict connects predicates.at(vars) to predicates.at(higher_vars) at various types/dimensions and is used to project candidate invariants to larger quantifier prefix
	for (const vars_t & low_vars : vars_traversal_order)
	{
		const vector<string>& lower_predicates = predicates_dict[low_vars];
		int num_lower_predicates = lower_predicates.size();
		for (int type_index = 0; type_index < num_types; type_index++)
		{
			vars_t high_vars = low_vars;
			high_vars[type_index]++;
			if (config.one_to_one_exists && config.one_to_one.in_type == type_index) high_vars[config.one_to_one.out_type]++;
			if (std::find(vars_traversal_order.begin(), vars_traversal_order.end(), high_vars) != vars_traversal_order.end())
			{
				// a valid low-high vars pair, e.g., [2,1,1] - [2,1,2]
				const vector<string>& higher_predicates = predicates_dict[high_vars];
				int num_higher_predicates = higher_predicates.size();
				const map<string, int>& higher_p_to_idx = p_to_idx_dict[high_vars];
				vector<vector<bool>> all_is_unique_ordereds;
				helper.get_all_is_unique_ordereds(num_types, all_is_unique_ordereds);
				for (const vector<bool>& is_unique_ordered : all_is_unique_ordereds)
				{
					vector<vector<map<string, string>>> all_type_mappings;
					for (int type_index = 0; type_index < num_types; type_index++)
					{
						const vector<map<string, string>>& this_type_mappings = single_type_mappings[type_index][low_vars[type_index]][high_vars[type_index]][is_unique_ordered[type_index]];
						all_type_mappings.push_back(this_type_mappings);
						if (config.one_to_one_exists && config.one_to_one.out_type == type_index)
						{
							vector<map<string, string>> out_type_mappings = all_type_mappings.back();
							all_type_mappings.pop_back();
							vector<map<string, string>> in_type_mappings = all_type_mappings.back();
							all_type_mappings.pop_back();
							vector<map<string, string>> bijection_type_mappings;
							helper.zip_merge_vector_of_map_string(in_type_mappings, out_type_mappings, bijection_type_mappings);
							all_type_mappings.push_back(bijection_type_mappings);
						}
					}
					vector<vector<map<string, string>>> mapping_each_type_list_list = cart_product(all_type_mappings);
					vector<vector<int>> all_column_indices_this_lowhighvars_isuniqueordered;
					for (const vector<map<string, string>>& mapping_each_type_list : mapping_each_type_list_list)
					{
						map<string, string> vars_map;
						join_vector_of_maps(mapping_each_type_list, vars_map);
						vector<string> mapped_predicates;
						processor.remap_predicates(lower_predicates, vars_map, mapped_predicates);
						vector<int> column_indices(2 * num_lower_predicates);
						for (int i = 0; i < num_lower_predicates; i++)
						{
							int new_pos;
							if (higher_p_to_idx.find(mapped_predicates[i]) == higher_p_to_idx.end())
							{
								assert(column_compression_on || py_column_compression_detected);
								new_pos = INVALID_PREDICATE_COLUMN;  // negative number means no mapped predicate at higher vars
							}
							else
							{
								new_pos = higher_p_to_idx.at(mapped_predicates[i]);
							}
							column_indices[i] = new_pos;
							column_indices[i + num_lower_predicates] = new_pos + num_higher_predicates;
						}
						all_column_indices_this_lowhighvars_isuniqueordered.push_back(column_indices);
					}
					lowhighvars_column_indices_dict[low_vars][high_vars][is_unique_ordered] = all_column_indices_this_lowhighvars_isuniqueordered;
				}
			}
		}
	}
}


void Solver::calc_inst_data_mat_dict_each_leading_forall()
{
	// data projection
	// let's say we have three types T1 T2 T3. The template size is (2,2,1). The instance sizes are (1,1,1) - (3,3,3).
	inst_data_mat_dict_each_leading_forall[lead_forall_vars_t()] = inst_data_mat_dict;  // base case. No leading forall. Use csv files themselves
	vector<vector<lead_forall_vars_t>> leading_forall_vars_each_length(num_types + 1);  
	leading_forall_vars_each_length[0] = { lead_forall_vars_t() };
	// leading_forall_vars_each_length[0] = [ vector<int>() ]
	// leading_forall_vars_each_length[1] = [ [1], [2] ]
	// leading_forall_vars_each_length[2] = [ [1,1], [1,2], [2,1], [2,2] ]
	// leading_forall_vars_each_length[3] = [ [1,1,1], [1,2,1], [2,1,1], [2,2,1] ]
	// in other words, leading_forall_vars_each_length contains all possible leading forall variable numbers, which is the set of keys of inst_data_mat_dict_each_leading_forall
	for (int projecting_type_index = 0; projecting_type_index < num_types; projecting_type_index++)
	{
		if (config.one_to_one_exists && config.one_to_one.in_type == projecting_type_index) continue;
		// let's say we are now projecting T2, then projecting_type_index = 1. Before T2 the leading forall vars has two choices [1] and [2], 
		// T2 has only two var number choices 1 and 2, so we end up with 2*2=4 leading forall vars choices [1,1], [1,2], [2,1], [2,2] to be projected into
		int max_vars = config.template_vars_map[config.type_order[projecting_type_index]].size();  // how many quantified variables this type can have
		const vector<lead_forall_vars_t>& all_existing_leading_forall_vars = (config.one_to_one_exists && config.one_to_one.out_type == projecting_type_index) ? leading_forall_vars_each_length[projecting_type_index - 1] : leading_forall_vars_each_length[projecting_type_index];
		for (const lead_forall_vars_t& existing_leading_forall_vars : all_existing_leading_forall_vars)
		{
			const map<inst_t, DataMatrix>& last_data_mat_dict = inst_data_mat_dict_each_leading_forall.at(existing_leading_forall_vars);
			for (int num_vars = max_vars; num_vars >= 1; num_vars--)
			{
				// let's say we are projecting into leading forall vars [1,2]
				// last_data_mat_dict has 9 keys: [1,1,1], [1,1,2], ..., [1,3,2], [1,3,3]
				// we should discard [1,1,1], [1,1,2] and [1,1,3] because they cannot be mapped to two unique T2 quantified variables
				// new_data_mat_dict and deduplicated_data_mat_dict both should have three keys [1,2,1], [1,2,2], [1,2,3], each integrating two last keys. For example, [1,2,3] integrates last instance sizes [1,2,3] and [1,3,3]
				lead_forall_vars_t new_leading_forall_vars = existing_leading_forall_vars;
				new_leading_forall_vars.push_back(num_vars);
				if (config.one_to_one_exists && config.one_to_one.out_type == projecting_type_index) new_leading_forall_vars.push_back(num_vars);
				leading_forall_vars_each_length[projecting_type_index + 1].push_back(new_leading_forall_vars);  // add [1,2]
				map<inst_t, DataMatrix> new_data_mat_dict;
				map<inst_t, unordered_set<vector<int>, VectorHash>> deduplicated_data_mat_dict;
				for (map<inst_t, DataMatrix>::const_iterator it = last_data_mat_dict.begin(); it != last_data_mat_dict.end(); it++)
				{
					const inst_t& old_inst = it->first;
					int num_objects = old_inst[projecting_type_index];
					if (num_objects < num_vars) continue;  // discard [1,1,3]
					inst_t reduced_inst = old_inst;
					reduced_inst[projecting_type_index] = num_vars;
					if (config.one_to_one_exists && config.one_to_one.out_type == projecting_type_index) reduced_inst[projecting_type_index - 1] = num_vars;
					unordered_set<vector<int>, VectorHash>& deduplicated_data_mat = deduplicated_data_mat_dict[reduced_inst];  // deduplicated_data_mat may be not empty now, because multiple old_inst can project to the same reduced_inst
					const DataMatrix& old_data_mat = it->second;
					const map<string, int>& old_inst_p_to_idx = inst_p_to_idx_dict.at(old_inst);
					vector<map<string, string>> vars_mappings = single_type_mappings[projecting_type_index][num_vars][num_objects][true];
					if (config.one_to_one_exists && config.one_to_one.out_type == projecting_type_index)
					{
						const vector<map<string, string>>& in_type_vars_mappings = single_type_mappings[projecting_type_index - 1][num_vars][num_objects][true];
						vector<map<string, string>> bijection_vars_mappings;
						helper.zip_merge_vector_of_map_string(in_type_vars_mappings, vars_mappings, bijection_vars_mappings);
						vars_mappings = bijection_vars_mappings;
					}
					int num_predicates_old_inst = inst_predicates_dict.at(old_inst).size();
					int num_predicates_reduced_inst = inst_predicates_dict.at(reduced_inst).size();
					for (const map<string, string>& vars_map : vars_mappings)
					{
						vector<string> mapped_inst_predicates;
						processor.remap_predicates(inst_predicates_dict.at(reduced_inst), vars_map, mapped_inst_predicates);
						vector<int> column_indices(2 * num_predicates_reduced_inst);
						bool all_remapped_predicates_exists = true;
						for (int i = 0; i < num_predicates_reduced_inst; i++)
						{
							const string& mapped_p_str = mapped_inst_predicates[i];
							if (old_inst_p_to_idx.find(mapped_p_str) == old_inst_p_to_idx.end())
							{
								assert(column_compression_on || py_column_compression_detected);
								all_remapped_predicates_exists = false;
								break;
							}
							int new_pos = old_inst_p_to_idx.at(mapped_p_str);
							column_indices[i] = new_pos;
							column_indices[i + num_predicates_reduced_inst] = new_pos < num_predicates_old_inst? new_pos + num_predicates_old_inst : new_pos - num_predicates_old_inst;
						}
						if (!all_remapped_predicates_exists) continue;

						for (int i = 0; i < old_data_mat.nrow; i++)
						{
							int* row = old_data_mat.data_ptr[i];
							vector<int> reduced_row(2 * num_predicates_reduced_inst);
							int k = 0;
							for (int idx : column_indices)
							{
								reduced_row[k++] = row[idx];
							}
							deduplicated_data_mat.insert(reduced_row);
						}
					}
				}
				// now we have visited all old instances. We should convert deduplicated_data_mat_dict to new_data_mat_dict
				for (map<inst_t, unordered_set<vector<int>, VectorHash>>::const_iterator it = deduplicated_data_mat_dict.begin(); it != deduplicated_data_mat_dict.end(); it++)
				{
					const inst_t& inst = it->first;
					const unordered_set<vector<int>, VectorHash>& deduplicated_data_mat = it->second;
					int nrow = deduplicated_data_mat.size();
					if (nrow == 0) continue;
					int ncol = (*deduplicated_data_mat.begin()).size();
					assert(ncol > 0);
					DataMatrix new_data_mat;
					new_data_mat.data_ptr = contiguous_2d_array(nrow, ncol);
					new_data_mat.nrow = nrow;
					new_data_mat.ncol = ncol;
					int row_count = 0;
					for (const vector<int>& row : deduplicated_data_mat)
					{
						std::copy(row.begin(), row.end(), new_data_mat.data_ptr[row_count]);
						row_count++;
					}
					new_data_mat_dict[inst] = new_data_mat;
				}

				inst_data_mat_dict_each_leading_forall[new_leading_forall_vars] = new_data_mat_dict;
			}
		}
	}
}

void Solver::precompute_vars_self_mapping_bulk()
{
	for (int num_exists = 0; num_exists <= config.max_exists; num_exists++)
	{
		// iterate through each subtemplate and enumerate candidate invariants
		for (const vars_t& vars : vars_traversal_order)
		{
			for (const qalter_t& qalter : vars_qalter_exists_number[vars][num_exists])
			{
				precompute_vars_self_mapping(vars, qalter);
			}
		}
	}
}

void Solver::reduce_predicates(vector<string>& old_predicates, vector<string>& new_predicates, int type_index, int var_index_to_remove) const
{
	assert(new_predicates.size() == 0);
	map<string, vector<int>> var_in_p;
	map<string, int> p_to_idx;
	processor.parse_predicates(old_predicates, var_in_p, p_to_idx);
	int num_predicates = old_predicates.size();
	string var_to_remove = config.template_vars_map.at(config.type_order[type_index])[var_index_to_remove];
	vector<int> p_to_remove = var_in_p[var_to_remove];
	/* TODO-long-term: support one-to-one, below shows old code
	if (config.one_to_one_exists)
	{
		map<string, string>::iterator it = config.one_to_one_bidir.find(var_to_remove);
		if (it != config.one_to_one_bidir.end())
		{
			vector<int>& additional_p_to_remove = var_in_p[it->second];
			p_to_remove.insert(p_to_remove.end(), additional_p_to_remove.begin(), additional_p_to_remove.end());
		}
	}
	*/
	for (int i = 0; i < num_predicates; i++)
	{
		if (std::find(p_to_remove.begin(), p_to_remove.end(), i) == p_to_remove.end())
		{
			new_predicates.push_back(old_predicates[i]);
		}
	}
}

void Solver::calc_vars_traversal_order()
{
	vars_t genesis_vars(num_types, 1);
	vars_traversal_order.push_back(genesis_vars);
	for (int type_index = 0; type_index < num_types; type_index++)
	{
		vector<vars_t> curr_traversal_order = vars_traversal_order;
		int curr_group_size = template_sizes[type_index];
		for (int j = 1; j < curr_group_size; j++)
		{
			vector<vars_t> new_traversal_order;
			for (const vars_t& vars : curr_traversal_order)
			{
				vars_t new_vars = vars;
				new_vars[type_index]++;
				new_traversal_order.push_back(new_vars);
			}
			vars_traversal_order.insert(vars_traversal_order.end(), new_traversal_order.begin(), new_traversal_order.end());
			curr_traversal_order = new_traversal_order;
		}
	}
	if (config.one_to_one_exists)
	{
		vector<vars_t> filtered_vars_traversal_order;
		for (const vars_t& vars : vars_traversal_order)
		{
			if (vars[config.one_to_one.in_type] == vars[config.one_to_one.out_type]) filtered_vars_traversal_order.push_back(vars);
		}
		vars_traversal_order = filtered_vars_traversal_order;
	}
}

void Solver::calc_vars_qalters_exists_number()
{
	// enumerate all qalters
	vector<qalter_t> all_qalters;
	helper.get_all_qalters(num_types, all_qalters);
	// loop over each vars and qalter
	for (const vars_t& vars : vars_traversal_order)
	{
		vars_qalter_exists_number[vars].resize(config.max_exists + 1);
		for (const qalter_t& qalter : all_qalters)
		{
			int number_exists = 0;
			for (int i = 0; i < num_types; i++)
			{
				if (qalter[i]) number_exists += vars[i];
			}
			if (number_exists <= config.max_exists)
			{
				vars_qalter_exists_number[vars][number_exists].push_back(qalter);
			}
		}
	}
}

void Solver::enumerate_dnf(const vars_t& vars, const qalter_t& qalter, inv_set_t& inv_results)
{
	// vars specifies the number of quantified variables for each type, qalter specifies for each type, whether the variables are universally or existentially quantified
	// preparation steps
	auto enumerate_dnf_start_time = time_now();
	vector<bool> is_unique_ordered;
	qalter_to_unique_ordered(qalter, is_unique_ordered);
	const vector<string>& predicates = predicates_dict[vars];
	int number_predicates = predicates.size();
	const map<string, vector<int>>& var_in_p = var_in_p_dict[vars];
	map<int, int> exists_type_to_varnum_map;
	vector<int> exists_type_list;
	vector<string> exists_vars;
	vector<int> leading_forall_vars;
	helper.extract_exists_vars(vars, qalter, exists_type_to_varnum_map, exists_type_list, exists_vars, leading_forall_vars);

	auto enumerate_dnf_end_time = time_now();
	cout << "enumerate_dnf time: " << std::fixed << std::setprecision(2) << double(time_diff(enumerate_dnf_end_time, enumerate_dnf_start_time))/1000000 << "s" << endl;
}


int Solver::check_if_inv_on_csv(const vars_t& vars, const qalter_t& qalter, const inst_t& inst, const inv_t& candidate_inv, const DataMatrix& data_mat, const map<vector<int>, vector<int>>& one_column_indices_dict) const
{
	// example
	// vars: [2,2,1], qalter: [false, true, false], candidate_inv: [[0,3], [2]], data_mat has instance size [3,2,2]
	// then the candidate invariant has shape forall X1 < X2. exists Y1 Y2. forall Z1. ...
	// the keys one_column_indices_dict are [0,0,0], [0,0,1], [0,1,0], [0,1,1], ..., [0,3,0], [0,3,1], [1,0,0], ..., [1,3,1], [2,0,0], ..., [2,3,1]
	// the first element can take 3 values which corresponds to X1 X2 -> x1 x2 | x1 x3 | x2 x3, second element 4 values Y1 Y2 -> y1 y1 | y1 y2 | y2 y1 | y2 y2, third element 2 values Z1 -> z1 | z2
		bool debug = false;
	// if(qalter==vector<bool>{false,false,true,false}){
	// 	if(candidate_inv == set<vector<int>>{{5},{15},{23}}){
	// 		if(vars == vars_t{2,1,1,1})
	// 			debug = true;
	// 	}
	// }
	if(debug){
		cout<<"DEBUG!"<<endl;
		for(auto const& [key, value]: one_column_indices_dict){
			cout<<vec_to_str(key)<<" -> "<<vec_to_str(value)<<endl;
		}
	}
	int nrow = data_mat.nrow;
	int** data_ptr = data_mat.data_ptr;
	vector<int> num_mapping_each_type(num_types);
	vector<bool> is_unique_ordered;
	qalter_to_unique_ordered(qalter, is_unique_ordered);
	for (int i = 0; i < num_types; i++) num_mapping_each_type[i] = single_type_mappings[i][vars[i]][inst[i]].at(is_unique_ordered[i]).size();
	for (int row = 0; row < nrow; row++)
	{
		bool this_row_is_satisfied = true;
		const int* data_line = data_ptr[row];
		vector<int> counters(num_types, 0);
		while (true)
		{
			const vector<int>& curr_mapping = one_column_indices_dict.at(counters);
			vector<vector<int>> candidate_inv_as_data_indices;
			bool invalid_mapping_discovered = false;
			for (const clause_t& anded_clause : candidate_inv)
			{
				int anded_clause_length = anded_clause.size();
				clause_t mapped_clause(anded_clause);
				for (int i = 0; i < anded_clause_length; i++)
				{
					mapped_clause[i] = curr_mapping[anded_clause[i]];
					if (mapped_clause[i] < 0) invalid_mapping_discovered = true;
				}
				candidate_inv_as_data_indices.push_back(mapped_clause);
			}
			bool true_on_curr_counters = invalid_mapping_discovered ? true : check_if_qfree_dnf_formula_holds_on_data_line(data_line, candidate_inv_as_data_indices);
			bool true_on_current_level = true_on_curr_counters;
			bool current_level_unknown = false;
			// forall N1. p(N1) has two levels: the base level is whether p(n1), p(n2),... holds; the top level is whether forall N1. p(N1) holds
			// in general, a formula has num_types + 1 levels. At each level, some quantifier prefix are instantiated. Base level -> all instantiated; top level -> none instantiated.
			for (int type_index = num_types - 1; type_index >= 0; type_index--)
			{
				current_level_unknown = false;
				if (qalter[type_index])
				{
					if (true_on_current_level)
					{
						true_on_current_level = true;
					}
					else
					{
						if (counters[type_index] == num_mapping_each_type[type_index] - 1)
						{
							true_on_current_level = false;
						}
						else
						{
							current_level_unknown = true;
						}
					}
				}
				else
				{
					if (true_on_current_level)
					{
						if (counters[type_index] == num_mapping_each_type[type_index] - 1)
						{
							true_on_current_level = true;
						}
						else
						{
							current_level_unknown = true;
						}
					}
					else
					{
						true_on_current_level = false;
					}
				}
				if (current_level_unknown)
				{
					counters[type_index]++;
					for (int trailing_type_index = type_index + 1; trailing_type_index < num_types; trailing_type_index++) counters[trailing_type_index] = 0;
					break;
				}
			}
			if (!current_level_unknown)
			{
				// the loop above terminates by exhausting types rather than "break", we know the whether this data line satisfies the candidate inv
				this_row_is_satisfied = true_on_current_level;
				break;
			}
		}
		if (!this_row_is_satisfied)
		{
			return row;
		}
	}
	return INV_HOLD_ON_CSV;
}

bool Solver::check_if_qfree_dnf_formula_holds_on_data_line(const int* data_line, const vector<vector<int>>& candidate_inv_as_data_indices) const
{
	for (const vector<int>& anded_clause : candidate_inv_as_data_indices) 
	{
		bool this_clause_is_satisfied = true;
		for (int col : anded_clause)
		{
			if (data_line[col] == 0)
			{
				this_clause_is_satisfied = false;
				break;
			}
		}
		if (this_clause_is_satisfied) return true;
	}
	return false;
}

void Solver::precompute_vars_self_mapping(const vars_t& vars, const qalter_t& qalter)
{
	const map<string, int>& p_to_idx = p_to_idx_dict[vars];
	vector<bool> is_unique_ordered;
	qalter_to_unique_ordered(qalter, is_unique_ordered);
	bool self_mapped_predicates_dict_already_calculated = self_mapped_predicates_dict[vars][is_unique_ordered].size() > 0; // calculated by another qalter with the same is_unique_ordered
	if (self_mapped_predicates_dict_already_calculated) return;
	const vector<string>& predicates = predicates_dict[vars];
	int num_predicates = predicates.size();
	int double_num_predicates = 2 * num_predicates;
	
	// calculate self_mapped_predicates_dict[vars][is_unique_ordered], which is used to calculate permuted invariants
	vector<vector<map<string, string>>> vars_mappings_each_type(num_types);
	for (int i = 0; i < num_types; i++)
	{
		if (is_unique_ordered[i] && (config.total_ordered_types.find(i) != config.total_ordered_types.end()))  // leading ordered forall variables cannot be permuted
		{
			vars_mappings_each_type[i] = { map<string,string>() };
			continue;
		}
		vector<vector<int>> this_type_mappings = single_type_self_mappings.at(i).at(vars[i]).at(vars[i]);
		// filter out N1 N2 -> N1 N1. This is not allowed in invariant permutation. exists X Y. p(X,Y) is not equivalent to exists X Y. p(X,X)
		vars_mappings_each_type[i].reserve(this_type_mappings.size());
		vector<string> input_var_list;
		construct_vars_vector(config.type_abbrs[config.type_order[i]], vars[i], input_var_list);
		for (const vector<int>& this_map_as_indices : this_type_mappings)
		{
			map<string, string> this_map;
			vector<string> projected_var_list;
			construct_vars_vector(config.type_abbrs[config.type_order[i]], this_map_as_indices, projected_var_list);
			for (int j = 0; j < vars[i]; j++) this_map[input_var_list[j]] = projected_var_list[j];
			vars_mappings_each_type[i].push_back(this_map);
		}
		if (config.one_to_one_exists && config.one_to_one.out_type == i)
		{
			vector<map<string, string>> bijection_mappings;
			helper.zip_merge_vector_of_map_string(vars_mappings_each_type[i - 1], vars_mappings_each_type[i], bijection_mappings);
			vars_mappings_each_type[i - 1] = { map<string,string>() };
			vars_mappings_each_type[i] = bijection_mappings;
		}
	}

	vector<vector<map<string, string>>> vars_mappings;
	vars_mappings = cart_product(vars_mappings_each_type);
	for (const vector<map<string, string>>& vars_map_list : vars_mappings)
	{
		// an example vars_map_list: [{"N1": "N2", "N2": "N1"}, {"T1":"T1"}]
		map<string, string> vars_map;
		join_vector_of_maps(vars_map_list, vars_map);
		vector<string> new_predicates;
		processor.remap_predicates(predicates, vars_map, new_predicates);
		vector<int> new_predicates_as_indices_of_predicates(double_num_predicates);
		for (int i = 0; i < num_predicates; i++)
		{
			if (p_to_idx.find(new_predicates[i]) == p_to_idx.end())
			{
				assert(column_compression_on || py_column_compression_detected);
				new_predicates_as_indices_of_predicates[i] = INVALID_PREDICATE_COLUMN;
			}
			else
			{
				new_predicates_as_indices_of_predicates[i] = p_to_idx.at(new_predicates[i]);
			}
		}
		for (int i = num_predicates; i < double_num_predicates; i++) new_predicates_as_indices_of_predicates[i] = new_predicates_as_indices_of_predicates[i - num_predicates] + num_predicates;
		self_mapped_predicates_dict[vars][is_unique_ordered].push_back(new_predicates_as_indices_of_predicates);
	}
}

void Solver::calc_self_mapped_predicates_each_mapping()
{
	for (const vars_t& vars : vars_traversal_order)
	{
		// calculate self_mapped_new_predicates_each_mapping[vars][(start_type, end_type)], which is used to calculate exists->forall predecessors
		// should only be used for the first existential type in qalter
		// later existential types, when converted to forall, does not need to distinguish N1 < N2 and N2 < N1 for itself and following forall types
		const vector<string>& predicates = predicates_dict.at(vars);
		int number_predicates = predicates.size();
		int double_number_predicates = 2 * number_predicates;
		const map<string, int>& p_to_idx = p_to_idx_dict.at(vars);
		for (int start_type = 0; start_type < num_types; start_type++)
		{
			for (int end_type = start_type + 1; end_type <= num_types; end_type++)
			{
				// if qalter = [false, true, false, true], first_exists = 1, second_exists = 3
				// if qalter = [false, false, false, false], first_exists = -1, second_exists = 4
				vector<vector<vector<int>>> indices_mappings_each_type(end_type - start_type);
				vector<vector<string>> input_vars_lists(end_type - start_type);
				for (int type_index = start_type; type_index < end_type; type_index++)
				{
					int num_vars_this_type = vars[type_index];
					construct_vars_vector(config.type_abbrs[config.type_order[type_index]], num_vars_this_type, input_vars_lists[type_index - start_type]);
					vector<vector<int>> mappings_this_type;
					for (int out_var_num = 1; out_var_num <= num_vars_this_type; out_var_num++)
					{
						const vector<vector<int>>& mappings_this_type_out_var = single_type_self_mappings[type_index][num_vars_this_type][out_var_num];
						mappings_this_type.insert(mappings_this_type.end(), mappings_this_type_out_var.begin(), mappings_this_type_out_var.end());
					}
					indices_mappings_each_type[type_index - start_type] = mappings_this_type;
				}
				vector<vector<vector<int>>> indices_mappings_across_types = cart_product(indices_mappings_each_type);
				for (const vector<vector<int>>& indices_mapping_across_types : indices_mappings_across_types)
				{
					map<string, string> vars_map;
					for (int type_index = start_type; type_index < end_type; type_index++)
					{
						vector<string> projected_var_list;
						construct_vars_vector(config.type_abbrs[config.type_order[type_index]], indices_mapping_across_types[type_index - start_type], projected_var_list);
						for (int j = 0; j < vars[type_index]; j++) vars_map[input_vars_lists[type_index - start_type][j]] = projected_var_list[j];
					}
					vector<string> new_predicates;
					processor.remap_predicates(predicates, vars_map, new_predicates);
					vector<int> new_predicates_as_indices_of_predicates(double_number_predicates);
					for (int i = 0; i < number_predicates; i++)
					{
						if (p_to_idx.find(new_predicates[i]) == p_to_idx.end())
						{
							assert(column_compression_on || py_column_compression_detected);
							new_predicates_as_indices_of_predicates[i] = INVALID_PREDICATE_COLUMN;
						}
						else
						{
							new_predicates_as_indices_of_predicates[i] = p_to_idx.at(new_predicates[i]);
						}
					}
					for (int i = number_predicates; i < double_number_predicates; i++) new_predicates_as_indices_of_predicates[i] = new_predicates_as_indices_of_predicates[i - number_predicates] + number_predicates;
					self_mapped_new_predicates_each_mapping[vars][std::make_pair(start_type,end_type)][indices_mapping_across_types] = new_predicates_as_indices_of_predicates;
				}
			}
		}
	}
}


void Solver::add_permuted_candidates(inv_set_t& formula_set, const vars_t& vars, const vector<bool>& is_unique_ordered, const inv_t& candidate_inv)
{
	const vector<vector<int>>& all_new_predicates_indices = self_mapped_predicates_dict[vars][is_unique_ordered];
	for (const vector<int>& new_predicates_indices : all_new_predicates_indices)
	{
		inv_t new_candidate_inv;
		bool mapping_valid = map_inv_with_column_indices(candidate_inv, new_predicates_indices, new_candidate_inv);
		if (mapping_valid) formula_set.insert(new_candidate_inv);
	}
}

void Solver::calc_deuniqued_invs(const vars_t& vars, const qalter_t& qalter, vector<inv_set_t>& deuniqued_invs)
{
	// for example, if vars=[1,2,1], qalter=[false,false,true]
	// the current template is forall X1. forall Y1 < Y2. exists Z1. ...
	// there are two elements in the output deuniqued_invs, the indices 0 and 1 represent the first deuniqued type, both corresponds to forall X1. forall Y1 Y2. exists Z1. ...
	// [true,true,false] gives the identical result as extended_invs_dict[vars][qalter] so we do not record it
	// one important property: deuniqued_invs[any-key] should be a subset of extended_invs_dict[vars][qalter]
	//TODO!
}


void Solver::early_preparations()
{
	calc_predicates_dict();
	calc_varinp_and_ptoidx();
	calc_single_type_mappings();  // map quantified variables to instance objects
	calc_single_type_self_mappings();  // map quantified variables to quantified variables
	calc_column_indices_dict();
}

void Solver::auto_solve()
{
	auto early_prep_start_time = time_now();
	early_preparations();
	
	calc_vars_traversal_order();  // store a valid traversal order of the quantified variable set in vars_traversal_order
	calc_lowhighvars_column_indices_dict();
	calc_inst_data_mat_dict_each_leading_forall();
	calc_vars_qalters_exists_number();
	precompute_vars_self_mapping_bulk();
	calc_self_mapped_predicates_each_mapping();
	split_n_into_k_numbers_bulk(config.max_literal, config.max_ored_clauses, config.max_anded_literals, n_into_k);
	auto late_prep_end_time = time_now();
	cout << "Solver preparation time: " << std::fixed << std::setprecision(2) << double(time_diff(late_prep_end_time, early_prep_start_time))/1000000 << "s" << endl;

	// first enumerate existential-quantifier-free invariants, then one exists, two exists, and so on
	for (int num_exists = 0; num_exists <= config.max_exists; num_exists++)
	{
		// iterate through each subtemplate and enumerate candidate invariants
		for (const vars_t& vars : vars_traversal_order)
		{
			for (const qalter_t& qalter : vars_qalter_exists_number[vars][num_exists])
			{
				vector<bool> is_unique_ordered; qalter_to_unique_ordered(qalter, is_unique_ordered);
				inv_set_t invs;
				cout << "enumerating vars " << vec_to_str(vars) << " and qalter " << vec_to_str(qalter) << endl;
				enumerate_dnf(vars, qalter, invs);
				invs_dict[vars][qalter] = invs;
				// for each vars successor succesor of the current subtemplate, project the checked invariants

				auto inv_generalization_start_time = time_now();
				for (map<vars_t, map<vector<bool>, vector<vector<int>>>>::const_iterator it = lowhighvars_column_indices_dict[vars].begin(); it != lowhighvars_column_indices_dict[vars].end(); it++)
				{// Exactly the grounding in ours

					// const vars_t& successor = it->first;
					// int successor_num_exists = 0;
					// for (int i = 0; i < num_types; i++) if (qalter[i]) successor_num_exists += successor[i];
					// if (successor_num_exists > config.max_exists) continue;  // (successor, qalter) pair is out of the current template
					// const vector<vector<int>>& column_indices_list = it->second.at(is_unique_ordered);
					// inv_set_t new_extended_invs;
					// helper.generalize_invs(extended_invs_dict[vars][qalter], column_indices_list, new_extended_invs);
					// extended_invs_dict[successor][qalter].insert(new_extended_invs.begin(), new_extended_invs.end());
					// new_extended_invs.clear();
					// generalize_exists_xpxx_invs(vars, successor, qalter, extended_invs_dict.at(vars).at(qalter), new_extended_invs);  // TODO-now: fix
					// extended_invs_dict[successor][qalter].insert(new_extended_invs.begin(), new_extended_invs.end());
				}
				auto inv_generalization_end_time = time_now();
				int inv_generalization_time = time_diff(inv_generalization_end_time, inv_generalization_start_time);
				cout << "inv generalization_time: " << std::fixed << std::setprecision(2) << double(inv_generalization_time)/1000000 << "s" << endl;
			}
		}
	}
	
	cout << "Invariant enumeration finished" << endl;
}

void Solver::encode_and_output(const string& outfile, map<int, tuple<vars_t, qalter_t, inv_t>>& id_to_inv, const vector<tuple<vars_t, qalter_t, string>>& more_invs)
{
	vector<string> str_invs;
	encoder.encode_invs_dict(invs_dict, predicates_dict, str_invs, id_to_inv, more_invs);
	encoder.append_invs_ivy(input_ivy_file, outfile, str_invs);
}