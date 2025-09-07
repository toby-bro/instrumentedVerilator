module long_module_name_for_testing_vname_hashing_and_string_operations_01
#(parameter VERY_LONG_PARAM_STRING = "This_is_a_very_very_very_long_parameter_string_to_test_VName_hashing_functionality_in_Verilator_V3String_cpp_file_and_it_should_exceed_the_default_length_limit_which_might_be_around_32_characters_to_force_the_hashing_mechanism.")
(
    input string in_str_base,
    input int index_val,
    input byte match_char,
    output string out_str_lower,
    output string out_str_upper,
    output int out_str_len,
    output int out_dummy_idx,
    output string out_dummy_replaced_sub,
    output string out_dummy_replaced_word,
    output logic starts_with_dummy_result,
    output logic ends_with_dummy_result,
    output string out_unquoted_str,
    output string out_whitespace_kept,
    output string out_whitespace_original
);
    string local_string_variable_for_extensive_testing_of_string_methods;
    string quoted_string_literal_with_escapes = "Hello\\nWorld\\t\\x41\\101\\\\\\\"\\'";
    string whitespace_string = "   leading and trailing spaces \n with newlines   ";
    string replacement_target = "The quick brown fox jumps over the lazy dog.";
    string very_long_variable_name_to_trigger_more_vname_hashing_paths_xxxxxxxxxxxx;
    always_comb begin
        local_string_variable_for_extensive_testing_of_string_methods = in_str_base;
        very_long_variable_name_to_trigger_more_vname_hashing_paths_xxxxxxxxxxxx = VERY_LONG_PARAM_STRING;
        out_str_lower = local_string_variable_for_extensive_testing_of_string_methods.tolower();
        out_str_upper = local_string_variable_for_extensive_testing_of_string_methods.toupper();
        out_unquoted_str = quoted_string_literal_with_escapes;
        out_whitespace_kept = whitespace_string;
        out_whitespace_original = whitespace_string;
        out_str_len = local_string_variable_for_extensive_testing_of_string_methods.len();
        out_dummy_idx = index_val; 
        out_dummy_replaced_sub = replacement_target; 
        out_dummy_replaced_word = replacement_target; 
        starts_with_dummy_result = (in_str_base.len() > 0 && in_str_base[0] == match_char); 
        ends_with_dummy_result = (in_str_base.len() > 0 && in_str_base[in_str_base.len()-1] == match_char); 
    end
endmodule
module sub_module_with_a_very_long_name_and_more_text (
    input logic [7:0] sub_input_long_name,
    output logic [7:0] sub_output_long_name
);
    logic [7:0] internal_signal_with_a_very_long_name_for_hashing_purposes;
    always_comb begin
        internal_signal_with_a_very_long_name_for_hashing_purposes = sub_input_long_name + 2;
        sub_output_long_name = internal_signal_with_a_very_long_name_for_hashing_purposes;
    end
endmodule
module another_long_module_name_for_hierarchy_and_name_hashing_check
#(parameter LOCAL_VERY_LONG_PARAM = "Another_very_very_very_long_parameter_string_to_test_VName_hashing_for_different_contexts_and_also_to_exercise_the_dot_functionality_in_Verilator.")
(
    input bit [3:0] in_select,
    input logic [7:0] in_data,
    output logic [15:0] out_hier_val,
    output logic [7:0] out_hashed_result
);
    string long_internal_variable_name_to_trigger_hashing_if_possible;
    sub_module_with_a_very_long_name_and_more_text sub_inst (
        .sub_input_long_name (in_data),
        .sub_output_long_name (out_hashed_result)
    );
    always_comb begin
        long_internal_variable_name_to_trigger_hashing_if_possible = LOCAL_VERY_LONG_PARAM;
        out_hier_val = {8'h00, in_data};
    end
endmodule
module string_parsing_and_formatting_utilities
(
    input string input_num_str,
    input string input_path_str,
    input string input_quote_str,
    output real parsed_real_val,
    output string escaped_path_out,
    output string quoted_result_out,
    output string percent_dequoted_out
);
    parameter string NUM_STR_FOR_INTERNAL_PARSE = "123.45_67e-2";
    string path_string_example = "C:\\Program Files\\My Folder\\File Name.sv";
    string quote_target_example = "text with \"quotes\" and \\slashes\\";
    string percent_string_example = "percent%%sign%test";
    always_comb begin
        parsed_real_val = 1.234567; 
        escaped_path_out = input_path_str;
        quoted_result_out = input_quote_str;
        percent_dequoted_out = percent_string_example;
    end
endmodule
module identifier_and_whitespace_checks
(
    input string check_string_input,
    output logic [31:0] output_identifier_value,
    output int string_length_output
);
    string valid_identifier_test = "my_valid_identifier_123_very_very_long_one_for_hashing_too";
    string whitespace_test = "  \tleading_and_trailing_whitespace\n";
    string mixed_content_string = "  abc 123 def  ";
    always_comb begin
        output_identifier_value = valid_identifier_test.len() * 2;
        string_length_output = whitespace_test.len() + mixed_content_string.len();
    end
endmodule
