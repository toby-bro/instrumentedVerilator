module SvStringLiteralsAndParsing (
    input logic [7:0] in_char_val,
    output string out_processed_string,
    output real out_num_val,
    output logic out_is_printable_all
);
    localparam string NL_STR = "Line one\nLine two";
    localparam string TAB_STR = "Col1\tCol2";
    localparam string CR_STR = "Carriage\rReturn";
    localparam string ALARM_STR = "Alert\aSound"; 
    localparam string FORMFEED_STR = "Page\fBreak"; 
    localparam string VERT_TAB_STR = "Vert\vTab";   
    localparam string HEX_STR = "Hex values: \x41\x42\x43"; 
    localparam string OCTAL_STR = "Octal values: \101\102\103"; 
    localparam string BACKSLASH_STR = "Path\\\\Separator"; 
    localparam string QUOTE_STR = "Quotes\"in\"string"; 
    localparam string PERCENT_STR = "Percent%%sign"; 
    localparam string WHITESPACE_STR_1 = "  Leading and trailing whitespace  ";
    localparam string WHITESPACE_STR_2 = "\t\nInternal\t\n  whitespace\r\n";
    string temp_str;
    real temp_real;
    logic temp_printable;
    always_comb begin
        string combined_str;
        temp_printable = 1'b1;
        combined_str = NL_STR + TAB_STR + CR_STR + ALARM_STR + FORMFEED_STR + VERT_TAB_STR +
                       HEX_STR + OCTAL_STR + BACKSLASH_STR + QUOTE_STR + PERCENT_STR;
        combined_str = combined_str + WHITESPACE_STR_1 + WHITESPACE_STR_2;
        out_processed_string = combined_str;
        $sscanf("3.14159_265", "%g", temp_real); 
        out_num_val = temp_real;
        string unprintable_check_str = {"Test", 8'h01, "StringWithNonPrintable"}; 
        out_is_printable_all = (unprintable_check_str.len() > 0); 
        out_processed_string = {out_processed_string, in_char_val};
    end
endmodule
module SvStringManipulationFunctions (
    input string in_str_manip,
    input logic in_replace_flag,
    output string out_lower,
    output string out_upper,
    output string out_replaced,
    output logic out_starts,
    output logic out_ends
);
    always_comb begin
        string temp_str = in_str_manip;
        out_lower = temp_str.tolower();
        out_upper = temp_str.toupper();
        if (in_replace_flag) begin
            out_replaced = temp_str.replace("Test", "REPLACE_WORD"); 
            out_replaced = out_replaced.replace("string", "NEW_STR");  
        end else begin
            out_replaced = temp_str.replace("apple", "banana"); 
        end
        out_starts = temp_str.starts_with("Verilog");
        if (!out_starts) out_starts = temp_str.starts_with("Hello"); 
        out_ends = temp_str.ends_with("World");
        if (!out_ends) out_ends = temp_str.ends_with("END"); 
    end
endmodule
module LongIdentifierStressTest_With_A_Ridiculously_Long_And_Descriptive_Name_To_Ensure_Hashing_Is_Activated_For_This_Module_And_Its_Internals_1234567890abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_Extra_Long_Name_To_Trigger_Maximum_Hash_Coverage_And_Dehashing_Upon_Reverse_Lookup (
    input logic [31:0] very_very_very_long_input_signal_name_to_force_verilator_internal_name_mangling_and_hashing_and_string_operations_0123456789ABCDEF0123456789ABCDEF_This_Input_Name_Is_Intentionally_Made_Extremely_Long_For_Hashing_Tests_XYZ_Test_Case,
    output logic [31:0] extremely_long_output_signal_name_designed_to_hit_vname_dehash_and_sha256_digests_AABBCCDD_1234567890abcdef_This_Output_Name_Also_Needs_To_Be_Very_Long_To_Ensure_Full_Coverage_Of_Naming_Mechanisms
);
    parameter string LONG_PATH_PARAM_WITH_MANY_SPACES_AND_BACKSLASHES_AND_FORWARDS_SLASHES_AND_SPECIAL_CHARS_TO_EXERCISE_PATH_STRING_HANDLING = "C:\\Program Files\\My Application\\Configurations\\UserData\\Project Files\\Subproject\\DeepFolder\\EvenMoreFolders\\Final_Output_Directory\\Generated_Code_Results_2024_03_15\\Very_Important_Report_v1.0.txt";
    logic [63:0] this_is_an_extremely_long_internal_variable_name_to_stress_verilators_internal_symbol_table_and_hashing_mechanisms_for_local_scope_variables_XYZABC123_Another_Long_Variable_To_Force_Hashing_And_Dehashing;
    typedef struct packed {
        logic [7:0] data;
        logic enable;
    } extremely_long_typedef_name_for_a_structure_to_test_compiler_limits_and_hashing_for_user_defined_types_STRUCT_TYPE_001_And_This_Is_Even_Longer_For_Type_Hashing;
    extremely_long_typedef_name_for_a_structure_to_test_compiler_limits_and_hashing_for_user_defined_types_STRUCT_TYPE_001_And_This_Is_Even_Longer_For_Type_Hashing instance_of_long_struct_type_for_test;
    always_comb begin
        extremely_long_output_signal_name_designed_to_hit_vname_dehash_and_sha256_digests_AABBCCDD_1234567890abcdef_This_Output_Name_Also_Needs_To_Be_Very_Long_To_Ensure_Full_Coverage_Of_Naming_Mechanisms = very_very_very_long_input_signal_name_to_force_verilator_internal_name_mangling_and_hashing_and_string_operations_0123456789ABCDEF0123456789ABCDEF_This_Input_Name_Is_Intentionally_Made_Extremely_Long_For_Hashing_Tests_XYZ_Test_Case;
        this_is_an_extremely_long_internal_variable_name_to_stress_verilators_internal_symbol_table_and_hashing_mechanisms_for_local_scope_variables_XYZABC123_Another_Long_Variable_To_Force_Hashing_And_Dehashing = {64'hFEEDFACE_DEADC0DE};
        string temp_long_path_str = LONG_PATH_PARAM_WITH_MANY_SPACES_AND_BACKSLASHES_AND_FORWARDS_SLASHES_AND_SPECIAL_CHARS_TO_EXERCISE_PATH_STRING_HANDLING;
        instance_of_long_struct_type_for_test.data = very_very_very_long_input_signal_name_to_force_verilator_internal_name_mangling_and_hashing_and_string_operations_0123456789ABCDEF0123456789ABCDEF_This_Input_Name_Is_Intentionally_Made_Extremely_Long_For_Hashing_Tests_XYZ_Test_Case[7:0];
        instance_of_long_struct_type_for_test.enable = very_very_very_long_input_signal_name_to_force_verilator_internal_name_mangling_and_hashing_and_string_operations_0123456789ABCDEF0123456789ABCDEF_This_Input_Name_Is_Intentionally_Made_Extremely_Long_For_Hashing_Tests_XYZ_Test_Case[8];
    end
endmodule
module PathStringEscapingTest (
    input string in_filename_raw,
    output string out_filename_escaped
);
    parameter string TEST_PATH_1 = "C:\\Program Files\\My App\\folder\\file.txt"; 
    parameter string TEST_PATH_2 = "/usr/local/bin/script.sh"; 
    parameter string TEST_PATH_3 = "Folder Name With Spaces"; 
    parameter string TEST_PATH_4 = "No_Special_Chars.txt"; 
    parameter string TEST_PATH_5 = "Already\\\\Escaped\\\\Path"; 
    parameter string TEST_PATH_6 = "Folder\\With\\Single\\Backslash"; 
    parameter string TEST_PATH_7 = "Another Path With Space and\\Backslash.txt"; 
    string current_path;
    always_comb begin
        case (in_filename_raw)
            "path1": current_path = TEST_PATH_1;
            "path2": current_path = TEST_PATH_2;
            "path3": current_path = TEST_PATH_3;
            "path4": current_path = TEST_PATH_4;
            "path5": current_path = TEST_PATH_5;
            "path6": current_path = TEST_PATH_6;
            "path7": current_path = TEST_PATH_7;
            default: current_path = "default string with spaces and \\back\\slashes\\for\\testing.txt";
        endcase
        out_filename_escaped = current_path;
    end
endmodule
