module case_unique0_violating_mod (
    input logic [1:0] case_expr,
    output logic [4:0] internal_out
);
    always @* begin
        unique0 casez (case_expr)
            2'b1?: internal_out = 8;
            2'b11: internal_out = 9;  
            2'b?1: internal_out = 10; 
            2'b00: internal_out = 11; 
        endcase
    end
endmodule

module case_unique_casez_reordered_mod (
    input logic [1:0] case_expr,
    input logic [3:0] case_inside_val,
    output logic [4:0] internal_out
);
    always @* begin
        unique casez ({case_expr[0], case_inside_val[3:2], case_expr[1]})
            4'b1?0?: internal_out = 30;
            4'b?101: internal_out = 31;  
            4'b0?1?: internal_out = 32;
            4'b1?1?: internal_out = 33;  
            4'b?111: internal_out = 34;  
        endcase
    end
endmodule

module loop_with_internal_assign (
    input logic [3:0] start_val,
    output logic [7:0] final_val
);
    logic [7:0] current_val;
    always_comb begin
        current_val = start_val;
        for (int k = 0; k < 3; k = k + 1) begin
            current_val = current_val + 1;
        end
        final_val = current_val;
    end
endmodule

module module_concat_if (
    input wire [3:0] in_a,
    input wire [3:0] in_b,
    input wire [7:0] in_c,
    input wire in_cond_if,
    output logic [15:0] out_concat,
    output logic [7:0] out_if_else
);
    always_comb begin
    out_concat = {in_a, in_b, in_c};
    if (in_cond_if) begin
        out_if_else = in_c;
    end else begin
        out_if_else = {in_a, in_b};
    end
    end
endmodule

module procedural_complex (
    input logic [15:0] in1,
    input logic [15:0] in2,
    input logic sel,
    output logic [15:0] out1,
    output logic [15:0] out2
);
    logic [15:0] temp1;
    logic [15:0] temp2;
    always_comb begin
        temp1 = (in1 + in2) * 10;
        if (sel) begin
            temp2 = temp1 ^ (in1 >>> 2);
            out1 = temp2 & in2;
        end else begin
            temp2 = temp1 | (in2 <<< 3);
            out1 = temp2 + in1;
        end
        out2 = temp1 - temp2;
    end
endmodule

module snippet (
    input wire clk,
    input logic [1:0] inj_case_expr_1755007859036_752,
    input logic [3:0] inj_case_inside_val_1755007859036_566,
    input logic inj_in1_1755007859045_421,
    input logic inj_in2_1755007859045_729,
    input logic [15:0] inj_in2_1755007859049_582,
    input logic [7:0] inj_in_1755007859036_140,
    input wire [3:0] inj_in_a_1755007859042_542,
    input wire [3:0] inj_in_b_1755007859042_515,
    input wire [7:0] inj_in_data_1755007859040_106,
    input logic [15:0] inj_packed_in_1755007859039_174,
    input wire reset,
    output logic [7:0] inj_field2_o_1755007859039_712,
    output logic [7:0] inj_final_val_1755007859044_232,
    output logic [4:0] inj_internal_out_1755007859036_935,
    output logic [4:0] inj_internal_out_1755007859047_229,
    output wire inj_o_c_1755007859036_338,
    output logic inj_out1_1755007859045_862,
    output logic [15:0] inj_out1_1755007859049_61,
    output logic inj_out2_1755007859045_558,
    output logic [15:0] inj_out2_1755007859049_792,
    output logic [7:0] inj_out_1755007859036_136,
    output logic [15:0] inj_out_concat_1755007859042_542,
    output wire [7:0] inj_out_data_1755007859040_978,
    output logic [7:0] inj_out_if_else_1755007859042_537,
    output logic [7:0] inj_out_val_1755007859038_563,
    output logic [3:0] inj_test_case_result_1755007859036_16
);
    // BEGIN: module_simple_ts1755007859036
    wire internal_xor_res_ts1755007859036;
        // BEGIN: simple_comb_ts1755007859041
        wire [7:0] intermediate_a_ts1755007859041;
        wire [7:0] intermediate_b_ts1755007859041;
        wire [7:0] intermediate_c_ts1755007859041;
            procedural_complex procedural_complex_inst_1755007859049_3671 (
                .in1(inj_packed_in_1755007859039_174),
                .in2(inj_in2_1755007859049_582),
                .sel(inj_in2_1755007859045_729),
                .out1(inj_out1_1755007859049_61),
                .out2(inj_out2_1755007859049_792)
            );
            case_unique0_violating_mod case_unique0_violating_mod_inst_1755007859047_160 (
                .internal_out(inj_internal_out_1755007859047_229),
                .case_expr(inj_case_expr_1755007859036_752)
            );
            // BEGIN: module_unpacked_array_ts1755007859046
            logic [1:0] data_ua[0:1] ;
            always_comb begin
                data_ua[0][0] = inj_in1_1755007859045_421;
                data_ua[0][1] = inj_in2_1755007859045_729;
                data_ua[1][0] = data_ua[0][0];
                data_ua[1][1] = ~data_ua[0][1];
            end
            assign inj_out1_1755007859045_862 = data_ua[1][0];
            assign inj_out2_1755007859045_558 = data_ua[1][1];
            // END: module_unpacked_array_ts1755007859046

            loop_with_internal_assign loop_with_internal_assign_inst_1755007859044_4238 (
                .start_val(inj_case_inside_val_1755007859036_566),
                .final_val(inj_final_val_1755007859044_232)
            );
            module_concat_if module_concat_if_inst_1755007859042_3891 (
                .in_c(intermediate_b_ts1755007859041),
                .in_cond_if(reset),
                .out_concat(inj_out_concat_1755007859042_542),
                .out_if_else(inj_out_if_else_1755007859042_537),
                .in_a(inj_in_a_1755007859042_542),
                .in_b(inj_in_b_1755007859042_515)
            );
        assign intermediate_a_ts1755007859041 = inj_in_data_1755007859040_106 + 8'd1;
        assign intermediate_b_ts1755007859041 = intermediate_a_ts1755007859041 << 1;
        assign intermediate_c_ts1755007859041 = intermediate_a_ts1755007859041 >> 1;
        assign inj_out_data_1755007859040_978 = intermediate_b_ts1755007859041 | intermediate_c_ts1755007859041;
        // END: simple_comb_ts1755007859041

        // BEGIN: typedef_struct_mod_ts1755007859039
        typedef struct packed {
            logic [7:0] field1_ts1755007859039;
            logic [7:0] field2_ts1755007859039;
        } my_packed_struct_t;
        my_packed_struct_t my_struct_var;
        always_comb begin
            my_struct_var = inj_packed_in_1755007859039_174;
        end
        assign inj_field2_o_1755007859039_712 = my_struct_var.field2_ts1755007859039;
        // END: typedef_struct_mod_ts1755007859039

        // BEGIN: generic_class_scope_diag_mod_ts1755007859038
        assign inj_out_val_1755007859038_563 = inj_in_1755007859036_140;
        // END: generic_class_scope_diag_mod_ts1755007859038

        // BEGIN: PragmaSyntaxVariety_ts1755007859037
    `ifdef SLANG_PRAGMA
    `unknown_pragma_real 1.23;
    `endif
    `ifdef SLANG_PRAGMA
    `unknown_slang_pragma (arg1, arg2="value")
    `endif
    `ifdef SLANG_PRAGMA
    `protect (1 + 2)
    `endif
    `ifdef SLANG_PRAGMA
    `protect {3, 4}
    `endif
    `ifdef SLANG_PRAGMA
    `protect unknown_action (arg=1)
    `endif
    `ifdef SLANG_PRAGMA
    `protect encoding
    `endif
    `ifdef SLANG_PRAGMA
    `protect encoding (enctype="raw", "string_arg_only")
    `endif
    `ifdef SLANG_PRAGMA
    `protect encoding (enctype="raw", unknown_option=99)
    `endif
    `ifdef SLANG_PRAGMA
    `protect encoding (bytes=-10)
    `endif
    `ifdef SLANG_PRAGMA
    `protect license (match="not_an_integer")
    `endif
    `ifdef SLANG_PRAGMA
    `protect license (match=42.5)
    `endif
    `ifdef SLANG_PRAGMA
    `protect viewport (obj="a", acc="b", extra=1)
    `endif
    `ifdef SLANG_PRAGMA
    `protect begin (arg_present)
    `endif
    `ifdef SLANG_PRAGMA
    `protect license ("license_string_only")
    `endif
    `ifdef SLANG_PRAGMA
    `protect license (library=my_library_ident)
    `endif
    `ifdef SLANG_PRAGMA
    `protect viewport (obj="a")
    `endif
    `ifdef SLANG_PRAGMA
    `protect viewport (obj="a", acc="b", c=3)
    `endif
    `ifdef SLANG_PRAGMA
    `protect viewport (obj="a", "access_string")
    `endif
    `ifdef SLANG_PRAGMA
    `protect viewport ("object_string", acc="b")
    `endif
    `ifdef SLANG_PRAGMA
    `protect viewport (object="a", access=123)
    `endif
    `ifdef SLANG_PRAGMA
    `protect viewport (object=123, access="b")
    `endif
    `ifdef SLANG_PRAGMA
    `protect viewport (not_object="a", access="b")
    `endif
    `ifdef SLANG_PRAGMA
    `protect viewport (object="a", not_access="b")
    `endif
    `ifdef SLANG_PRAGMA
    `diagnostic (1 + 2)
    `endif
    `ifdef SLANG_PRAGMA
    `diagnostic unknown_action_diag
    `endif
    `ifdef SLANG_PRAGMA
    `diagnostic level=warn
    `endif
    `ifdef SLANG_PRAGMA
    `diagnostic ignore (value=(1+2))
    `endif
    `ifdef SLANG_PRAGMA
    `diagnostic ignore (value=(value=1))
    `endif
    `ifdef SLANG_PRAGMA
    `diagnostic ignore (value=some_identifier)
    `endif
    `ifdef SLANG_PRAGMA
    `diagnostic warn (value=12345)
    `endif
    `ifdef SLANG_PRAGMA
    `diagnostic ignore simple_identifier_arg
    `endif
    `ifdef SLANG_PRAGMA
    `protect "simple_string_argument"
    `endif
    `ifdef SLANG_PRAGMA
    `diagnostic ignore "just_a_string_diag_code"
    `endif
    assign inj_test_case_result_1755007859036_16 = (inj_case_expr_1755007859036_752 == 2'b01) ? 4'h5 : 4'hA;
        // END: PragmaSyntaxVariety_ts1755007859037

        // BEGIN: timed_assign_unhandled_ts1755007859036
        always @(posedge clk) begin
            inj_out_1755007859036_136 <= inj_in_1755007859036_140;
        end
        // END: timed_assign_unhandled_ts1755007859036

        case_unique_casez_reordered_mod case_unique_casez_reordered_mod_inst_1755007859036_2839 (
            .internal_out(inj_internal_out_1755007859036_935),
            .case_expr(inj_case_expr_1755007859036_752),
            .case_inside_val(inj_case_inside_val_1755007859036_566)
        );
    assign internal_xor_res_ts1755007859036 = reset ^ clk;
    assign inj_o_c_1755007859036_338 = internal_xor_res_ts1755007859036 & reset;
    // END: module_simple_ts1755007859036
endmodule

