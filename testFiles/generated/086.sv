module MiscExpressions_ValueRange (
    input logic [15:0] in_vector,
    output logic [7:0] out_slice
);
    always_comb begin
        out_slice = in_vector[7:0];
    end
endmodule

module case_basic (
    input logic [1:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        case (in_val)
            2'b00: out_res = 1'b0;
            2'b01: out_res = 1'b1;
            2'b10: out_res = 1'b0;
            2'b11: out_res = 1'b1;
        endcase
    end
endmodule

module member_access_packed_union (
    input logic [31:0] in_val,
    input bit select_a,
    output logic [31:0] out_val
);
    typedef union packed {
        logic [31:0] a; 
        logic [31:0] b; 
    } my_packed_union;
    my_packed_union union_var;
    always_comb begin
        if (select_a)
            union_var.a = in_val;
        else
            union_var.b = in_val[31:0];
        out_val = union_var.a;
    end
endmodule

module mod_case_standard (
    input bit [7:0] in_cmd,
    output bit [3:0] out_status
);
always_comb begin
    case (in_cmd)
        8'd0, 8'd1, 8'd2: begin
            out_status = 4'hA;
        end
        8'd3, 8'd4: begin
            out_status = 4'hB;
        end
        default: begin
            out_status = 4'hF;
        end
    endcase
end
endmodule

module mod_split_case (
    input logic [7:0] data_in,
    input logic [1:0] sel,
    output logic [7:0] out_case_a,
    output logic [7:0] out_case_b
);
    logic [7:0]  split_case_var;
    logic [7:0] other_case_var;
    always_comb begin
        split_case_var = 8'hFF;
        other_case_var = 8'hAA;
        case (sel)
            2'b00: begin
                split_case_var = data_in + 5;
                other_case_var = data_in + 6;
            end
            2'b01: begin
                split_case_var = data_in - 5;
                other_case_var = data_in - 6;
            end
            default: begin
                split_case_var = data_in;
                other_case_var = data_in;
            end
        endcase
        out_case_a = split_case_var;
        out_case_b = other_case_var;
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_c3_x_1755007780911_908,
    input logic [1:0] inj_case_expr_1755007780906_59,
    input logic [3:0] inj_case_inside_val_1755007780906_885,
    input int inj_config_data_in_1755007780909_859,
    input logic [7:0] inj_data_in_1755007780906_612,
    input logic [15:0] inj_in_1755007780933_983,
    input bit [7:0] inj_in_cmd_1755007780906_83,
    input logic [31:0] inj_in_val_1755007780907_860,
    input logic [31:0] inj_p_in2_1755007780929_910,
    input logic inj_p_in_1755007780907_231,
    input bit inj_select_a_1755007780907_85,
    input logic [2:0] inj_selector_1755007780910_127,
    input logic [7:0] inj_v1_x_1755007780911_679,
    input logic [7:0] inj_v3_x_1755007780911_458,
    input logic [63:0] inj_wide_a_1755007780908_166,
    input logic [63:0] inj_wide_b_1755007780908_727,
    input logic [63:0] inj_wide_c_1755007780908_960,
    input wire reset,
    output int inj_config_data_out_1755007780909_970,
    output logic [7:0] inj_data_out_1755007780906_820,
    output logic inj_data_out_1755007780926_230,
    output logic [4:0] inj_internal_out_1755007780906_889,
    output logic [4:0] inj_internal_out_1755007780908_479,
    output logic inj_o_out_1755007780947_799,
    output int inj_o_val_1755007780914_348,
    output wire inj_out_1755007780910_453,
    output logic [15:0] inj_out_1755007780933_138,
    output logic [7:0] inj_out_case_a_1755007780920_315,
    output logic [7:0] inj_out_case_b_1755007780920_75,
    output logic inj_out_la_1755007780917_751,
    output reg inj_out_res_1755007780907_662,
    output reg inj_out_res_1755007780913_719,
    output reg inj_out_res_1755007780941_372,
    output logic [7:0] inj_out_slice_1755007780937_550,
    output bit [3:0] inj_out_status_1755007780906_761,
    output logic [7:0] inj_out_v_1755007780923_637,
    output logic [31:0] inj_out_val_1755007780907_989,
    output logic [7:0] inj_out_x_1755007780911_122,
    output wire inj_p_out_1755007780907_380,
    output logic [31:0] inj_p_out_1755007780929_478,
    output logic [3:0] inj_result_out_1755007780910_747,
    output logic [63:0] inj_wide_out_1755007780908_739
);
    // BEGIN: case_unique_casez_reordered_mod_ts1755007780906
    // BEGIN: SequentialLogic_ts1755007780907
    logic [7:0] internal_reg_ts1755007780907;
        // BEGIN: explicit_non_ansi_decl_module_ts1755007780907
        input logic inj_p_in_1755007780907_231_ts1755007780907;
        output wire inj_p_out_1755007780907_380_ts1755007780907;
            // BEGIN: mod_automatic_task_ts1755007780914
            task automatic update_val(input int in_v, output int out_v);
                out_v = in_v * 2;
            endtask
            always_comb begin
                int temp_val_ts1755007780914;
                    // BEGIN: extern_declarations_ts1755007780947
                    assign inj_o_out_1755007780947_799 = inj_p_in_1755007780907_231;
                    // END: extern_declarations_ts1755007780947

                    // BEGIN: case_empty_statement_ts1755007780941
                    always_comb begin
                        inj_out_res_1755007780941_372 = 1'b0;
                        case (inj_case_expr_1755007780906_59)
                            2'b00: inj_out_res_1755007780941_372 = 1'b1;
                            2'b01: ;
                            2'b10: inj_out_res_1755007780941_372 = 1'b0;
                            default: inj_out_res_1755007780941_372 = 1'b1;
                        endcase
                    end
                    // END: case_empty_statement_ts1755007780941

                    MiscExpressions_ValueRange MiscExpressions_ValueRange_inst_1755007780937_892 (
                        .in_vector(inj_in_1755007780933_983),
                        .out_slice(inj_out_slice_1755007780937_550)
                    );
                    // BEGIN: always_comb_assign_ts1755007780933
                    always_comb begin
                        inj_out_1755007780933_138 = inj_in_1755007780933_983;
                    end
                    // END: always_comb_assign_ts1755007780933

                    // BEGIN: more_procedural_ts1755007780929
                    always_comb begin
                        case (inj_case_expr_1755007780906_59)
                            2'b00: inj_p_out_1755007780929_478 = (inj_in_val_1755007780907_860 + inj_p_in2_1755007780929_910) * 2;
                            2'b01: inj_p_out_1755007780929_478 = (inj_in_val_1755007780907_860 - inj_p_in2_1755007780929_910) / 3; 
                            2'b10: inj_p_out_1755007780929_478 = (inj_in_val_1755007780907_860 << 4) | (inj_p_in2_1755007780929_910 >> 2);
                            default: inj_p_out_1755007780929_478 = ~(inj_in_val_1755007780907_860 ^ inj_p_in2_1755007780929_910) + 1;
                        endcase
                    end
                    // END: more_procedural_ts1755007780929

                    // BEGIN: sequential_register_ts1755007780926
                    always_ff @(posedge clk or negedge reset) begin
                        if (!reset) begin
                            inj_data_out_1755007780926_230 <= 1'b0; 
                        end else if (inj_p_in_1755007780907_231) begin
                            inj_data_out_1755007780926_230 <= inj_p_in_1755007780907_231_ts1755007780907; 
                        end
                    end
                    // END: sequential_register_ts1755007780926

                    // BEGIN: ModVectorAdd_ts1755007780923
                    assign inj_out_v_1755007780923_637 = internal_reg_ts1755007780907 + 8'h01;
                    // END: ModVectorAdd_ts1755007780923

                    mod_split_case mod_split_case_inst_1755007780920_5171 (
                        .sel(inj_case_expr_1755007780906_59),
                        .out_case_a(inj_out_case_a_1755007780920_315),
                        .out_case_b(inj_out_case_b_1755007780920_75),
                        .data_in(internal_reg_ts1755007780907)
                    );
                    // BEGIN: mod_large_array_target_ts1755007780917
                    assign inj_out_la_1755007780917_751 = inj_p_in_1755007780907_231_ts1755007780907;
                    // END: mod_large_array_target_ts1755007780917

                update_val(inj_config_data_in_1755007780909_859, temp_val_ts1755007780914);
                inj_o_val_1755007780914_348 = temp_val_ts1755007780914;
            end
            // END: mod_automatic_task_ts1755007780914

            // BEGIN: case_default_ts1755007780913
            always_comb begin
                inj_out_res_1755007780913_719 = 1'b0;
                case (inj_case_expr_1755007780906_59)
                    2'b01: inj_out_res_1755007780913_719 = 1'b1;
                    2'b10: inj_out_res_1755007780913_719 = 1'b0;
                    default: inj_out_res_1755007780913_719 = 1'b1;
                endcase
            end
            // END: case_default_ts1755007780913

            // BEGIN: split_ifelse_chain_ts1755007780912
            always @(posedge clk) begin
                if (inj_p_in_1755007780907_231) begin
                    inj_out_x_1755007780911_122 <= inj_v1_x_1755007780911_679;
                end else if (inj_p_in_1755007780907_231_ts1755007780907) begin
                    inj_out_x_1755007780911_122 <= inj_data_in_1755007780906_612;
                end else if (inj_c3_x_1755007780911_908) begin
                    inj_out_x_1755007780911_122 <= inj_v3_x_1755007780911_458;
                end else begin
                    inj_out_x_1755007780911_122 <= internal_reg_ts1755007780907;
                end
            end
            // END: split_ifelse_chain_ts1755007780912

            // BEGIN: rand_case_mod_ts1755007780910
            always_comb begin
                case (inj_selector_1755007780910_127)
                    0: inj_result_out_1755007780910_747 = 4'h0;
                    1: inj_result_out_1755007780910_747 = 4'h1;
                    2: inj_result_out_1755007780910_747 = 4'hA;
                    default: inj_result_out_1755007780910_747 = 4'hF;
                endcase
            end
            // END: rand_case_mod_ts1755007780910

            // BEGIN: mod_simple_ts1755007780910
            assign inj_out_1755007780910_453 = inj_p_out_1755007780907_380_ts1755007780907;
            // END: mod_simple_ts1755007780910

            // BEGIN: PragmaProtectOptions_ts1755007780909
        `ifdef SLANG_PRAGMA
        `protect encoding (enctype="base64", line_length=76, bytes=1024)
        `endif
        `ifdef SLANG_PRAGMA
        `protect license (library="my_project_lib", entry="start_feature_A", match=42, feature="feature_set_B", exit="end_feature_A")
        `endif
        `ifdef SLANG_PRAGMA
        `protect reset
        `endif
        `ifdef SLANG_PRAGMA
        `protect viewport (object="design.module_a.instance_b.register_c", access="read-only")
        `endif
        assign inj_config_data_out_1755007780909_970 = inj_config_data_in_1755007780909_859 + 1;
            // END: PragmaProtectOptions_ts1755007780909

            // BEGIN: wide_ops_deep_ts1755007780908
            assign inj_wide_out_1755007780908_739 = (((inj_wide_a_1755007780908_166 + inj_wide_b_1755007780908_727) ^ inj_wide_c_1755007780908_960) & (~inj_wide_a_1755007780908_166 | inj_wide_b_1755007780908_727)) + (inj_wide_c_1755007780908_960 >>> 5);
            // END: wide_ops_deep_ts1755007780908

            // BEGIN: case_parallel_simple_mod_ts1755007780908
            always @* begin
                (* parallel *)
                case (inj_case_inside_val_1755007780906_885)
                    4'd0, 4'd1: inj_internal_out_1755007780908_479 = 14;
                    4'd2, 4'd3: inj_internal_out_1755007780908_479 = 15;
                    default: inj_internal_out_1755007780908_479 = 18;
                endcase
            end
            // END: case_parallel_simple_mod_ts1755007780908

            case_basic case_basic_inst_1755007780907_4792 (
                .in_val(inj_case_expr_1755007780906_59),
                .out_res(inj_out_res_1755007780907_662)
            );
            member_access_packed_union member_access_packed_union_inst_1755007780907_331 (
                .in_val(inj_in_val_1755007780907_860),
                .select_a(inj_select_a_1755007780907_85),
                .out_val(inj_out_val_1755007780907_989)
            );
        assign inj_p_out_1755007780907_380_ts1755007780907 = inj_p_in_1755007780907_231_ts1755007780907;
        // END: explicit_non_ansi_decl_module_ts1755007780907

    always @(posedge clk or negedge reset) begin
        if (~reset) begin
            internal_reg_ts1755007780907 <= 8'h00;
        end else begin
            internal_reg_ts1755007780907 <= inj_data_in_1755007780906_612;
        end
    end
    assign inj_data_out_1755007780906_820 = internal_reg_ts1755007780907;
    // END: SequentialLogic_ts1755007780907

    mod_case_standard mod_case_standard_inst_1755007780906_4021 (
        .in_cmd(inj_in_cmd_1755007780906_83),
        .out_status(inj_out_status_1755007780906_761)
    );
    always @* begin
        unique casez ({inj_case_expr_1755007780906_59[0], inj_case_inside_val_1755007780906_885[3:2], inj_case_expr_1755007780906_59[1]})
            4'b1?0?: inj_internal_out_1755007780906_889 = 30;
            4'b?101: inj_internal_out_1755007780906_889 = 31;  
            4'b0?1?: inj_internal_out_1755007780906_889 = 32;
            4'b1?1?: inj_internal_out_1755007780906_889 = 33;  
            4'b?111: inj_internal_out_1755007780906_889 = 34;  
        endcase
    end
    // END: case_unique_casez_reordered_mod_ts1755007780906
endmodule

