interface simple_if (
    input logic clk
);
    logic data;
    logic ready;
    modport master (output data, input ready);
    modport slave (input data, output ready);
endinterface
module LintLatch (
    input logic in_j,
    input logic in_k,
    output logic out_l
);
    always_comb begin
        if (in_j) begin
            out_l = in_k;
        end else begin
            out_l = 1'b0; 
        end
    end
endmodule

module LintParamUnused #(
    parameter integer UNUSED_PARAM = 8
) (
    input logic in_m,
    output logic out_n
);
    assign out_n = in_m;
endmodule

module ModuleBasic (
    input logic a,
    input int b,
    output logic out_a,
    output int out_b
);
    parameter int P1  = 10;
    localparam int LP1 = 20;
    logic c;
    int   d;
    always_comb begin
        logic temp_v;
        temp_v = d;
        c      = temp_v;
    end
    assign out_a = a;
    assign d     = b;
    assign out_b = d + P1 + LP1;
endmodule

module Module_ConfigKeywords (
    input bit cfg_in,
    output bit cfg_out
);
    assign cfg_out = cfg_in;
endmodule

module case_priority_casex_complex_mod (
    input logic [1:0] case_expr,
    input logic [3:0] case_inside_val,
    output logic [4:0] internal_out
);
    always @* begin
        priority casex ({case_expr, case_inside_val[1:0]})
            4'b1???: internal_out = 24;
            4'b?1??: internal_out = 25;  
            4'b??1?: internal_out = 26;  
            4'b???1: internal_out = 27;  
            4'b0000: internal_out = 28;  
            default: internal_out = 29;
        endcase
    end
endmodule

module child_packed_scalar_port (
    input logic [3:0] data_in,
    output logic [3:0] data_out
);
    assign data_out = data_in;
endmodule

module non_ansi_concat_port (
    concat_port_input,
    concat_port_output,
    non_ansi_i,
    non_ansi_j
);
    output logic [1:0] non_ansi_i;
    output logic [1:0] non_ansi_j;
    input logic concat_port_input;
    output logic concat_port_output;
    assign non_ansi_i = 2'b10;
    assign non_ansi_j = 2'b01;
    assign concat_port_output = concat_port_input;
endmodule

module simple_adder (
    input logic a,
    input logic b,
    output logic sum
);
    assign sum = a + b;
endmodule

module split_case (
    input logic clk_w,
    input logic [7:0] d0_w,
    input logic [7:0] d1_w,
    input logic [7:0] d2_w,
    input logic [7:0] d3_w,
    input logic [1:0] sel_w,
    output logic [7:0] out_w
);
    always @(posedge clk_w) begin
        case (sel_w)
            2'b00: out_w <= d0_w;
            2'b01: out_w <= d1_w;
            2'b10: out_w <= d2_w;
            default: out_w <= d3_w;
        endcase
    end
endmodule

module sub_module (
    input logic sub_in,
    output logic sub_out
);
    assign sub_out = !sub_in;
endmodule

module snippet (
    input wire clk,
    input logic inj_a_1755007824201_862,
    input logic inj_b_1755007824201_547,
    input logic [15:0] inj_data0_1755007824245_726,
    input logic [15:0] inj_data1_1755007824245_187,
    input logic [7:0] inj_data_in_1755007824202_568,
    input logic [3:0] inj_data_in_1755007824208_105,
    input wire [1:0] inj_i_sel_1755007824220_699,
    input wire [3:0] inj_i_val_1755007824220_3,
    input bit inj_in_tc_1755007824201_360,
    input int inj_in_val_1755007824206_731,
    input logic [1:0] inj_in_val_1755007824210_385,
    input logic [2:0] inj_in_val_1755007824269_90,
    input wire [15:0] inj_value1_1755007824202_863,
    input wire [15:0] inj_value2_1755007824202_518,
    input wire reset,
    output bit inj_cfg_out_1755007824227_908,
    output logic inj_concat_port_output_1755007824264_162,
    output logic [7:0] inj_data_a_out_task_1755007824275_104,
    output logic [7:0] inj_data_b_out_task_1755007824275_548,
    output logic [3:0] inj_data_out_1755007824208_672,
    output int inj_data_out_1755007824240_742,
    output logic [15:0] inj_data_out_1755007824245_628,
    output reg [3:0] inj_data_out_1755007824250_754,
    output logic [7:0] inj_field2_o_1755007824281_26,
    output logic [4:0] inj_internal_out_1755007824212_847,
    output logic [4:0] inj_internal_out_1755007824259_561,
    output logic inj_main_out_1755007824247_994,
    output logic [1:0] inj_non_ansi_i_1755007824264_361,
    output logic [1:0] inj_non_ansi_j_1755007824264_453,
    output logic [3:0] inj_o_out_1755007824220_846,
    output logic inj_out_a_1755007824231_541,
    output int inj_out_b_1755007824231_472,
    output logic inj_out_h_1755007824235_74,
    output logic inj_out_l_1755007824203_167,
    output logic inj_out_n_1755007824209_423,
    output logic [7:0] inj_out_p_g_1755007824207_766,
    output logic [7:0] inj_out_q_g_1755007824207_786,
    output logic [7:0] inj_out_reg_a_1755007824202_988,
    output logic [7:0] inj_out_reg_b_1755007824202_187,
    output reg inj_out_res_1755007824210_566,
    output reg inj_out_res_1755007824238_553,
    output reg inj_out_res_1755007824269_674,
    output bit inj_out_tc_1755007824201_444,
    output bit inj_out_tc_1755007824204_695,
    output int inj_out_val_1755007824206_612,
    output int inj_out_val_1755007824242_988,
    output logic [7:0] inj_out_w_1755007824213_76,
    output logic [7:0] inj_result1_1755007824217_797,
    output logic [7:0] inj_result2_1755007824217_906,
    output reg [15:0] inj_result_val_1755007824202_359,
    output logic inj_sub_out_1755007824215_76,
    output logic inj_sub_out_1755007824254_989,
    output logic inj_sum_1755007824201_77,
    output bit inj_system_status_clear_1755007824224_119
);
    // BEGIN: TopConfigExample_ts1755007824201
    // BEGIN: Comb_IfElse_ts1755007824202
    // BEGIN: mod_split_ff_ts1755007824203
    logic [7:0]  split_reg_var_ts1755007824203;
    logic [7:0] other_reg_var_ts1755007824203;
        // BEGIN: split_reorder_blocking_ts1755007824207
        logic [7:0] mid_x_g_ts1755007824207;
        logic [7:0] mid_y_g_ts1755007824207;
            // BEGIN: mod_case_block_attrs_ts1755007824221
            logic [3:0] l_temp_ts1755007824220;
                // BEGIN: module_task_args_ts1755007824277
                logic [7:0] data_a_ts1755007824276 ;
                logic [7:0] data_b_ts1755007824276 ;
                    // BEGIN: typedef_struct_mod_ts1755007824281
                    typedef struct packed {
                        logic [7:0] field1_ts1755007824281;
                        logic [7:0] field2_ts1755007824281;
                    } my_packed_struct_t;
                    my_packed_struct_t my_struct_var;
                    always_comb begin
                        my_struct_var = inj_data0_1755007824245_726;
                    end
                    assign inj_field2_o_1755007824281_26 = my_struct_var.field2_ts1755007824281;
                    // END: typedef_struct_mod_ts1755007824281

                task automatic modify_vars;
                    input logic [7:0] task_arg_ts1755007824276;
                    logic [7:0] task_local_ts1755007824276 ;
                    begin
                        task_local_ts1755007824276 = task_arg_ts1755007824276;
                        data_a_ts1755007824276 = task_local_ts1755007824276 + 8'd1;
                        data_b_ts1755007824276 = task_arg_ts1755007824276 - 8'd1;
                    end
                endtask
                always_comb begin
                    if (inj_a_1755007824201_862) begin
                        data_a_ts1755007824276 = mid_y_g_ts1755007824207;
                        data_b_ts1755007824276 = 8'hFF;
                        modify_vars(mid_x_g_ts1755007824207);
                    end else begin
                        data_a_ts1755007824276 = 8'h00;
                        data_b_ts1755007824276 = 8'h00;
                    end
                end
                always_comb begin
                    inj_data_a_out_task_1755007824275_104 = data_a_ts1755007824276 + 8'd2;
                    inj_data_b_out_task_1755007824275_548 = data_b_ts1755007824276;
                end
                // END: module_task_args_ts1755007824277

                // BEGIN: casez_xz_alt_ts1755007824269
                always_comb begin
                    inj_out_res_1755007824269_674 = 1'b0;
                    casez (inj_in_val_1755007824269_90)
                        3'b1?z: inj_out_res_1755007824269_674 = 1'b1;
                        3'b0z?: inj_out_res_1755007824269_674 = 1'b0;
                        default: inj_out_res_1755007824269_674 = 1'b1;
                    endcase
                end
                // END: casez_xz_alt_ts1755007824269

                non_ansi_concat_port non_ansi_concat_port_inst_1755007824264_4870 (
                    .concat_port_input(inj_b_1755007824201_547),
                    .concat_port_output(inj_concat_port_output_1755007824264_162),
                    .non_ansi_i(inj_non_ansi_i_1755007824264_361),
                    .non_ansi_j(inj_non_ansi_j_1755007824264_453)
                );
                // BEGIN: case_full_simple_mod_ts1755007824259
                always @* begin
                    (* full *)
                    case (inj_in_val_1755007824210_385)
                        2'b00: inj_internal_out_1755007824259_561 = 10;
                        2'b01: inj_internal_out_1755007824259_561 = 11;
                        2'b10: inj_internal_out_1755007824259_561 = 12;
                        default: inj_internal_out_1755007824259_561 = 13;
                    endcase
                end
                // END: case_full_simple_mod_ts1755007824259

                // BEGIN: sub_module_ts1755007824254
                assign inj_sub_out_1755007824254_989 = !inj_b_1755007824201_547;
                // END: sub_module_ts1755007824254

                // BEGIN: mod_event_implicit_ts1755007824250
                always @* begin
                    inj_data_out_1755007824250_754 = inj_i_val_1755007824220_3;
                end
                // END: mod_event_implicit_ts1755007824250

                // BEGIN: hierarchy_if_ts1755007824247
                sub_module u_sub (
                    .sub_in(inj_b_1755007824201_547),
                    .sub_out(inj_main_out_1755007824247_994)
                );
                simple_if if_inst (.clk(clk));
                always_comb begin
                    if_inst.data = inj_b_1755007824201_547;
                    if_inst.ready = inj_main_out_1755007824247_994;
                end
                // END: hierarchy_if_ts1755007824247

                // BEGIN: CombinationalLogicExplicit_ts1755007824245
                always @(inj_a_1755007824201_862 or inj_data0_1755007824245_726 or inj_data1_1755007824245_187) begin
                    if (inj_a_1755007824201_862) begin
                        inj_data_out_1755007824245_628 = inj_data1_1755007824245_187;
                    end else begin
                        inj_data_out_1755007824245_628 = inj_data0_1755007824245_726;
                    end
                end
                // END: CombinationalLogicExplicit_ts1755007824245

                // BEGIN: recursive_param_diag_mod_ts1755007824242
                assign inj_out_val_1755007824242_988 = inj_in_val_1755007824206_731;
                // END: recursive_param_diag_mod_ts1755007824242

                // BEGIN: mod_named_begin_ts1755007824240
                always_comb begin : my_named_block
                    inj_data_out_1755007824240_742 = inj_in_val_1755007824206_731;
                end
                // END: mod_named_begin_ts1755007824240

                // BEGIN: case_basic_ts1755007824238
                always_comb begin
                    inj_out_res_1755007824238_553 = 1'b0;
                    case (inj_in_val_1755007824210_385)
                        2'b00: inj_out_res_1755007824238_553 = 1'b0;
                        2'b01: inj_out_res_1755007824238_553 = 1'b1;
                        2'b10: inj_out_res_1755007824238_553 = 1'b0;
                        2'b11: inj_out_res_1755007824238_553 = 1'b1;
                    endcase
                end
                // END: case_basic_ts1755007824238

                // BEGIN: CoverageHelper_ts1755007824235
                assign inj_out_h_1755007824235_74 = inj_in_tc_1755007824201_360;
                // END: CoverageHelper_ts1755007824235

                ModuleBasic ModuleBasic_inst_1755007824231_183 (
                    .out_b(inj_out_b_1755007824231_472),
                    .a(inj_a_1755007824201_862),
                    .b(inj_in_val_1755007824206_731),
                    .out_a(inj_out_a_1755007824231_541)
                );
                // BEGIN: Module_ConfigKeywords_ts1755007824227
                assign inj_cfg_out_1755007824227_908 = inj_in_tc_1755007824201_360;
                // END: Module_ConfigKeywords_ts1755007824227

                // BEGIN: PragmaResetDirectives_ts1755007824224
            `ifdef SLANG_PRAGMA
            `reset protect diagnostic
            `endif
            assign inj_system_status_clear_1755007824224_119 = reset;
                // END: PragmaResetDirectives_ts1755007824224

            always_comb begin
                (* full_case *)
                (* parallel_case *)
                case (inj_i_sel_1755007824220_699)
                    2'b00: l_temp_ts1755007824220 = inj_i_val_1755007824220_3;
                    2'b01: l_temp_ts1755007824220 = inj_i_val_1755007824220_3 << 1;
                    2'b10: l_temp_ts1755007824220 = inj_i_val_1755007824220_3 >> 1;
                    default: l_temp_ts1755007824220 = 4'bxxxx;
                endcase
                (* coverage_off *)
                begin : my_named_block
                    inj_o_out_1755007824220_846 = l_temp_ts1755007824220;
                end
            end
            // END: mod_case_block_attrs_ts1755007824221

            // BEGIN: dup_cond_ts1755007824218
            always_comb begin
                inj_result1_1755007824217_797 = '0;
                inj_result2_1755007824217_906 = '0;
                if (inj_data_in_1755007824208_105[0]) begin
                    inj_result1_1755007824217_797 = mid_x_g_ts1755007824207 + split_reg_var_ts1755007824203;
                end else begin
                    inj_result1_1755007824217_797 = mid_x_g_ts1755007824207 - split_reg_var_ts1755007824203;
                end
                if (inj_data_in_1755007824208_105[1]) begin
                    inj_result2_1755007824217_906 = mid_x_g_ts1755007824207 - split_reg_var_ts1755007824203;
                end else begin
                    inj_result2_1755007824217_906 = mid_x_g_ts1755007824207 + split_reg_var_ts1755007824203;
                end
                case (inj_data_in_1755007824208_105[3:2])
                    2'b00: inj_result1_1755007824217_797 = mid_x_g_ts1755007824207 & split_reg_var_ts1755007824203;
                    2'b01: inj_result1_1755007824217_797 = mid_x_g_ts1755007824207 | split_reg_var_ts1755007824203;
                    2'b10: inj_result2_1755007824217_906 = mid_x_g_ts1755007824207 & split_reg_var_ts1755007824203;
                    2'b11: inj_result2_1755007824217_906 = mid_x_g_ts1755007824207 | split_reg_var_ts1755007824203;
                    default: begin inj_result1_1755007824217_797 = '0; inj_result2_1755007824217_906 = '0; end
                endcase
                if (inj_data_in_1755007824208_105[0] == inj_data_in_1755007824208_105[1]) begin
                    inj_result1_1755007824217_797 = inj_result1_1755007824217_797 + 1;
                end else if (inj_data_in_1755007824208_105[2] != inj_data_in_1755007824208_105[3]) begin
                    inj_result2_1755007824217_906 = inj_result2_1755007824217_906 - 1;
                end
            end
            // END: dup_cond_ts1755007824218

            // BEGIN: sub_module_ts1755007824215
            assign inj_sub_out_1755007824215_76 = !inj_b_1755007824201_547;
            // END: sub_module_ts1755007824215

            split_case split_case_inst_1755007824213_2378 (
                .clk_w(clk),
                .d0_w(other_reg_var_ts1755007824203),
                .d1_w(inj_data_in_1755007824202_568),
                .d2_w(mid_y_g_ts1755007824207),
                .d3_w(mid_x_g_ts1755007824207),
                .sel_w(inj_in_val_1755007824210_385),
                .out_w(inj_out_w_1755007824213_76)
            );
            case_priority_casex_complex_mod case_priority_casex_complex_mod_inst_1755007824212_784 (
                .case_expr(inj_in_val_1755007824210_385),
                .case_inside_val(inj_data_in_1755007824208_105),
                .internal_out(inj_internal_out_1755007824212_847)
            );
            // BEGIN: case_default_ts1755007824210
            always_comb begin
                inj_out_res_1755007824210_566 = 1'b0;
                case (inj_in_val_1755007824210_385)
                    2'b01: inj_out_res_1755007824210_566 = 1'b1;
                    2'b10: inj_out_res_1755007824210_566 = 1'b0;
                    default: inj_out_res_1755007824210_566 = 1'b1;
                endcase
            end
            // END: case_default_ts1755007824210

            LintParamUnused LintParamUnused_inst_1755007824209_6074 (
                .in_m(inj_b_1755007824201_547),
                .out_n(inj_out_n_1755007824209_423)
            );
            child_packed_scalar_port child_packed_scalar_port_inst_1755007824208_8514 (
                .data_out(inj_data_out_1755007824208_672),
                .data_in(inj_data_in_1755007824208_105)
            );
        always @(*) begin
            mid_x_g_ts1755007824207 = inj_data_in_1755007824202_568 * 2;
            mid_y_g_ts1755007824207 = mid_x_g_ts1755007824207 + split_reg_var_ts1755007824203;
            inj_out_p_g_1755007824207_766 = mid_y_g_ts1755007824207 - 1;
            inj_out_q_g_1755007824207_786 = mid_x_g_ts1755007824207 / 2;
        end
        // END: split_reorder_blocking_ts1755007824207

        // BEGIN: unknown_class_pkg_diag_mod_ts1755007824206
        assign inj_out_val_1755007824206_612 = inj_in_val_1755007824206_731;
        // END: unknown_class_pkg_diag_mod_ts1755007824206

        // BEGIN: TopConfigExample_ts1755007824204
        Module_ConfigKeywords i_cfg (.cfg_in(inj_in_tc_1755007824201_360), .cfg_out(inj_out_tc_1755007824204_695));
        // END: TopConfigExample_ts1755007824204

        LintLatch LintLatch_inst_1755007824203_5490 (
            .in_j(inj_b_1755007824201_547),
            .in_k(inj_a_1755007824201_862),
            .out_l(inj_out_l_1755007824203_167)
        );
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            split_reg_var_ts1755007824203 <= 8'b0;
            other_reg_var_ts1755007824203 <= 8'b0;
            inj_out_reg_a_1755007824202_988 <= 8'b0;
            inj_out_reg_b_1755007824202_187 <= 8'b0;
        end else begin
            split_reg_var_ts1755007824203 <= inj_data_in_1755007824202_568;
            other_reg_var_ts1755007824203 <= inj_data_in_1755007824202_568 + 2;
            inj_out_reg_a_1755007824202_988 <= split_reg_var_ts1755007824203;
            inj_out_reg_b_1755007824202_187 <= other_reg_var_ts1755007824203;
        end
    end
    // END: mod_split_ff_ts1755007824203

    always_comb begin
        if (clk) begin
            inj_result_val_1755007824202_359 = inj_value1_1755007824202_863;
        end else begin
            inj_result_val_1755007824202_359 = inj_value2_1755007824202_518;
        end
    end
    // END: Comb_IfElse_ts1755007824202

    Module_ConfigKeywords i_cfg (.cfg_in(inj_in_tc_1755007824201_360), .cfg_out(inj_out_tc_1755007824201_444));
    // END: TopConfigExample_ts1755007824201

    simple_adder simple_adder_inst_1755007824201_1148 (
        .a(inj_a_1755007824201_862),
        .b(inj_b_1755007824201_547),
        .sum(inj_sum_1755007824201_77)
    );
endmodule

