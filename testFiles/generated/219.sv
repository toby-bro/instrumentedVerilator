module CaseZExample (
    input wire [3:0] data_in,
    input wire [1:0] sel,
    output reg [3:0] case_out
);
    wire [3:0] local_data;
    assign local_data = data_in;
    always @* begin
        casez (sel)
            2'b0?: case_out = local_data;
            2'b10: case_out = 4'b1111;
            default: case_out = 4'b0000;
        endcase
    end
endmodule

module IfElseIfChain (
    input logic [7:0] data0,
    input logic [7:0] data1,
    input logic [7:0] data2,
    input logic [7:0] data3,
    input logic [1:0] sel_code,
    output logic [7:0] selected_data
);
    always_comb begin
        if (sel_code == 2'b00) begin
            selected_data = data0;
        end else if (sel_code == 2'b01) begin
            selected_data = data1;
        end else if (sel_code == 2'b10) begin
            selected_data = data2;
        end else begin
            selected_data = data3;
        end
    end
endmodule

module ModuleImplicitPort (
    input logic signed [7:0] data,
    output logic out_valid
);
    logic valid;
    assign valid = |data;
    assign out_valid = valid;
endmodule

module Parameterized #(
    parameter int WIDTH = 8
) (
    input logic [7:0] din,
    output logic [7:0] dout
);
    assign dout = din;
endmodule

module SimpleAssign (
    input logic [7:0] in_data,
    output logic [7:0] out_data
);
    assign out_data = in_data;
endmodule

module basic_assign_if (
    input logic in_a,
    input logic in_b,
    output logic out_c
);
    logic intermediate_wire;
    assign intermediate_wire = in_a & in_b;
    always_comb begin
        if (intermediate_wire) begin
            out_c = 1'b1;
        end else begin
            out_c = 1'b0;
        end
    end
endmodule

module deep_task_logic (
    input wire [1:0] dtl_action_sel,
    input wire dtl_clk,
    input wire [7:0] dtl_data_a,
    input wire [7:0] dtl_data_b,
    input wire dtl_en,
    input wire dtl_rst_n,
    output logic [7:0] dtl_result_reg
);
    task automatic perform_action;
        input [7:0] in_a;
        input [7:0] in_b;
        input [1:0] action;
        output logic [7:0] calculated_res;
        logic [7:0] temp_task_calc;
        if (action[0]) begin
            if (action[1]) begin
                temp_task_calc = in_a + in_b;
            end else begin
                temp_task_calc = in_a - in_b;
            end
        end else begin
            if (action[1]) begin
                temp_task_calc = in_a & in_b;
            end else begin
                temp_task_calc = in_a | in_b;
            end
        end
        case (temp_task_calc[1:0])
            2'b00: calculated_res = temp_task_calc ^ 8'hFF;
            2'b01: calculated_res = temp_task_calc + 1;
            2'b10: calculated_res = temp_task_calc - 1;
            default: calculated_res = temp_task_calc;
        endcase
    endtask
    always_ff @(posedge dtl_clk or negedge dtl_rst_n) begin
        if (!dtl_rst_n) begin
            dtl_result_reg <= 8'd0;
        end else begin
            logic [7:0] next_dtl_result;
            if (dtl_en) begin
                perform_action(dtl_data_a, dtl_data_b, dtl_action_sel, next_dtl_result);
            end else begin
                next_dtl_result = dtl_result_reg;
            end
            dtl_result_reg <= next_dtl_result;
        end
    end
endmodule

module expr_preadd_comb (
    input logic [7:0] add_val_m1,
    input logic [7:0] in_val_m1,
    output logic [7:0] out_sum_m1,
    output logic [7:0] var_out_m1
);
    logic [7:0] var_m1;
    always_comb begin
        var_m1 = in_val_m1;
        out_sum_m1 = (++var_m1) + add_val_m1;
        var_out_m1 = var_m1;
    end
endmodule

module mod_casex_wildcard_overlap_priority (
    input bit [3:0] in_mask_x,
    output bit [1:0] out_match_type_x
);
always_comb begin
    out_match_type_x = 2'b01;
    priority casex (in_mask_x)
        4'b1X0Z: begin
            out_match_type_x = 2'b10;
        end
        4'b10?Z: begin
            out_match_type_x = 2'b11;
        end
        4'bZ1?X: begin
            out_match_type_x = 2'b00;
        end
        default: begin
            out_match_type_x = 2'b01;
        end
    endcase
end
endmodule

module rand_case_mod (
    input logic [2:0] selector,
    output logic [3:0] result_out
);
    always_comb begin
        case (selector)
            0: result_out = 4'h0;
            1: result_out = 4'h1;
            2: result_out = 4'hA;
            default: result_out = 4'hF;
        endcase
    end
endmodule

module sequential_always_assign (
    input logic clk,
    input logic [7:0] in,
    output logic [7:0] out
);
    always @(posedge clk) begin
        out <= in;
    end
endmodule

module sequential_register (
    input logic clk,
    input logic data_in,
    input logic enable_in,
    input logic reset_n,
    output logic data_out
);
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            data_out <= 1'b0; 
        end else if (enable_in) begin
            data_out <= data_in; 
        end
    end
endmodule

module simple_undeclared_mod (
    input int in_val,
    output int out_val
);
    assign out_val = in_val;
endmodule

module split_multiple_in_branch (
    input logic clk_j,
    input logic condition_j,
    input logic [7:0] in_a_j,
    input logic [7:0] in_b_j,
    output logic [7:0] out_x_j,
    output logic [7:0] out_y_j
);
    always @(posedge clk_j) begin
        if (condition_j) begin
            out_x_j <= in_a_j * 3;
            out_y_j <= in_b_j + 1;
        end else begin
            out_x_j <= in_a_j;
            out_y_j <= in_b_j;
        end
    end
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_d3_1755007827200_887,
    input logic [7:0] inj_data3_1755007827261_151,
    input logic signed [7:0] inj_data_1755007827176_129,
    input wire [3:0] inj_data_in_1755007827174_910,
    input wire [7:0] inj_dtl_data_a_1755007827177_403,
    input wire [7:0] inj_dtl_data_b_1755007827177_116,
    input logic inj_enable_1755007827175_242,
    input wire [3:0] inj_in0_1755007827174_81,
    input wire [3:0] inj_in1_1755007827174_146,
    input logic inj_in1_1755007827183_251,
    input wire [3:0] inj_in3_1755007827174_4,
    input bit [3:0] inj_in_mask_x_1755007827224_920,
    input logic [1:0] inj_in_val_1755007827181_315,
    input int inj_in_val_1755007827197_694,
    input logic [15:0] inj_in_vec_1755007827228_20,
    input wire [1:0] inj_sel_1755007827174_144,
    input logic [2:0] inj_selector_1755007827175_305,
    input logic [3:0] inj_val_a_1755007827175_244,
    input logic [3:0] inj_val_b_1755007827175_18,
    input wire reset,
    output reg [3:0] inj_case_out_1755007827174_348,
    output logic inj_data_out_1755007827188_802,
    output logic [7:0] inj_default_out_1755007827247_13,
    output logic [7:0] inj_dout_1755007827191_480,
    output logic [7:0] inj_dtl_result_reg_1755007827177_885,
    output logic [7:0] inj_dtl_result_reg_1755007827194_900,
    output reg [3:0] inj_mux_out_1755007827174_87,
    output logic [7:0] inj_out1_1755007827200_825,
    output logic inj_out_1755007827183_845,
    output logic [7:0] inj_out_1755007827254_28,
    output logic inj_out_c_1755007827211_409,
    output logic [7:0] inj_out_data_1755007827233_316,
    output logic inj_out_g_1755007827207_275,
    output logic inj_out_its_1755007827219_886,
    output bit [1:0] inj_out_match_type_x_1755007827224_331,
    output logic [3:0] inj_out_narrow_1755007827249_930,
    output int inj_out_port_1755007827239_231,
    output reg inj_out_res_1755007827181_282,
    output logic [7:0] inj_out_slice_be_1755007827228_600,
    output logic [7:0] inj_out_slice_le_1755007827228_407,
    output logic [7:0] inj_out_sum_m1_1755007827252_483,
    output int inj_out_val_1755007827197_496,
    output int inj_out_val_1755007827241_67,
    output int inj_out_val_1755007827244_811,
    output logic inj_out_valid_1755007827176_913,
    output logic [7:0] inj_out_x_j_1755007827215_348,
    output logic [7:0] inj_out_y_j_1755007827215_456,
    output logic inj_q_1755007827186_165,
    output logic [3:0] inj_result_1755007827175_265,
    output logic [3:0] inj_result_out_1755007827175_976,
    output logic [7:0] inj_selected_data_1755007827260_592,
    output logic [7:0] inj_var_out_m1_1755007827252_311
);
    // BEGIN: Comb_Case_ts1755007827175
    // BEGIN: CombinationalLogic_ts1755007827175
    // BEGIN: deep_task_logic_ts1755007827179
    task automatic perform_action;
        input [7:0] in_a;
        input [7:0] in_b;
        input [1:0] action;
        output logic [7:0] calculated_res_ts1755007827179;
        logic [7:0] temp_task_calc_ts1755007827179;
        if (action[0]) begin
            if (action[1]) begin
                temp_task_calc_ts1755007827179 = in_a + in_b;
            end else begin
                temp_task_calc_ts1755007827179 = in_a - in_b;
            end
        end else begin
            if (action[1]) begin
                temp_task_calc_ts1755007827179 = in_a & in_b;
            end else begin
                temp_task_calc_ts1755007827179 = in_a | in_b;
            end
        end
        case (temp_task_calc_ts1755007827179[1:0])
            2'b00: calculated_res_ts1755007827179 = temp_task_calc_ts1755007827179 ^ 8'hFF;
            2'b01: calculated_res_ts1755007827179 = temp_task_calc_ts1755007827179 + 1;
            2'b10: calculated_res_ts1755007827179 = temp_task_calc_ts1755007827179 - 1;
            default: calculated_res_ts1755007827179 = temp_task_calc_ts1755007827179;
        endcase
    endtask
    always_ff @(posedge clk or negedge reset) begin
        if (!reset) begin
            inj_dtl_result_reg_1755007827177_885 <= 8'd0;
        end else begin
            logic [7:0] next_dtl_result_ts1755007827179;
                // BEGIN: dup_logic_ops_ts1755007827201
                logic cond1_ts1755007827201, cond2_ts1755007827201, cond3_ts1755007827201;
                logic complex_cond1_ts1755007827201, complex_cond2_ts1755007827201;
                    IfElseIfChain IfElseIfChain_inst_1755007827261_5888 (
                        .selected_data(inj_selected_data_1755007827260_592),
                        .data0(inj_data_1755007827176_129),
                        .data1(next_dtl_result_ts1755007827179),
                        .data2(inj_d3_1755007827200_887),
                        .data3(inj_data3_1755007827261_151),
                        .sel_code(inj_in_val_1755007827181_315)
                    );
                    sequential_always_assign sequential_always_assign_inst_1755007827254_9846 (
                        .clk(clk),
                        .in(next_dtl_result_ts1755007827179),
                        .out(inj_out_1755007827254_28)
                    );
                    expr_preadd_comb expr_preadd_comb_inst_1755007827252_3230 (
                        .in_val_m1(next_dtl_result_ts1755007827179),
                        .out_sum_m1(inj_out_sum_m1_1755007827252_483),
                        .var_out_m1(inj_var_out_m1_1755007827252_311),
                        .add_val_m1(inj_d3_1755007827200_887)
                    );
                    // BEGIN: LintImplicitWidth_ts1755007827249
                    assign inj_out_narrow_1755007827249_930 = inj_data_1755007827176_129;
                    // END: LintImplicitWidth_ts1755007827249

                    // BEGIN: func_macro_defaults_ts1755007827247
                    `define DEFAULT_CONST       8'hAA
                    `define CALC(val, def=`DEFAULT_CONST) ((val) | (def))
                    localparam logic [7:0] P_WITH_DEF     = `CALC(8'h0F);
                    localparam logic [7:0] P_OVERRIDE_DEF = `CALC(8'hF0, 8'h11);
                    assign inj_default_out_1755007827247_13 = cond3_ts1755007827201 ? P_WITH_DEF : P_OVERRIDE_DEF;
                    // END: func_macro_defaults_ts1755007827247

                    // BEGIN: system_names_mod_ts1755007827244
                    assign inj_out_val_1755007827244_811 = $bits(inj_in_val_1755007827197_694);
                    // END: system_names_mod_ts1755007827244

                    simple_undeclared_mod simple_undeclared_mod_inst_1755007827241_9040 (
                        .out_val(inj_out_val_1755007827241_67),
                        .in_val(inj_in_val_1755007827197_694)
                    );
                    // BEGIN: Module_IfNoneParam_ts1755007827239
                    assign inj_out_port_1755007827239_231 = inj_in_val_1755007827197_694;
                    // END: Module_IfNoneParam_ts1755007827239

                    SimpleAssign SimpleAssign_inst_1755007827233_7518 (
                        .in_data(inj_d3_1755007827200_887),
                        .out_data(inj_out_data_1755007827233_316)
                    );
                    // BEGIN: range_select_simple_packed_ts1755007827228
                    assign inj_out_slice_be_1755007827228_600 = inj_in_vec_1755007827228_20[7:0]; 
                    assign inj_out_slice_le_1755007827228_407 = inj_in_vec_1755007827228_20[7:0]; 
                    // END: range_select_simple_packed_ts1755007827228

                    mod_casex_wildcard_overlap_priority mod_casex_wildcard_overlap_priority_inst_1755007827224_5665 (
                        .out_match_type_x(inj_out_match_type_x_1755007827224_331),
                        .in_mask_x(inj_in_mask_x_1755007827224_920)
                    );
                    // BEGIN: ImplicitTimeScaleModule_ts1755007827219
                    assign inj_out_its_1755007827219_886 = inj_enable_1755007827175_242;
                    // END: ImplicitTimeScaleModule_ts1755007827219

                    split_multiple_in_branch split_multiple_in_branch_inst_1755007827215_8738 (
                        .out_x_j(inj_out_x_j_1755007827215_348),
                        .out_y_j(inj_out_y_j_1755007827215_456),
                        .clk_j(clk),
                        .condition_j(complex_cond2_ts1755007827201),
                        .in_a_j(next_dtl_result_ts1755007827179),
                        .in_b_j(inj_d3_1755007827200_887)
                    );
                    basic_assign_if basic_assign_if_inst_1755007827211_2015 (
                        .in_b(complex_cond2_ts1755007827201),
                        .out_c(inj_out_c_1755007827211_409),
                        .in_a(cond1_ts1755007827201)
                    );
                    // BEGIN: LintSeqNonBlockAssign_ts1755007827207
                    always_ff @(posedge clk) begin
                        inj_out_g_1755007827207_275 <= complex_cond1_ts1755007827201;
                    end
                    // END: LintSeqNonBlockAssign_ts1755007827207

                assign cond1_ts1755007827201 = inj_val_a_1755007827175_244[0] && inj_val_a_1755007827175_244[1];
                assign cond2_ts1755007827201 = inj_val_a_1755007827175_244[2] || inj_val_a_1755007827175_244[3];
                assign cond3_ts1755007827201 = !inj_val_a_1755007827175_244[0];
                assign complex_cond1_ts1755007827201 = (cond1_ts1755007827201 || cond2_ts1755007827201) && cond3_ts1755007827201;
                assign complex_cond2_ts1755007827201 = !(inj_val_a_1755007827175_244[0] && inj_val_a_1755007827175_244[1]) || (inj_val_a_1755007827175_244[2] || !inj_val_a_1755007827175_244[3]);
                always_comb begin
                    inj_out1_1755007827200_825 = '0;
                    if (complex_cond1_ts1755007827201) begin
                        inj_out1_1755007827200_825 = inj_data_1755007827176_129 + next_dtl_result_ts1755007827179;
                    end else begin
                        inj_out1_1755007827200_825 = inj_data_1755007827176_129 ^ inj_d3_1755007827200_887;
                    end
                    if (complex_cond2_ts1755007827201) begin
                        inj_out1_1755007827200_825 = inj_out1_1755007827200_825 + inj_d3_1755007827200_887;
                    end else begin
                        inj_out1_1755007827200_825 = inj_out1_1755007827200_825 - inj_d3_1755007827200_887;
                    end
                    if ((inj_val_a_1755007827175_244[0] && inj_val_a_1755007827175_244[1]) && (!inj_val_a_1755007827175_244[2] || inj_val_a_1755007827175_244[3])) begin
                        inj_out1_1755007827200_825 = inj_out1_1755007827200_825 * 2;
                    end
                end
                // END: dup_logic_ops_ts1755007827201

                // BEGIN: system_names_mod_ts1755007827197
                assign inj_out_val_1755007827197_496 = $bits(inj_in_val_1755007827197_694);
                // END: system_names_mod_ts1755007827197

                deep_task_logic deep_task_logic_inst_1755007827194_8631 (
                    .dtl_data_a(inj_dtl_data_a_1755007827177_403),
                    .dtl_data_b(inj_dtl_data_b_1755007827177_116),
                    .dtl_en(clk),
                    .dtl_rst_n(reset),
                    .dtl_result_reg(inj_dtl_result_reg_1755007827194_900),
                    .dtl_action_sel(inj_sel_1755007827174_144),
                    .dtl_clk(clk)
                );
                Parameterized Parameterized_inst_1755007827191_9452 (
                    .din(next_dtl_result_ts1755007827179),
                    .dout(inj_dout_1755007827191_480)
                );
                sequential_register sequential_register_inst_1755007827188_9756 (
                    .data_out(inj_data_out_1755007827188_802),
                    .clk(clk),
                    .data_in(inj_enable_1755007827175_242),
                    .enable_in(inj_in1_1755007827183_251),
                    .reset_n(reset)
                );
                // BEGIN: ModClockedResetReg_ts1755007827186
                always @(posedge clk or negedge reset) begin
                if (!reset) begin
                    inj_q_1755007827186_165 <= 1'b0;
                end else begin
                    inj_q_1755007827186_165 <= inj_enable_1755007827175_242;
                end
                end
                // END: ModClockedResetReg_ts1755007827186

                // BEGIN: simple_and_gate_ts1755007827183
                assign inj_out_1755007827183_845 = inj_in1_1755007827183_251 & inj_enable_1755007827175_242;
                // END: simple_and_gate_ts1755007827183

                // BEGIN: case_basic_ts1755007827181
                always_comb begin
                    inj_out_res_1755007827181_282 = 1'b0;
                    case (inj_in_val_1755007827181_315)
                        2'b00: inj_out_res_1755007827181_282 = 1'b0;
                        2'b01: inj_out_res_1755007827181_282 = 1'b1;
                        2'b10: inj_out_res_1755007827181_282 = 1'b0;
                        2'b11: inj_out_res_1755007827181_282 = 1'b1;
                    endcase
                end
                // END: case_basic_ts1755007827181

            if (reset) begin
                perform_action(inj_dtl_data_a_1755007827177_403, inj_dtl_data_b_1755007827177_116, inj_sel_1755007827174_144, next_dtl_result_ts1755007827179);
            end else begin
                next_dtl_result_ts1755007827179 = inj_dtl_result_reg_1755007827177_885;
            end
            inj_dtl_result_reg_1755007827177_885 <= next_dtl_result_ts1755007827179;
        end
    end
    // END: deep_task_logic_ts1755007827179

    ModuleImplicitPort ModuleImplicitPort_inst_1755007827176_4949 (
        .data(inj_data_1755007827176_129),
        .out_valid(inj_out_valid_1755007827176_913)
    );
    rand_case_mod rand_case_mod_inst_1755007827175_1271 (
        .result_out(inj_result_out_1755007827175_976),
        .selector(inj_selector_1755007827175_305)
    );
    always_comb begin
        if (inj_enable_1755007827175_242) begin
            inj_result_1755007827175_265 = inj_val_a_1755007827175_244 + inj_val_b_1755007827175_18;
        end else begin
            inj_result_1755007827175_265 = 4'h0;
        end
    end
    // END: CombinationalLogic_ts1755007827175

    always_comb begin
        case (inj_sel_1755007827174_144)
            2'b00: inj_mux_out_1755007827174_87 = inj_in0_1755007827174_81;
            2'b01: inj_mux_out_1755007827174_87 = inj_in1_1755007827174_146;
            2'b10: inj_mux_out_1755007827174_87 = inj_data_in_1755007827174_910;
            default: inj_mux_out_1755007827174_87 = inj_in3_1755007827174_4;
        endcase
    end
    // END: Comb_Case_ts1755007827175

    CaseZExample CaseZExample_inst_1755007827174_8298 (
        .data_in(inj_data_in_1755007827174_910),
        .sel(inj_sel_1755007827174_144),
        .case_out(inj_case_out_1755007827174_348)
    );
endmodule

