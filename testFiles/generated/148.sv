module mod_module_attrs #(
    parameter int WIDTH = 8
) (
    input wire [7:0] i_in,
    output logic [7:0] o_out
);
    logic [WIDTH-1:0] r_data;
    always_comb begin
        r_data = i_in;
    end
    assign o_out = r_data;
endmodule

module module_function (
    input wire [7:0] in_func_a,
    input wire [7:0] in_func_b,
    output logic [7:0] out_func_result
);
    function automatic [7:0] add_and_subtract;
    input [7:0] val1;
    input [7:0] val2;
    reg [7:0] temp;
    begin
    temp = val1 + val2;
    add_and_subtract = temp - 1;
    end
    endfunction
    always_comb begin
    out_func_result = add_and_subtract(in_func_a, in_func_b);
    end
endmodule

module name_conflict_example (
    input logic i_in,
    output logic o_out
);
    parameter int my_param = 5;
    logic my_var;
    always_comb my_var = i_in;
    assign o_out = i_in && (my_param == 5) && my_var;
endmodule

module snippet #(
    parameter bit GEN = 1
) (
    input wire clk,
    input logic [7:0] inj_a_1755007802577_292,
    input logic [7:0] inj_b_1755007802577_0,
    input logic [7:0] inj_c_1755007802577_256,
    input logic [3:0] inj_i_bind_control_1755007802576_886,
    input wire [3:0] inj_in_a_1755007802575_977,
    input wire [3:0] inj_in_b_1755007802575_723,
    input wire [7:0] inj_in_func_a_1755007802575_792,
    input wire [7:0] inj_in_func_b_1755007802575_887,
    input logic inj_sig_in_1755007802575_434,
    input wire [15:0] inj_value1_1755007802576_511,
    input wire [15:0] inj_value2_1755007802576_228,
    input wire reset,
    output logic inj_anded_1755007802577_662,
    output logic inj_bind_out_1755007802576_414,
    output logic inj_diff_1755007802577_770,
    output logic inj_o_bind_status_1755007802576_286,
    output logic [7:0] inj_o_out_1755007802575_976,
    output logic inj_o_out_1755007802577_158,
    output logic inj_ored_1755007802577_533,
    output logic [15:0] inj_out_concat_1755007802575_254,
    output logic [7:0] inj_out_func_result_1755007802575_368,
    output logic [7:0] inj_out_if_else_1755007802575_194,
    output reg [15:0] inj_result_val_1755007802576_638,
    output logic inj_sig_out_1755007802575_872,
    output logic [7:0] inj_sum_1755007802577_256,
    output logic inj_xored_1755007802577_660
);
    // BEGIN: GenerateIfParam_ts1755007802575
    // BEGIN: module_concat_if_ts1755007802575
    // BEGIN: bind_module_ts1755007802576
    // BEGIN: module_to_bind_ts1755007802576
    // BEGIN: Comb_IfElse_ts1755007802576
    // BEGIN: more_ops_ts1755007802577
    assign inj_sum_1755007802577_256 = inj_a_1755007802577_292 + inj_b_1755007802577_0;
    assign inj_diff_1755007802577_770 = inj_a_1755007802577_292 > inj_c_1755007802577_256;
    assign inj_anded_1755007802577_662 = inj_a_1755007802577_292 & inj_b_1755007802577_0;
    assign inj_ored_1755007802577_533 = inj_a_1755007802577_292 | inj_c_1755007802577_256;
    assign inj_xored_1755007802577_660 = inj_a_1755007802577_292 ^ inj_b_1755007802577_0;
    // END: more_ops_ts1755007802577

    name_conflict_example name_conflict_example_inst_1755007802577_5086 (
        .i_in(inj_sig_in_1755007802575_434),
        .o_out(inj_o_out_1755007802577_158)
    );
    always_comb begin
        if (clk) begin
            inj_result_val_1755007802576_638 = inj_value1_1755007802576_511;
        end else begin
            inj_result_val_1755007802576_638 = inj_value2_1755007802576_228;
        end
    end
    // END: Comb_IfElse_ts1755007802576

    always_comb inj_o_bind_status_1755007802576_286 = |inj_i_bind_control_1755007802576_886;
    // END: module_to_bind_ts1755007802576

    assign inj_bind_out_1755007802576_414 = inj_sig_in_1755007802575_434;
    // END: bind_module_ts1755007802576

    always_comb begin
    inj_out_concat_1755007802575_254 = {inj_in_a_1755007802575_977, inj_in_b_1755007802575_723, inj_in_func_b_1755007802575_887};
    if (reset) begin
        inj_out_if_else_1755007802575_194 = inj_in_func_b_1755007802575_887;
    end else begin
        inj_out_if_else_1755007802575_194 = {inj_in_a_1755007802575_977, inj_in_b_1755007802575_723};
    end
    end
    // END: module_concat_if_ts1755007802575

    mod_module_attrs mod_module_attrs_inst_1755007802575_2131 (
        .o_out(inj_o_out_1755007802575_976),
        .i_in(inj_in_func_b_1755007802575_887)
    );
    generate
        if (GEN) begin : g_true
            assign inj_sig_out_1755007802575_872 = inj_sig_in_1755007802575_434;
        end
        else begin : g_false
            assign inj_sig_out_1755007802575_872 = ~inj_sig_in_1755007802575_434;
        end
    endgenerate
    // END: GenerateIfParam_ts1755007802575

    module_function module_function_inst_1755007802575_6095 (
        .in_func_a(inj_in_func_a_1755007802575_792),
        .in_func_b(inj_in_func_b_1755007802575_887),
        .out_func_result(inj_out_func_result_1755007802575_368)
    );
endmodule

