module ArrayIndexAndPartSelect (
    input logic [31:0] data_in,
    input int index_in,
    input logic [4:0] start_bit,
    output logic bit_out,
    output logic [7:0] byte_out
);
    logic [31:0] internal_data = data_in;
    assign bit_out = internal_data[index_in];
    assign byte_out = internal_data[start_bit +: 8];
endmodule

module LintUnusedSignal (
    input logic in_a,
    output logic out_b
);
    logic unused_w; 
    assign out_b = in_a;
endmodule

module Module_IfNoneParam (
    input int in_port,
    output int out_port
);
    assign out_port = in_port;
endmodule

module macro_concat_user (
    input logic [3:0] concat_in,
    output logic [7:0] concat_out
);
    `define MAKE_NAME(a,b) a``b
    logic var_signal;
    always_comb begin
        `MAKE_NAME(var,_signal) = concat_in[0];
    end
    assign concat_out = {4'b0, concat_in[3:1], var_signal};
endmodule

module module_finish_numbers (
    input bit dummy_in,
    output bit dummy_out
);
    parameter p_finish_0 = 0;
    parameter p_finish_1 = 1;
    parameter p_finish_2 = 2;
    parameter p_finish_other_3 = 3;
    parameter p_finish_large_100 = 100;
    parameter p_finish_neg_minus1 = -1;
    localparam lp_finish_0 = 0;
    localparam lp_finish_1 = 1;
    localparam lp_finish_2 = 2;
    localparam lp_finish_other_5 = 5;
    localparam lp_finish_neg_minus10 = -10;
    assign dummy_out = dummy_in;
endmodule

module split_conditional_reorder (
    input logic clk_cc,
    input logic condition_cc,
    input logic [7:0] val1_cc,
    input logic [7:0] val2_cc,
    input logic [7:0] val3_cc,
    output logic [7:0] out_reg_cc
);
    always @(posedge clk_cc) begin
        out_reg_cc <= val1_cc;
        if (condition_cc) begin
            out_reg_cc <= val2_cc;
        end else begin
            out_reg_cc <= val3_cc;
        end
    end
endmodule

module snippet (
    input wire clk,
    input logic [3:0] inj_concat_in_1755007757330_465,
    input logic inj_cond1_1755007757331_159,
    input logic inj_cond2_1755007757331_989,
    input logic [7:0] inj_data_in_1755007757330_591,
    input logic [31:0] inj_data_in_1755007757331_801,
    input bit inj_dummy_in_1755007757330_947,
    input logic [15:0] inj_in_data_1755007757344_424,
    input int inj_in_port_1755007757330_815,
    input bit [7:0] inj_in_value_1755007757330_494,
    input logic [1:0] inj_large_data_in_1755007757342_490,
    input logic [4:0] inj_start_bit_1755007757331_566,
    input logic [7:0] inj_val2_cc_1755007757335_788,
    input logic [7:0] inj_val3_cc_1755007757335_544,
    input wire reset,
    output logic inj_bit_out_1755007757331_21,
    output logic [7:0] inj_byte_out_1755007757331_229,
    output logic [7:0] inj_concat_out_1755007757330_686,
    output bit inj_dummy_out_1755007757330_254,
    output logic inj_is_even_1755007757330_725,
    output logic [7:0] inj_large_sum_out_1755007757342_582,
    output logic inj_out_b_1755007757339_697,
    output bit [2:0] inj_out_category_1755007757330_694,
    output logic [7:0] inj_out_field_a_1755007757344_901,
    output logic [7:0] inj_out_field_b_1755007757344_929,
    output logic [7:0] inj_out_nested_a_1755007757331_407,
    output logic [7:0] inj_out_nested_b_1755007757331_48,
    output int inj_out_port_1755007757330_185,
    output logic [7:0] inj_out_reg_cc_1755007757335_220,
    output logic inj_y_1755007757337_177
);
    // BEGIN: mod_if_elseif_chained_ts1755007757330
    // BEGIN: FunctionTaskMod_ts1755007757330
    function automatic bit check_even(input logic [7:0] v);
        check_even = ~v[0];
    endfunction
    task automatic dummy_task(input logic [7:0] v);
        int tmp_ts1755007757330;
        tmp_ts1755007757330 = v;
    // BEGIN: mod_split_nested_ts1755007757333
    logic [7:0]  split_nested_var_ts1755007757333;
    logic [7:0] other_nested_var_ts1755007757333;
    // BEGIN: loop_unroll_limit_test_ts1755007757342
    logic [7:0] current_large_sum_ts1755007757342;
    // BEGIN: StructExample_ts1755007757345
    typedef struct packed {
        logic [7:0] field_a_ts1755007757345;
        logic [7:0] field_b_ts1755007757345;
    } example_struct_t;
    example_struct_t my_struct;
    always_comb begin
        my_struct     = inj_in_data_1755007757344_424;
        inj_out_field_a_1755007757344_901   = my_struct.field_a_ts1755007757345;
        inj_out_field_b_1755007757344_929   = my_struct.field_b_ts1755007757345;
    end
    // END: StructExample_ts1755007757345

    always_comb begin
        current_large_sum_ts1755007757342 = 8'h00;
        for (int m = 0; m < 40; m = m + 1) begin 
            current_large_sum_ts1755007757342 = current_large_sum_ts1755007757342 + inj_large_data_in_1755007757342_490[0];
            current_large_sum_ts1755007757342 = current_large_sum_ts1755007757342 + inj_large_data_in_1755007757342_490[1];
            current_large_sum_ts1755007757342 = current_large_sum_ts1755007757342 + 1;
        end
        inj_large_sum_out_1755007757342_582 = current_large_sum_ts1755007757342;
    end
    // END: loop_unroll_limit_test_ts1755007757342

    LintUnusedSignal LintUnusedSignal_inst_1755007757339_2634 (
        .in_a(inj_cond1_1755007757331_159),
        .out_b(inj_out_b_1755007757339_697)
    );
    // BEGIN: ModSimpleLogic_ts1755007757337
    assign inj_y_1755007757337_177 = inj_cond1_1755007757331_159 ^ inj_cond2_1755007757331_989;
    // END: ModSimpleLogic_ts1755007757337

    split_conditional_reorder split_conditional_reorder_inst_1755007757335_5077 (
        .out_reg_cc(inj_out_reg_cc_1755007757335_220),
        .clk_cc(clk),
        .condition_cc(inj_cond1_1755007757331_159),
        .val1_cc(inj_data_in_1755007757330_591),
        .val2_cc(inj_val2_cc_1755007757335_788),
        .val3_cc(inj_val3_cc_1755007757335_544)
    );
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            split_nested_var_ts1755007757333 <= 8'b0;
            other_nested_var_ts1755007757333 <= 8'b0;
        end else begin
            split_nested_var_ts1755007757333 <= 8'h11; 
            other_nested_var_ts1755007757333 <= 8'h22; 
            if (inj_cond1_1755007757331_159) begin
                split_nested_var_ts1755007757333 <= inj_data_in_1755007757330_591 + 10;
                other_nested_var_ts1755007757333 <= inj_data_in_1755007757330_591 + 20;
                if (inj_cond2_1755007757331_989) begin
                    split_nested_var_ts1755007757333 <= inj_data_in_1755007757330_591 + 100;
                    other_nested_var_ts1755007757333 <= inj_data_in_1755007757330_591 + 200;
                end
            end else begin
                split_nested_var_ts1755007757333 <= inj_data_in_1755007757330_591 - 10;
                other_nested_var_ts1755007757333 <= inj_data_in_1755007757330_591 - 20;
            end
        end
    end
    always_comb begin
        inj_out_nested_a_1755007757331_407 = split_nested_var_ts1755007757333;
        inj_out_nested_b_1755007757331_48 = other_nested_var_ts1755007757333;
    end
    // END: mod_split_nested_ts1755007757333

    ArrayIndexAndPartSelect ArrayIndexAndPartSelect_inst_1755007757331_5518 (
        .data_in(inj_data_in_1755007757331_801),
        .index_in(inj_in_port_1755007757330_815),
        .start_bit(inj_start_bit_1755007757331_566),
        .bit_out(inj_bit_out_1755007757331_21),
        .byte_out(inj_byte_out_1755007757331_229)
    );
    Module_IfNoneParam Module_IfNoneParam_inst_1755007757330_4402 (
        .in_port(inj_in_port_1755007757330_815),
        .out_port(inj_out_port_1755007757330_185)
    );
    endtask
    assign inj_is_even_1755007757330_725 = check_even(inj_data_in_1755007757330_591);
    // END: FunctionTaskMod_ts1755007757330

always_comb begin
    if (inj_in_value_1755007757330_494 < 10) begin
        inj_out_category_1755007757330_694 = 3'd0;
    end else if (inj_in_value_1755007757330_494 < 50) begin
        inj_out_category_1755007757330_694 = 3'd1;
    end else if (inj_in_value_1755007757330_494 < 100) begin
        inj_out_category_1755007757330_694 = 3'd2;
    end else begin
        inj_out_category_1755007757330_694 = 3'd3;
    end
end
    // END: mod_if_elseif_chained_ts1755007757330

    module_finish_numbers module_finish_numbers_inst_1755007757330_4459 (
        .dummy_in(inj_dummy_in_1755007757330_947),
        .dummy_out(inj_dummy_out_1755007757330_254)
    );
    macro_concat_user macro_concat_user_inst_1755007757330_9386 (
        .concat_in(inj_concat_in_1755007757330_465),
        .concat_out(inj_concat_out_1755007757330_686)
    );
endmodule

