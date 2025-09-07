module case_priority_overlapping_mod (
    input logic [1:0] case_expr,
    output logic [4:0] internal_out
);
    always @* begin
        priority casez (case_expr)
            2'b1?: internal_out = 5;
            2'b?1: internal_out = 6;  
            2'b0?: internal_out = 7;
            2'b?0: internal_out = 8;  
            default: internal_out = 9;
        endcase
    end
endmodule

module mod_automatic_task (
    input int i_val,
    output int o_val
);
    task automatic update_val(input int in_v, output int out_v);
        out_v = in_v * 2;
    endtask
    always_comb begin
        int temp_val;
        update_val(i_val, temp_val);
        o_val = temp_val;
    end
endmodule

module snippet #(
    parameter integer DATA_WIDTH = 8
) (
    input wire clk,
    input logic inj_a_1755007813116_515,
    input logic inj_b_1755007813116_154,
    input logic [1:0] inj_case_expr_1755007813115_558,
    input int inj_i_val_1755007813116_499,
    input wire [7:0] inj_param_in_1755007813116_891,
    input logic [7:0] inj_start_val_i_1755007813116_8,
    input wire reset,
    output logic [4:0] inj_internal_out_1755007813115_152,
    output int inj_o_val_1755007813116_669,
    output wire [7:0] inj_param_out_1755007813116_541,
    output logic inj_sum_1755007813116_71,
    output logic [15:0] inj_sum_out_i_1755007813116_445
);
    // BEGIN: simple_adder_ts1755007813116
    // BEGIN: split_for_loop_ts1755007813116
    // BEGIN: module_with_params_ts1755007813116
    assign inj_param_out_1755007813116_541 = inj_param_in_1755007813116_891;
    // END: module_with_params_ts1755007813116

    always @(posedge clk) begin
        inj_sum_out_i_1755007813116_445 <= 0;
        for (int i = 0; i < 4; i = i + 1) begin
            inj_sum_out_i_1755007813116_445 <= inj_sum_out_i_1755007813116_445 + inj_start_val_i_1755007813116_8 + i;
        end
    end
    // END: split_for_loop_ts1755007813116

    mod_automatic_task mod_automatic_task_inst_1755007813116_3332 (
        .i_val(inj_i_val_1755007813116_499),
        .o_val(inj_o_val_1755007813116_669)
    );
    assign inj_sum_1755007813116_71 = inj_a_1755007813116_515 + inj_b_1755007813116_154;
    // END: simple_adder_ts1755007813116

    case_priority_overlapping_mod case_priority_overlapping_mod_inst_1755007813115_2744 (
        .case_expr(inj_case_expr_1755007813115_558),
        .internal_out(inj_internal_out_1755007813115_152)
    );
endmodule

