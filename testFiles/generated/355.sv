module BindSimpleModule (
    input bit in,
    output bit out
);
    assign out = in;
endmodule

module ModuleImplicitPort (
    input logic signed [7:0] data,
    output logic out_valid
);
    logic valid;
    assign valid = |data;
    assign out_valid = valid;
endmodule

module bitwise_ops (
    input logic [7:0] in1,
    input logic [7:0] in2,
    input logic [7:0] in3,
    output logic [7:0] out
);
    assign out = (in1 & in2) | (~in3) ^ (in1 << 2) >> 1;
endmodule

module module_to_bind (
    input logic i_bind_clk,
    input logic [3:0] i_bind_control,
    output logic o_bind_status
);
    always_comb o_bind_status = |i_bind_control;
endmodule

module split_arith_nb (
    input logic clk_v,
    input logic [7:0] op1_v,
    input logic [7:0] op2_v,
    output logic [7:0] diff_v,
    output logic [7:0] prod_v,
    output logic [7:0] sum_v
);
    always @(posedge clk_v) begin
        sum_v <= op1_v + op2_v;
        diff_v <= op1_v - op2_v;
        prod_v <= op1_v * op2_v;
    end
endmodule

module wide_bus_ops (
    input wire [63:0] wide_a,
    input wire [63:0] wide_b,
    output wire [127:0] concat_out,
    output wire [7:0] reduce_xor_out,
    output wire [63:0] wide_sum
);
    assign wide_sum = wide_a + wide_b;
    assign reduce_xor_out = ^wide_a[63:0];
    assign concat_out = {wide_a, wide_b};
endmodule

module snippet (
    input wire clk,
    input logic inj_data_value_1755007873634_585,
    input logic [3:0] inj_i_bind_control_1755007873634_860,
    input logic [7:0] inj_in1_1755007873633_398,
    input logic [7:0] inj_in2_1755007873633_940,
    input logic [7:0] inj_in3_1755007873633_683,
    input bit inj_in_1755007873633_513,
    input logic inj_level1_en_1755007873634_922,
    input logic inj_level2_en_1755007873634_548,
    input wire [63:0] inj_wide_a_1755007873635_886,
    input wire [63:0] inj_wide_b_1755007873635_690,
    input wire reset,
    output wire [127:0] inj_concat_out_1755007873635_994,
    output logic [7:0] inj_diff_v_1755007873633_902,
    output logic inj_o_bind_status_1755007873634_752,
    output logic [7:0] inj_out_1755007873633_143,
    output bit inj_out_1755007873633_27,
    output logic inj_out_valid_1755007873633_491,
    output logic [7:0] inj_prod_v_1755007873633_886,
    output wire [7:0] inj_reduce_xor_out_1755007873635_300,
    output logic inj_result_out_1755007873634_701,
    output logic [7:0] inj_sum_v_1755007873633_183,
    output wire [63:0] inj_wide_sum_1755007873635_522
);
    // BEGIN: nested_blocks_ts1755007873634
    wide_bus_ops wide_bus_ops_inst_1755007873635_4447 (
        .wide_a(inj_wide_a_1755007873635_886),
        .wide_b(inj_wide_b_1755007873635_690),
        .concat_out(inj_concat_out_1755007873635_994),
        .reduce_xor_out(inj_reduce_xor_out_1755007873635_300),
        .wide_sum(inj_wide_sum_1755007873635_522)
    );
    always_comb begin : main_block 
        inj_result_out_1755007873634_701 = 1'b0; 
        if (inj_level1_en_1755007873634_922) begin : inner_block1 
            if (inj_level2_en_1755007873634_548) begin : inner_block2 
                inj_result_out_1755007873634_701 = inj_data_value_1755007873634_585;
            end 
        end 
    end
    // END: nested_blocks_ts1755007873634

    module_to_bind module_to_bind_inst_1755007873634_82 (
        .i_bind_clk(clk),
        .i_bind_control(inj_i_bind_control_1755007873634_860),
        .o_bind_status(inj_o_bind_status_1755007873634_752)
    );
    ModuleImplicitPort ModuleImplicitPort_inst_1755007873633_8388 (
        .data(inj_in1_1755007873633_398),
        .out_valid(inj_out_valid_1755007873633_491)
    );
    split_arith_nb split_arith_nb_inst_1755007873633_3734 (
        .diff_v(inj_diff_v_1755007873633_902),
        .prod_v(inj_prod_v_1755007873633_886),
        .sum_v(inj_sum_v_1755007873633_183),
        .clk_v(clk),
        .op1_v(inj_in1_1755007873633_398),
        .op2_v(inj_in2_1755007873633_940)
    );
    bitwise_ops bitwise_ops_inst_1755007873633_1121 (
        .out(inj_out_1755007873633_143),
        .in1(inj_in1_1755007873633_398),
        .in2(inj_in2_1755007873633_940),
        .in3(inj_in3_1755007873633_683)
    );
    BindSimpleModule BindSimpleModule_inst_1755007873633_1252 (
        .in(inj_in_1755007873633_513),
        .out(inj_out_1755007873633_27)
    );
endmodule

