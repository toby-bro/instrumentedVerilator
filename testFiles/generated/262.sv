module SimpleLogicTest (
    input bit [7:0] data_in,
    input bit select_signal,
    output bit [7:0] data_out
);
    logic [7:0] temp_data;
    always_comb begin
        if (select_signal) begin
            temp_data = data_in + 1;
        end else begin
            temp_data = data_in - 1;
        end
        data_out = temp_data;
    end
endmodule

module configuration_top (
    input logic i_in,
    output logic o_out
);
    assign o_out = i_in;
endmodule

module module_to_bind (
    input logic i_bind_clk,
    input logic [3:0] i_bind_control,
    output logic o_bind_status
);
    always_comb o_bind_status = |i_bind_control;
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

module target_module_for_bind (
    input logic i_target_clk,
    input logic [7:0] i_target_data,
    output logic [7:0] o_target_result
);
    always_comb o_target_result = i_target_data + 1;
endmodule

module snippet (
    input wire clk,
    input logic inj_condition_j_1755007842099_95,
    input bit [7:0] inj_data_in_1755007842100_107,
    input logic [3:0] inj_i_control_1755007842099_232,
    input logic [7:0] inj_i_data_1755007842099_65,
    input wire [7:0] inj_in1_1755007842102_637,
    input wire [7:0] inj_in2_1755007842102_378,
    input logic [7:0] inj_in_a_j_1755007842099_500,
    input bit inj_select_signal_1755007842100_501,
    input int inj_val_a_1755007842103_378,
    input int inj_val_b_1755007842103_225,
    input int inj_val_c_1755007842103_934,
    input wire reset,
    output bit [7:0] inj_data_out_1755007842100_595,
    output logic [5:0] inj_indicators_1755007842103_406,
    output logic inj_o_out_1755007842099_467,
    output logic [7:0] inj_o_result_1755007842099_968,
    output logic inj_o_status_1755007842099_188,
    output wire [7:0] inj_out1_1755007842102_440,
    output wire [7:0] inj_out2_1755007842102_657,
    output logic [7:0] inj_out_x_j_1755007842099_50,
    output logic [7:0] inj_out_y_j_1755007842099_576,
    output logic inj_sub_out_1755007842100_248
);
    // BEGIN: bind_directive_top_ts1755007842099
    // BEGIN: sub_module_ts1755007842100
    // BEGIN: multi_always_comb_ts1755007842102
    logic [7:0] intermediate1_ts1755007842102;
    logic [7:0] intermediate2_ts1755007842102;
        // BEGIN: dup_compare_ts1755007842103
        always_comb begin
            inj_indicators_1755007842103_406 = '0;
            inj_indicators_1755007842103_406[0] = (inj_val_a_1755007842103_378 == inj_val_b_1755007842103_225);
            inj_indicators_1755007842103_406[1] = (inj_val_a_1755007842103_378 != inj_val_b_1755007842103_225);
            inj_indicators_1755007842103_406[2] = (inj_val_a_1755007842103_378 > inj_val_b_1755007842103_225);
            inj_indicators_1755007842103_406[3] = (inj_val_a_1755007842103_378 < inj_val_b_1755007842103_225);
            inj_indicators_1755007842103_406[4] = (inj_val_a_1755007842103_378 >= inj_val_b_1755007842103_225);
            inj_indicators_1755007842103_406[5] = (inj_val_a_1755007842103_378 <= inj_val_b_1755007842103_225);
            if (inj_val_b_1755007842103_225 == inj_val_c_1755007842103_934) begin
                inj_indicators_1755007842103_406 = inj_indicators_1755007842103_406 | 6'b111111;
            end
            if (inj_val_a_1755007842103_378 > inj_val_c_1755007842103_934) begin
                inj_indicators_1755007842103_406 = inj_indicators_1755007842103_406 & 6'b000000;
            end
            if ((inj_val_a_1755007842103_378 < inj_val_b_1755007842103_225) && (inj_val_b_1755007842103_225 > inj_val_c_1755007842103_934)) begin
                inj_indicators_1755007842103_406[0] = 1;
            end else if ((inj_val_a_1755007842103_378 >= inj_val_b_1755007842103_225) || (inj_val_b_1755007842103_225 <= inj_val_c_1755007842103_934)) begin
                inj_indicators_1755007842103_406[1] = 1;
            end
        end
        // END: dup_compare_ts1755007842103

    always @(*) begin
        intermediate1_ts1755007842102 = inj_in1_1755007842102_637 & inj_in2_1755007842102_378;
    end
    always @(*) begin
        intermediate2_ts1755007842102 = inj_in1_1755007842102_637 | inj_in2_1755007842102_378;
    end
    assign inj_out1_1755007842102_440 = intermediate1_ts1755007842102 + 8'd1;
    assign inj_out2_1755007842102_657 = intermediate2_ts1755007842102 - 8'd1;
    // END: multi_always_comb_ts1755007842102

    assign inj_sub_out_1755007842100_248 = !inj_condition_j_1755007842099_95;
    // END: sub_module_ts1755007842100

    SimpleLogicTest SimpleLogicTest_inst_1755007842100_2493 (
        .data_in(inj_data_in_1755007842100_107),
        .select_signal(inj_select_signal_1755007842100_501),
        .data_out(inj_data_out_1755007842100_595)
    );
    configuration_top configuration_top_inst_1755007842099_2917 (
        .o_out(inj_o_out_1755007842099_467),
        .i_in(inj_condition_j_1755007842099_95)
    );
    split_multiple_in_branch split_multiple_in_branch_inst_1755007842099_4749 (
        .in_b_j(inj_i_data_1755007842099_65),
        .out_x_j(inj_out_x_j_1755007842099_50),
        .out_y_j(inj_out_y_j_1755007842099_576),
        .clk_j(clk),
        .condition_j(inj_condition_j_1755007842099_95),
        .in_a_j(inj_in_a_j_1755007842099_500)
    );
    target_module_for_bind target_inst(
        .i_target_clk   (clk),
        .i_target_data  (inj_i_data_1755007842099_65),
        .o_target_result(inj_o_result_1755007842099_968)
    );
    module_to_bind bind_inst(
        .i_bind_clk     (clk),
        .i_bind_control (inj_i_control_1755007842099_232),
        .o_bind_status  (inj_o_status_1755007842099_188)
    );
    // END: bind_directive_top_ts1755007842099
endmodule

