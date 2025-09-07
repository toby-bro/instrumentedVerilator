module BitwiseAssign (
    input logic [3:0] in_a,
    input logic [3:0] in_b,
    output logic [3:0] out_y
);
    assign out_y = in_a ^ in_b;
endmodule

module Comb_Loop (
    input wire loop_in,
    output wire loop_out
);
    wire loop_wire1;
    wire loop_wire2;
    assign loop_wire1 = loop_wire2 | loop_in;
    assign loop_wire2 = loop_wire1; 
    assign loop_out = loop_wire1;
endmodule

module CombinationalLogic (
    input logic enable,
    input logic [3:0] val_a,
    input logic [3:0] val_b,
    output logic [3:0] result
);
    always_comb begin
        if (enable) begin
            result = val_a + val_b;
        end else begin
            result = 4'h0;
        end
    end
endmodule

module Module_ControlFlow (
    input bit clk,
    input logic [7:0] data_in,
    input bit reset_n,
    input logic [2:0] sel_in,
    output reg [7:0] data_out
);
    reg [7:0] temp;
    always_comb begin
        unique case (sel_in)
            3'b000: temp = data_in;
            3'b001: temp = data_in + 1;
            3'b010: temp = data_in - 1;
            default: temp = 8'hAA;
        endcase
    end
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            data_out <= 8'h00;
        else
            data_out <= temp;
    end
endmodule

module ReductionOperations (
    input logic [7:0] data_in,
    output logic and_reduce,
    output logic or_reduce,
    output logic xor_reduce
);
    assign and_reduce = &data_in;
    assign or_reduce = |data_in;
    assign xor_reduce = ^data_in;
endmodule

module split_input_only_var (
    input logic clk_k,
    input logic control_signal_k,
    input logic [7:0] data_in_k,
    output logic [7:0] data_out_k
);
    always @(posedge clk_k) begin
        if (control_signal_k) begin
            data_out_k <= data_in_k;
        end
    end
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_b_aa_1755007783575_624,
    input logic [7:0] inj_c_aa_1755007783575_410,
    input logic [7:0] inj_data_in_k_1755007783575_822,
    input logic inj_enable_1755007783575_881,
    input logic [15:0] inj_in1_1755007783576_957,
    input logic [15:0] inj_in2_1755007783576_418,
    input logic [15:0] inj_in3_1755007783576_675,
    input logic [15:0] inj_in4_1755007783576_165,
    input logic [15:0] inj_in5_1755007783576_579,
    input logic [2:0] inj_sel_in_1755007783576_524,
    input logic [3:0] inj_val_a_1755007783575_281,
    input logic [3:0] inj_val_b_1755007783575_879,
    input wire reset,
    output logic inj_and_reduce_1755007783578_929,
    output reg [7:0] inj_data_out_1755007783576_409,
    output logic [7:0] inj_data_out_k_1755007783575_333,
    output wire inj_loop_out_1755007783577_636,
    output logic inj_or_reduce_1755007783578_9,
    output logic [15:0] inj_out1_1755007783579_781,
    output logic [15:0] inj_out2_1755007783579_237,
    output logic inj_out_1755007783576_375,
    output logic inj_out_1755007783578_928,
    output logic [3:0] inj_out_y_1755007783575_796,
    output logic [3:0] inj_result_1755007783575_246,
    output logic [7:0] inj_x_aa_1755007783575_950,
    output logic inj_xor_reduce_1755007783578_475,
    output logic [7:0] inj_y_aa_1755007783575_983,
    output logic [7:0] inj_z_aa_1755007783575_334
);
    // BEGIN: split_combo_blocking_ts1755007783575
    // BEGIN: arith_comp_ops_ts1755007783576
    // BEGIN: variable_sel_mux_ts1755007783579
    // BEGIN: procedural_complex_ts1755007783580
    logic [15:0] temp1_ts1755007783580;
    logic [15:0] temp2_ts1755007783580;
    always_comb begin
        temp1_ts1755007783580 = (inj_in3_1755007783576_675 + inj_in2_1755007783576_418) * 10;
        if (inj_enable_1755007783575_881) begin
            temp2_ts1755007783580 = temp1_ts1755007783580 ^ (inj_in3_1755007783576_675 >>> 2);
            inj_out1_1755007783579_781 = temp2_ts1755007783580 & inj_in2_1755007783576_418;
        end else begin
            temp2_ts1755007783580 = temp1_ts1755007783580 | (inj_in2_1755007783576_418 <<< 3);
            inj_out1_1755007783579_781 = temp2_ts1755007783580 + inj_in3_1755007783576_675;
        end
        inj_out2_1755007783579_237 = temp1_ts1755007783580 - temp2_ts1755007783580;
    end
    // END: procedural_complex_ts1755007783580

    assign inj_out_1755007783578_928 = inj_b_aa_1755007783575_624[inj_sel_in_1755007783576_524];
    // END: variable_sel_mux_ts1755007783579

    ReductionOperations ReductionOperations_inst_1755007783578_6543 (
        .and_reduce(inj_and_reduce_1755007783578_929),
        .or_reduce(inj_or_reduce_1755007783578_9),
        .xor_reduce(inj_xor_reduce_1755007783578_475),
        .data_in(inj_data_in_k_1755007783575_822)
    );
    Comb_Loop Comb_Loop_inst_1755007783577_4661 (
        .loop_in(reset),
        .loop_out(inj_loop_out_1755007783577_636)
    );
    Module_ControlFlow Module_ControlFlow_inst_1755007783576_4422 (
        .data_in(inj_data_in_k_1755007783575_822),
        .reset_n(reset),
        .sel_in(inj_sel_in_1755007783576_524),
        .data_out(inj_data_out_1755007783576_409),
        .clk(clk)
    );
    assign inj_out_1755007783576_375 = (inj_in1_1755007783576_957 + inj_in2_1755007783576_418) * inj_in3_1755007783576_675 > inj_in4_1755007783576_165 - inj_in5_1755007783576_579;
    // END: arith_comp_ops_ts1755007783576

    BitwiseAssign BitwiseAssign_inst_1755007783575_7954 (
        .out_y(inj_out_y_1755007783575_796),
        .in_a(inj_val_a_1755007783575_281),
        .in_b(inj_val_b_1755007783575_879)
    );
    always @(*) begin
        inj_x_aa_1755007783575_950 = inj_data_in_k_1755007783575_822 + inj_b_aa_1755007783575_624;
        inj_y_aa_1755007783575_983 = inj_x_aa_1755007783575_950 - inj_c_aa_1755007783575_410;
        inj_z_aa_1755007783575_334 = inj_data_in_k_1755007783575_822 * inj_c_aa_1755007783575_410;
    end
    // END: split_combo_blocking_ts1755007783575

    split_input_only_var split_input_only_var_inst_1755007783575_1098 (
        .data_out_k(inj_data_out_k_1755007783575_333),
        .clk_k(clk),
        .control_signal_k(inj_enable_1755007783575_881),
        .data_in_k(inj_data_in_k_1755007783575_822)
    );
    CombinationalLogic CombinationalLogic_inst_1755007783575_4775 (
        .result(inj_result_1755007783575_246),
        .enable(inj_enable_1755007783575_881),
        .val_a(inj_val_a_1755007783575_281),
        .val_b(inj_val_b_1755007783575_879)
    );
endmodule

