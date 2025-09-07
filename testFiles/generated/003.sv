interface cond_if;
    logic [15:0] control_reg;
    logic [15:0] status_reg;
    modport CtrlStat (output control_reg, input status_reg);
endinterface
module module_to_bind (
    input logic i_bind_clk,
    input logic [3:0] i_bind_control,
    output logic o_bind_status
);
    always_comb o_bind_status = |i_bind_control;
endmodule

module simple_xor_gate (
    input logic in1,
    input logic in2,
    output logic out
);
    assign out = in1 ^ in2;
endmodule

module target_module_for_bind (
    input logic i_target_clk,
    input logic [7:0] i_target_data,
    output logic [7:0] o_target_result
);
    always_comb o_target_result = i_target_data + 1;
endmodule

module bind_directive_top (
    input logic i_clk,
    input logic [3:0] i_control,
    input logic [7:0] i_data,
    output logic [7:0] o_result,
    output logic o_status
);
    target_module_for_bind target_inst(
        .i_target_clk   (i_clk),
        .i_target_data  (i_data),
        .o_target_result(o_result)
    );
    module_to_bind bind_inst(
        .i_bind_clk     (i_clk),
        .i_bind_control (i_control),
        .o_bind_status  (o_status)
    );
endmodule

module snippet (
    input wire clk,
    input logic [15:0] inj_data_in_1755007751080_484,
    input logic [3:0] inj_i_control_1755007751081_776,
    input logic inj_in2_1755007751080_698,
    input logic inj_in_la_1755007751080_97,
    input logic [7:0] inj_in_val_y_1755007751080_193,
    input wire reset,
    output logic inj_control_status_1755007751080_473,
    output logic [7:0] inj_o_result_1755007751081_735,
    output logic inj_o_status_1755007751081_845,
    output logic inj_out_1755007751080_283,
    output logic inj_out_la_1755007751080_231,
    output logic [7:0] inj_out_vec_y_1755007751080_273
);
    // BEGIN: mod_large_array_target_ts1755007751080
    // BEGIN: split_vector_assign_ts1755007751080
    // BEGIN: module_conditional_write_ts1755007751081
    bind_directive_top bind_directive_top_inst_1755007751081_9612 (
        .o_result(inj_o_result_1755007751081_735),
        .o_status(inj_o_status_1755007751081_845),
        .i_clk(clk),
        .i_control(inj_i_control_1755007751081_776),
        .i_data(inj_in_val_y_1755007751080_193)
    );
    cond_if cif_inst();
    always_comb begin
        if (inj_in_la_1755007751080_97) begin
            cif_inst.control_reg = inj_data_in_1755007751080_484;
        end else begin
            cif_inst.control_reg = 16'h0;
        end
        inj_control_status_1755007751080_473 = (cif_inst.control_reg != 16'h0);
    end
    // END: module_conditional_write_ts1755007751081

    simple_xor_gate simple_xor_gate_inst_1755007751080_27 (
        .in1(inj_in_la_1755007751080_97),
        .in2(inj_in2_1755007751080_698),
        .out(inj_out_1755007751080_283)
    );
    always @(posedge clk) begin
        if (inj_in_la_1755007751080_97) begin
            inj_out_vec_y_1755007751080_273[3:0] <= inj_in_val_y_1755007751080_193[3:0];
            inj_out_vec_y_1755007751080_273[7:4] <= inj_in_val_y_1755007751080_193[7:4] + 1;
        end else begin
            inj_out_vec_y_1755007751080_273 <= 8'hFF;
        end
    end
    // END: split_vector_assign_ts1755007751080

    assign inj_out_la_1755007751080_231 = inj_in_la_1755007751080_97;
    // END: mod_large_array_target_ts1755007751080
endmodule

