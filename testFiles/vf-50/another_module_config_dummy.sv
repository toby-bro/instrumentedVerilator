module module_to_bind (
    input logic i_bind_clk,
    input logic [3:0] i_bind_control,
    output logic o_bind_status
);
    always_comb o_bind_status = |i_bind_control;
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

module another_module_config_dummy (
    input wire clk,
    input logic i,
    input logic [3:0] inj_i_control_1755538366595_972,
    input logic [7:0] inj_i_data_1755538366595_687,
    input logic [15:0] inj_in1_1755538366595_414,
    input logic [15:0] inj_in2_1755538366595_11,
    input wire rst,
    output logic [7:0] inj_o_result_1755538366595_801,
    output logic inj_o_status_1755538366595_289,
    output logic [15:0] inj_out1_1755538366595_365,
    output logic [15:0] inj_out2_1755538366595_580,
    output logic o
);
    // BEGIN: procedural_complex_ts1755538366595
    logic [15:0] temp1_ts1755538366595;
    logic [15:0] temp2_ts1755538366595;
    always_comb begin
        temp1_ts1755538366595 = (inj_in1_1755538366595_414 + inj_in2_1755538366595_11) * 10;
        if (i) begin
            temp2_ts1755538366595 = temp1_ts1755538366595 ^ (inj_in1_1755538366595_414 >>> 2);
            inj_out1_1755538366595_365 = temp2_ts1755538366595 & inj_in2_1755538366595_11;
        end else begin
            temp2_ts1755538366595 = temp1_ts1755538366595 | (inj_in2_1755538366595_11 <<< 3);
            inj_out1_1755538366595_365 = temp2_ts1755538366595 + inj_in1_1755538366595_414;
        end
        inj_out2_1755538366595_580 = temp1_ts1755538366595 - temp2_ts1755538366595;
    end
    // END: procedural_complex_ts1755538366595

    bind_directive_top bind_directive_top_inst_1755538366595_3862 (
        .o_result(inj_o_result_1755538366595_801),
        .o_status(inj_o_status_1755538366595_289),
        .i_clk(clk),
        .i_control(inj_i_control_1755538366595_972),
        .i_data(inj_i_data_1755538366595_687)
    );
    assign o = i & i; 
endmodule

