module module_to_bind (
    input logic i_bind_clk,
    input logic [3:0] i_bind_control,
    output logic o_bind_status
);
    always_comb o_bind_status = |i_bind_control;
endmodule

module snippet (
    input wire clk,
    input logic [3:0] inj_i_bind_control_1755007778061_990,
    input wire reset,
    output logic inj_o_bind_status_1755007778061_209
);
    module_to_bind module_to_bind_inst_1755007778061_8752 (
        .i_bind_clk(clk),
        .i_bind_control(inj_i_bind_control_1755007778061_990),
        .o_bind_status(inj_o_bind_status_1755007778061_209)
    );
endmodule

