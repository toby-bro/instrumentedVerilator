module module_to_bind (
    input logic i_bind_clk,
    input logic [3:0] i_bind_control,
    input wire rst,
    output logic inj_out_sub_1755538364374_176,
    output logic o_bind_status
);
    // BEGIN: mod_sub_ts1755538364374
    assign inj_out_sub_1755538364374_176 = rst;
    // END: mod_sub_ts1755538364374

    always_comb o_bind_status = |i_bind_control;
endmodule

