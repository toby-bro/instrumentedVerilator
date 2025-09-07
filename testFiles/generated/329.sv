interface MyInterface (
    input logic clk
);
    logic req;
    logic valid;
    modport master (output req, input valid, input clk);
    modport slave (input req, output valid, input clk);
endinterface
module concat_assign (
    input logic [7:0] in,
    output logic [3:0] out_h,
    output logic [3:0] out_l
);
    assign {out_h, out_l} = in;
endmodule

module named_block_logic (
    input logic i_gate,
    input logic i_in,
    output logic o_out
);
    logic r_internal;
    logic r_temp;
    always_comb begin : my_combinational_block
        r_temp = i_in & i_gate;
        r_internal = r_temp;
        o_out = r_internal;
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_i_gate_1755007864786_229,
    input logic inj_i_in_1755007864786_627,
    input logic [7:0] inj_in_1755007864786_923,
    input wire reset,
    output logic inj_dout_a_1755007864786_331,
    output logic inj_dout_b_1755007864786_868,
    output logic inj_o_1755007864787_322,
    output logic inj_o_out_1755007864786_694,
    output logic [3:0] inj_out_h_1755007864786_334,
    output logic [3:0] inj_out_l_1755007864786_47,
    output logic inj_valid_out_1755007864786_237
);
    // BEGIN: ModuleWithInterface_ts1755007864786
    // BEGIN: ModMultipleAlways_ts1755007864786
    // BEGIN: another_module_config_dummy_ts1755007864787
    assign inj_o_1755007864787_322 = inj_i_gate_1755007864786_229 & inj_i_gate_1755007864786_229; 
    // END: another_module_config_dummy_ts1755007864787

    always @(posedge clk or negedge reset) begin 
    if (!reset) begin 
        inj_dout_a_1755007864786_331 <= 1'b0;
    end else begin
        inj_dout_a_1755007864786_331 <= inj_i_gate_1755007864786_229; 
    end
    end
    always @(posedge clk) begin 
    inj_dout_b_1755007864786_868 <= inj_i_in_1755007864786_627; 
    end
    // END: ModMultipleAlways_ts1755007864786

    MyInterface my_if (clk);
    assign my_if.req = 1'b1;
    assign inj_valid_out_1755007864786_237 = my_if.valid;
    // END: ModuleWithInterface_ts1755007864786

    named_block_logic named_block_logic_inst_1755007864786_9094 (
        .i_gate(inj_i_gate_1755007864786_229),
        .i_in(inj_i_in_1755007864786_627),
        .o_out(inj_o_out_1755007864786_694)
    );
    concat_assign concat_assign_inst_1755007864786_6562 (
        .in(inj_in_1755007864786_923),
        .out_h(inj_out_h_1755007864786_334),
        .out_l(inj_out_l_1755007864786_47)
    );
endmodule

