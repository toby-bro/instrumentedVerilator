module mod_basic (
    input wire i_clk,
    output logic o_done
);
    logic r_state;
    parameter int PARAM_BASIC = 42;
    always_ff @(posedge i_clk) begin
        r_state <= ~r_state;
    end
    always_comb begin
        o_done = r_state;
    end
endmodule

module snippet (
    input wire clk,
    input wire reset,
    output logic inj_o_done_1755007801548_317
);
    mod_basic mod_basic_inst_1755007801548_6119 (
        .o_done(inj_o_done_1755007801548_317),
        .i_clk(clk)
    );
endmodule

