module snippet (
    input wire clk,
    input logic [31:0] inj_in_1755007883023_156,
    input bit [3:0] inj_in_data_1755007883023_339,
    input wire reset,
    output logic [7:0] inj_out1_1755007883023_506,
    output logic inj_out2_1755007883023_247,
    output bit [3:0] inj_out_result_1755007883023_88
);
    // BEGIN: constant_sel_ts1755007883023
    // BEGIN: mod_if_else_simple_ts1755007883023
always_comb begin
    if (inj_in_data_1755007883023_339 > 8) begin
        inj_out_result_1755007883023_88 = inj_in_data_1755007883023_339 + 1;
    end else begin
        inj_out_result_1755007883023_88 = inj_in_data_1755007883023_339 - 1;
    end
end
    // END: mod_if_else_simple_ts1755007883023

    assign inj_out1_1755007883023_506 = inj_in_1755007883023_156[15:8];
    assign inj_out2_1755007883023_247 = inj_in_1755007883023_156[3];
    // END: constant_sel_ts1755007883023
endmodule

