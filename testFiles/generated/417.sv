module CombinationalLogicExplicit (
    input logic [15:0] data0,
    input logic [15:0] data1,
    input logic sel,
    output logic [15:0] data_out
);
    always @(sel or data0 or data1) begin
        if (sel) begin
            data_out = data1;
        end else begin
            data_out = data0;
        end
    end
endmodule

module snippet (
    input wire clk,
    input logic [15:0] inj_data0_1755007893776_375,
    input logic [15:0] inj_data1_1755007893776_657,
    input logic inj_sel_1755007893776_814,
    input wire reset,
    output logic [15:0] inj_data_out_1755007893776_126
);
    CombinationalLogicExplicit CombinationalLogicExplicit_inst_1755007893776_2574 (
        .data0(inj_data0_1755007893776_375),
        .data1(inj_data1_1755007893776_657),
        .sel(inj_sel_1755007893776_814),
        .data_out(inj_data_out_1755007893776_126)
    );
endmodule

