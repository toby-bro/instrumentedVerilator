module CaseZExample (
    input wire [3:0] data_in,
    input wire [1:0] sel,
    output reg [3:0] case_out
);
    wire [3:0] local_data;
    assign local_data = data_in;
    always @* begin
        casez (sel)
            2'b0?: case_out = local_data;
            2'b10: case_out = 4'b1111;
            default: case_out = 4'b0000;
        endcase
    end
endmodule

module snippet (
    input wire clk,
    input wire [3:0] inj_data_in_1755007905265_115,
    input logic [1:0] inj_in_val_1755007905265_472,
    input wire [1:0] inj_sel_1755007905265_83,
    input wire reset,
    output reg [3:0] inj_case_out_1755007905265_966,
    output reg inj_out_res_1755007905265_538
);
    // BEGIN: case_single_default_after_item_ts1755007905265
    always_comb begin
        inj_out_res_1755007905265_538 = 1'b0;
        case (inj_in_val_1755007905265_472)
            2'b01: inj_out_res_1755007905265_538 = 1'b1;
            default: inj_out_res_1755007905265_538 = 1'b0;
            2'b10: inj_out_res_1755007905265_538 = 1'b1;
        endcase
    end
    // END: case_single_default_after_item_ts1755007905265

    CaseZExample CaseZExample_inst_1755007905265_4724 (
        .data_in(inj_data_in_1755007905265_115),
        .sel(inj_sel_1755007905265_83),
        .case_out(inj_case_out_1755007905265_966)
    );
endmodule

