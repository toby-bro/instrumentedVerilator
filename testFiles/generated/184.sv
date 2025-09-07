module ModClockedResetReg (
    input logic clk,
    input logic d,
    input logic rst_n,
    output logic q
);
    always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        q <= 1'b0;
    end else begin
        q <= d;
    end
    end
endmodule

module case_single_default_after_item (
    input logic [1:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        case (in_val)
            2'b01: out_res = 1'b1;
            default: out_res = 1'b0;
            2'b10: out_res = 1'b1;
        endcase
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_d_1755007814836_292,
    input bit [7:0] inj_data1_1755007814836_75,
    input bit [7:0] inj_data2_1755007814836_311,
    input logic [1:0] inj_in_val_1755007814835_143,
    input bit inj_sel_1755007814836_248,
    input wire reset,
    output reg inj_out_res_1755007814835_695,
    output logic inj_q_1755007814836_245,
    output bit [7:0] inj_result1_1755007814836_397,
    output bit [7:0] inj_result2_1755007814836_491
);
    // BEGIN: comb_conditional_ts1755007814836
    ModClockedResetReg ModClockedResetReg_inst_1755007814836_8551 (
        .d(inj_d_1755007814836_292),
        .rst_n(reset),
        .q(inj_q_1755007814836_245),
        .clk(clk)
    );
    always @* begin
        if (inj_sel_1755007814836_248) begin
            inj_result1_1755007814836_397 = inj_data1_1755007814836_75;
            inj_result2_1755007814836_491 = inj_data1_1755007814836_75;
        end else begin
            inj_result1_1755007814836_397 = inj_data2_1755007814836_311;
            inj_result2_1755007814836_491 = inj_data2_1755007814836_311;
        end
    end
    // END: comb_conditional_ts1755007814836

    case_single_default_after_item case_single_default_after_item_inst_1755007814835_9698 (
        .in_val(inj_in_val_1755007814835_143),
        .out_res(inj_out_res_1755007814835_695)
    );
endmodule

