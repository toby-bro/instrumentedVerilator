module IfElseIfChain (
    input logic [7:0] data0,
    input logic [7:0] data1,
    input logic [7:0] data2,
    input logic [7:0] data3,
    input logic [1:0] sel_code,
    output logic [7:0] selected_data
);
    always_comb begin
        if (sel_code == 2'b00) begin
            selected_data = data0;
        end else if (sel_code == 2'b01) begin
            selected_data = data1;
        end else if (sel_code == 2'b10) begin
            selected_data = data2;
        end else begin
            selected_data = data3;
        end
    end
endmodule

module casez_xz (
    input logic [2:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        casez (in_val)
            3'b1??: out_res = 1'b1;
            3'b0z?: out_res = 1'b0;
            default: out_res = 1'b1;
        endcase
    end
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_data0_1755007797553_405,
    input logic [7:0] inj_data1_1755007797553_587,
    input logic [7:0] inj_data2_1755007797553_545,
    input logic [7:0] inj_data3_1755007797553_4,
    input logic [2:0] inj_in_val_1755007797553_742,
    input logic [1:0] inj_sel_code_1755007797553_183,
    input wire reset,
    output reg inj_out_res_1755007797553_357,
    output logic [7:0] inj_selected_data_1755007797553_382
);
    IfElseIfChain IfElseIfChain_inst_1755007797553_499 (
        .data1(inj_data1_1755007797553_587),
        .data2(inj_data2_1755007797553_545),
        .data3(inj_data3_1755007797553_4),
        .sel_code(inj_sel_code_1755007797553_183),
        .selected_data(inj_selected_data_1755007797553_382),
        .data0(inj_data0_1755007797553_405)
    );
    casez_xz casez_xz_inst_1755007797553_981 (
        .in_val(inj_in_val_1755007797553_742),
        .out_res(inj_out_res_1755007797553_357)
    );
endmodule

