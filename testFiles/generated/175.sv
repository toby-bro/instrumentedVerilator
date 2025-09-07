module case_empty_statement (
    input logic [1:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        case (in_val)
            2'b00: out_res = 1'b1;
            2'b01: ;
            2'b10: out_res = 1'b0;
            default: out_res = 1'b1;
        endcase
    end
endmodule

module cu_base (
    input logic [7:0] data_in,
    output logic [7:0] data_out
);
    assign data_out = data_in;
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_data_in_1755007811762_49,
    input logic [1:0] inj_in_val_1755007811762_898,
    input wire reset,
    output logic [7:0] inj_data_out_1755007811762_231,
    output reg inj_out_res_1755007811762_293
);
    case_empty_statement case_empty_statement_inst_1755007811762_3737 (
        .in_val(inj_in_val_1755007811762_898),
        .out_res(inj_out_res_1755007811762_293)
    );
    cu_base cu_base_inst_1755007811762_6560 (
        .data_in(inj_data_in_1755007811762_49),
        .data_out(inj_data_out_1755007811762_231)
    );
endmodule

