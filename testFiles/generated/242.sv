module ModuleFF (
    input logic clk,
    input bit [3:0] in1,
    input bit [3:0] in2,
    input logic reset,
    output bit [3:0] out1,
    output bit [3:0] out2
);
    parameter int MAX_COUNT = 10;
    localparam int START_VAL = 5;
    logic [3:0] ff_reg;
    integer unused_int_var;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            ff_reg <= START_VAL;
            out1 <= '0;
            out2 <= '0;
            unused_int_var <= 0;
        end else begin
            case ({in1, in2})
                8'h00: ff_reg <= ff_reg;
                8'h01: ff_reg <= in1 + in2;
                default: ff_reg <= MAX_COUNT;
            endcase
            out1 <= ff_reg;
            out2 <= {in1[0], in1[0], in1[0], in1[0]} | {in2[3], in2[2], in2[1], in2[0]};
        end
    end
endmodule

module snippet (
    input wire clk,
    input logic [1:0] inj_case_expr_1755007835083_683,
    input bit [3:0] inj_in1_1755007835083_731,
    input bit [3:0] inj_in2_1755007835083_475,
    input wire reset,
    output logic [4:0] inj_internal_out_1755007835083_512,
    output bit [3:0] inj_out1_1755007835083_214,
    output bit [3:0] inj_out2_1755007835083_510
);
    // BEGIN: case_unique0_violating_mod_ts1755007835083
    always @* begin
        unique0 casez (inj_case_expr_1755007835083_683)
            2'b1?: inj_internal_out_1755007835083_512 = 8;
            2'b11: inj_internal_out_1755007835083_512 = 9;  
            2'b?1: inj_internal_out_1755007835083_512 = 10; 
            2'b00: inj_internal_out_1755007835083_512 = 11; 
        endcase
    end
    // END: case_unique0_violating_mod_ts1755007835083

    ModuleFF ModuleFF_inst_1755007835083_4029 (
        .in1(inj_in1_1755007835083_731),
        .in2(inj_in2_1755007835083_475),
        .reset(reset),
        .out1(inj_out1_1755007835083_214),
        .out2(inj_out2_1755007835083_510),
        .clk(clk)
    );
endmodule

