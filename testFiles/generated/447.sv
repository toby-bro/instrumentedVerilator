module Comb_Assign (
    input wire in1,
    input wire in2,
    output wire out
);
    assign out = in1 & in2;
endmodule

module snippet (
    input wire clk,
    input wire [2:0] inj_count_in_1755007903560_917,
    input wire reset,
    output wire [2:0] inj_count_out_1755007903560_558,
    output wire inj_out_1755007903560_254
);
    // BEGIN: simple_seq_ts1755007903560
    reg [2:0] counter_reg_ts1755007903560;
        Comb_Assign Comb_Assign_inst_1755007903560_6816 (
            .in2(clk),
            .out(inj_out_1755007903560_254),
            .in1(reset)
        );
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            counter_reg_ts1755007903560 <= 3'b000;
        end else begin
            counter_reg_ts1755007903560 <= inj_count_in_1755007903560_917 + 3'b001;
        end
    end
    assign inj_count_out_1755007903560_558 = counter_reg_ts1755007903560;
    // END: simple_seq_ts1755007903560
endmodule

