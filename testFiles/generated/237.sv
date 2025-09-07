module Seq_DFF (
    input wire clk,
    input wire [7:0] d_in,
    input wire rst,
    output reg [7:0] q_out
);
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            q_out <= 8'b0;
        end else begin
            q_out <= d_in;
        end
    end
endmodule

module snippet (
    input wire clk,
    input wire [7:0] inj_d_in_1755007833454_776,
    input wire reset,
    output reg [7:0] inj_q_out_1755007833454_20
);
    Seq_DFF Seq_DFF_inst_1755007833454_2747 (
        .q_out(inj_q_out_1755007833454_20),
        .clk(clk),
        .d_in(inj_d_in_1755007833454_776),
        .rst(reset)
    );
endmodule

