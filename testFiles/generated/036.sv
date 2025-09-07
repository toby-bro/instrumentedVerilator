module simple_for_loop (
    input logic [7:0] in_data,
    output logic [7:0] out_sum
);
    logic [7:0] sum;
    always_comb begin
        sum = 8'h00;
        for (int i = 0; i < 5; i = i + 1) begin
            sum = sum + in_data;
        end
        out_sum = sum;
    end
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_in_data_1755007762687_95,
    input wire reset,
    output logic [7:0] inj_out_sum_1755007762687_918
);
    simple_for_loop simple_for_loop_inst_1755007762687_805 (
        .out_sum(inj_out_sum_1755007762687_918),
        .in_data(inj_in_data_1755007762687_95)
    );
endmodule

