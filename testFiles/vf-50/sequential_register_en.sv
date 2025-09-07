module simple_adder (
    input logic a,
    input logic b,
    output logic sum
);
    assign sum = a + b;
endmodule

module sequential_register_en (
    input logic clk,
    input logic [7:0] data_in,
    input logic en,
    input wire rst,
    output logic [7:0] data_out,
    output logic inj_sum_1755538629378_887
);
    simple_adder simple_adder_inst_1755538629378_9201 (
        .sum(inj_sum_1755538629378_887),
        .a(clk),
        .b(en)
    );
    always_ff @(posedge clk) begin
        if (en) begin
            data_out <= data_in;
        end
    end
endmodule

