package util_pkg;
    typedef struct packed {
        logic [7:0] low;
        logic [7:0] high;
    } byte_pair_t;
    typedef union packed {
        logic [15:0] whole;
        byte_pair_t  pair;
    } word_union_t;
endpackage
class Multiplier;
    function automatic logic [15:0] mul(logic [7:0] x, logic [7:0] y);
        mul = x * y;
    endfunction
endclass
module comb_adder_param #(
    parameter WIDTH = 8
) (
    input  logic [WIDTH-1:0] in_a,
    input  logic [WIDTH-1:0] in_b,
    output logic [WIDTH   :0] sum_o
);
    always_comb begin
        sum_o = in_a + in_b;
    end
endmodule
module counter_sync_reset (
    input  logic       clk,
    input  logic       rst_n,
    output logic [7:0] count_o
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            count_o <= '0;
        else
            count_o <= count_o + 8'd1;
    end
endmodule
module generate_inverter #(
    parameter N = 4
) (
    input  logic [N-1:0] in_vec,
    output logic [N-1:0] out_vec
);
    generate
        genvar i;
        for (i = 0; i < N; i++) begin : gen_inv
            assign out_vec[i] = ~in_vec[i];
        end
    endgenerate
endmodule
module struct_union_demo (
    input  logic  [7:0] byte_i,
    output logic [15:0] word_o
);
    import util_pkg::*;
    word_union_t u;
    always_comb begin
        u.whole = {byte_i, byte_i};
        word_o  = u.whole;
    end
endmodule
module class_usage_demo (
    input  logic  [7:0] factor_a,
    input  logic  [7:0] factor_b,
    output logic [15:0] product_o
);
    always_comb begin
        Multiplier m = new();
        product_o = m.mul(factor_a, factor_b);
    end
endmodule
