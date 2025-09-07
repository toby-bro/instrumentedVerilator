`define INC(x) ((x) + 1)
package util_pkg;
    function automatic logic [7:0] reverse_bits (input logic [7:0] data);
        integer idx;
        reverse_bits = 8'h0;
        for (idx = 0; idx < 8; idx = idx + 1) begin
            reverse_bits[idx] = data[7-idx];
        end
    endfunction
    function automatic logic parity (input logic [7:0] data);
        parity = ^data;
    endfunction
endpackage
module mod_struct_union (
    input  logic [7:0] in_bus,
    output logic [7:0] out_bus
);
    typedef struct packed {
        logic [3:0] upper;
        logic [3:0] lower;
    } split_t;
    split_t s;
    always_comb begin
        s.upper = in_bus[7:4];
        s.lower = in_bus[3:0];
        out_bus  = {s.lower, s.upper};
    end
endmodule
module mod_class (
    input  logic [3:0] data_in,
    output logic [3:0] data_out
);
    class scaler;
        int factor;
        function new (int f = 1);
            factor = f;
        endfunction
        function int scale (int v);
            return v * factor;
        endfunction
    endclass
    scaler s;
    always_comb begin
        s = new(2);
        data_out = s.scale(data_in);
    end
endmodule
module mod_tasks_functions (
    input  logic [3:0] value_in,
    output logic [3:0] value_out
);
    task automatic increment (output logic [3:0] r, input logic [3:0] v);
        r = v + 1;
    endtask
    function automatic logic [3:0] twox (input logic [3:0] v);
        twox = v << 1;
    endfunction
    always_comb begin
        logic [3:0] tmp;
        increment(tmp, value_in);
        value_out = twox(tmp);
    end
endmodule
module mod_generate #(
    parameter WIDTH = 8
)(
    input  logic [WIDTH-1:0] din,
    output logic [WIDTH-1:0] dout
);
    genvar idx;
    generate
        for (idx = 0; idx < WIDTH; idx = idx + 1) begin : g_inv
            assign dout[idx] = ~din[idx];
        end
    endgenerate
endmodule
module mod_parity (
    input  logic [7:0] data,
    output logic       parity_even
);
    import util_pkg::*;
    always_comb begin
        parity_even = parity(data);
    end
endmodule
module mod_casez (
    input  logic [1:0] sel,
    output logic       out_bit
);
    always_comb begin
        casez (sel)
            2'b00 : out_bit = 1'b0;
            2'b01 : out_bit = 1'b1;
            2'b1? : out_bit = 1'b0;
            default: out_bit = 1'b1;
        endcase
    end
endmodule
module mod_counter (
    input  logic clk,
    output logic [3:0] count
);
    always_ff @(posedge clk) begin
        if (count == 4'd9)
            count <= '0;
        else
            count <= `INC(count);
    end
endmodule
module mod_nested (
    input  logic [3:0] a,
    output logic [3:0] y
);
    function automatic logic [3:0] factorial (input logic [3:0] n);
        if (n <= 1)
            factorial = 1;
        else
            factorial = n * factorial(n - 1);
    endfunction
    always_comb begin : outer_block
        begin : inner_block
            y = factorial(a);
        end
    end
endmodule
module mod_enum (
    input  logic [1:0] op,
    output logic       res
);
    typedef enum logic [1:0] {OP_A = 2'b00, OP_B = 2'b01, OP_C = 2'b10} op_t;
    always_comb begin
        unique case (op_t'(op))
            OP_A   : res = 1'b0;
            OP_B   : res = 1'b1;
            OP_C   : res = 1'b0;
            default: res = 1'b1;
        endcase
    end
endmodule
