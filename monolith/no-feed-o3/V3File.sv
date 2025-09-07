package math_pkg;
    typedef enum logic [1:0] {ADD, SUB, MUL, DIV} op_t;
endpackage
interface simple_if;
    logic req;
    logic gnt;
endinterface
interface bus_if #(parameter W = 8);
    logic [W-1:0] data;
    logic         valid;
    modport master (output data, output valid);
    modport slave  (input  data, input  valid);
endinterface
module gen_if #(parameter WIDTH = 4) (
    input  logic [WIDTH-1:0] sel,
    output logic [WIDTH-1:0] out
);
    generate
        genvar i;
        for (i = 0; i < WIDTH; i++) begin : g
            if (i % 2 == 0) begin : even
                assign out[i] = sel[i] & 1'b1;
            end else begin : odd
                assign out[i] = sel[i] | 1'b0;
            end
        end
    endgenerate
endmodule
module unique_case_mod (
    input  logic [1:0] sel,
    output logic       y
);
    always_comb begin
        unique casex (sel)
            2'b0?:  y = 1'b0;
            2'b10:  y = 1'b1;
            default: y = 1'b0;
        endcase
    end
endmodule
typedef struct packed {
    logic [7:0] low;
    logic [7:0] high;
} bytes_t;
typedef union packed {
    bytes_t     bytes;
    logic [15:0] word;
} packed_data_u;
module struct_union_mod (
    input  logic [15:0] din,
    output logic [15:0] dout
);
    packed_data_u data;
    always_comb begin
        data.word = din;
        dout      = {8'h00, data.bytes.low} + {8'h00, data.bytes.high};
    end
endmodule
class simple_c;
    function automatic int compute (int a);
        compute = (a ^ 32'hA5A5_A5A5) + 1;
    endfunction
endclass
module class_mod (
    input  logic        trigger,
    output logic [31:0] result
);
    always_comb begin
        simple_c c = new();
        result = trigger ? c.compute(32'hDEAD_BEEF) : 32'h0;
    end
endmodule
module pkg_mod (
    input  logic [7:0]      a,
    input  logic [7:0]      b,
    input  math_pkg::op_t   op,
    output logic [15:0]     res
);
    import math_pkg::*;
    always_comb begin
        case (op)
            ADD: res = a + b;
            SUB: res = a - b;
            MUL: res = a * b;
            DIV: res = (b != 0) ? a / b : 16'hDEAD;
            default: res = 16'h0000;
        endcase
    end
endmodule
module interface_user #(
    parameter W = 8
) (
    bus_if.master           bus,
    input  logic [W-1:0]    in,
    output logic            valid_out
);
    assign bus.data  = in;
    assign bus.valid = 1'b1;
    assign valid_out = bus.valid;
endmodule
