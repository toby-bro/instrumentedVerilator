module arithmetic_mod #(parameter int WIDTH = 8) (
    input  logic [WIDTH-1:0] a,
    input  logic [WIDTH-1:0] b,
    output logic [WIDTH-1:0] sum,
    output logic [WIDTH-1:0] diff
);
    assign sum  = a + b;
    assign diff = (a > b) ? (a - b) : (b - a);
endmodule
module wide_constant_mod (
    input  logic        sel,
    output logic [511:0] out_vec
);
    localparam [511:0] CONST_WIDE = 512'h00000000000000000000000000000000FEDCBA9876543210FEDCBA9876543210FEDCBA9876543210FEDCBA9876543210;
    assign out_vec = sel ? CONST_WIDE : 512'd0;
endmodule
module array_init_mod (
    input  logic [1:0] idx,
    output logic [7:0] data_out
);
    logic [7:0] mem [0:3] = '{8'h11, 8'h22, 8'h33, 8'h44};
    assign data_out = mem[idx];
endmodule
module assoc_array_mod (
    input  int               key_in,
    output logic [31:0]      value_out
);
    logic [31:0] aa [int] = '{default:32'h00000000,
                              5:32'hAAAABBBB,
                              10:32'hCCCCDDDD};
    always_comb begin
        if (aa.exists(key_in))
            value_out = aa[key_in];
        else
            value_out = 32'hDEADBEEF;
    end
endmodule
import "DPI-C" function int dpi_inc(input int a);
module dpi_call_mod (
    input  int in_val,
    output int out_val
);
    assign out_val = dpi_inc(in_val);
endmodule
class simple_class;
    int value;
    function new(int v = 0); value = v; endfunction
    function int get(); return value; endfunction
endclass
module class_mod (
    input  logic clk,
    input  int   in_data,
    output int   out_data
);
    simple_class c;
    int out_r;
    always_ff @(posedge clk) begin
        if (c == null) begin
            c <= new(in_data);
        end
        out_r <= c.get();
    end
    assign out_data = out_r;
endmodule
module queue_mod (
    input  logic clk,
    input  byte  in_byte,
    output byte  front_byte
);
    byte q[$];
    byte front_r;
    always_ff @(posedge clk) begin
        if (q.size() != 0)
            front_r <= q[0];
        else
            front_r <= in_byte;
    end
    assign front_byte = front_r;
endmodule
typedef struct packed {
    logic [7:0] b0;
    logic [7:0] b1;
} pkt_t;
module struct_mod (
    input  pkt_t in_pkt,
    output logic [7:0] sum
);
    localparam pkt_t DEFAULT_PKT = '{8'hAA, 8'h55};
    assign sum = in_pkt.b0 + in_pkt.b1 + DEFAULT_PKT.b0 + DEFAULT_PKT.b1;
endmodule
