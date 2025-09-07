`default_nettype none
class Ccounter;
    int val;
    function new(int v = 0);
        val = v;
    endfunction
    function void inc(int step = 1);
        val += step;
    endfunction
endclass
module bit_select_mux (
    input  logic [15:0] a,
    input  logic [15:0] b,
    input  logic        sel,
    output logic [7:0]  y_slice,
    output logic [15:0] y_mux
);
    always_comb begin
        y_slice = a[15:8];
        y_mux   = sel ? a : b;
    end
endmodule
module concat_example (
    input  logic [3:0] w,
    input  logic [3:0] x,
    input  logic [3:0] y,
    input  logic [3:0] z,
    output logic [15:0] out_concat
);
    always_comb begin
        out_concat = {w, x, y, z};
    end
endmodule
module splice_packed_example (
    input  logic [7:0]  adr,
    input  logic [31:0] data32,
    output logic [31:0] result
);
    always_comb begin
        result = {data32[31:24], adr, data32[15:8], data32[7:0]};
    end
endmodule
module splice_array_example (
    input  logic [7:0]  arr_in  [0:3],
    output logic [7:0]  arr_out [0:3],
    input  logic [1:0]  idx,
    output logic [7:0]  selected_element
);
    always_comb begin
        arr_out          = arr_in;
        selected_element = arr_in[idx];
    end
endmodule
module const_width_example (
    input  logic [7:0]  in_byte,
    output logic [15:0] out_word
);
    localparam logic [15:0] CONST16 = 16'hBEEF;
    always_comb begin
        out_word = {CONST16[7:0], in_byte};
    end
endmodule
module class_inst_example (
    input  logic        clk,
    input  logic [7:0]  d,
    output logic [7:0]  q
);
    Ccounter c_handle;
    always_ff @(posedge clk) begin
        c_handle = new(d);
        q <= c_handle.val;
    end
endmodule
module generate_example #(
    parameter int EN    = 1,
    parameter int WIDTH = 8
) (
    input  logic                    clk,
    input  logic [WIDTH-1:0]        in_vec,
    output logic [WIDTH-1:0]        out_vec
);
    if (EN) begin : g_enabled
        always_ff @(posedge clk) begin
            out_vec <= in_vec;
        end
    end else begin : g_disabled
        assign out_vec = {WIDTH{1'b0}};
    end
endmodule
module fanout_example (
    input  logic [3:0] in_sig,
    output logic [3:0] out_a,
    output logic [3:0] out_b,
    output logic [3:0] out_c
);
    assign out_a = in_sig;
    assign out_b = in_sig ^ 4'hA;
    assign out_c = ~in_sig;
endmodule
`default_nettype wire
