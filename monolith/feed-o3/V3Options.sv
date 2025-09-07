`timescale 1ns/1ps
`default_nettype none
module timescale_mod #(parameter int W = 8) (
    input  logic [W-1:0] in_data,
    output logic [W-1:0] out_data
);
    assign out_data = in_data;
endmodule
`define WIDTH_DEF 16
module param_mod #(
    parameter int WIDTH = `WIDTH_DEF,
    parameter bit INVERT = 0
) (
    input  logic [WIDTH-1:0]  din,
    output logic [WIDTH-1:0]  dout
);
    generate
        if (INVERT) begin
            assign dout = ~din;
        end else begin
            assign dout =  din;
        end
    endgenerate
endmodule
`undef WIDTH_DEF
module clocker_mod (
    input  logic clk,
    input  logic rst_n,
    input  logic  data_in,
    output logic  data_out
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            data_out <= 1'b0;
        else
            data_out <= data_in;
    end
endmodule
module struct_packed_mod (
    input  logic clk,
    input  logic [3:0] vec,
    output logic [3:0] vec_out
);
    typedef struct packed {
        logic [1:0] lo;
        logic [1:0] hi;
    } vec_t;
    vec_t s;
    always_ff @(posedge clk) begin
        s.lo <= vec[1:0];
        s.hi <= vec[3:2];
        vec_out <= {s.hi, s.lo};
    end
endmodule
module generate_mod #(parameter int N = 4) (
    input  logic [N-1:0] in_bits,
    output logic [N-1:0] out_bits
);
    genvar i;
    generate
        for (i = 0; i < N; i++) begin : g
            assign out_bits[i] = ~in_bits[i];
        end
    endgenerate
endmodule
module dpi_mod (
    output logic done
);
    import "DPI-C" function int dpi_counter ();
    assign done = dpi_counter()[0];
endmodule
interface simple_bus #(parameter int W = 8);
    logic [W-1:0] data;
endinterface
module bus_user_mod (
    input  logic clk,
    input  logic [7:0] in_data,
    output logic [7:0] out_data
);
    simple_bus #(8) sb();
    always_ff @(posedge clk) begin
        sb.data <= in_data;
        out_data <= sb.data;
    end
endmodule
module class_mod (
    input  logic clk,
    input  logic in_bit,
    output logic out_bit
);
    class inverter;
        function logic inv (logic x);
            return ~x;
        endfunction
    endclass
    inverter inv_h;
    always_ff @(posedge clk) begin
        if (inv_h == null)
            inv_h = new();
        out_bit <= inv_h.inv(in_bit);
    end
endmodule
`define SHIFT_LEFT(X) ((X) << 1)
module macro_mod (
    input  logic [7:0] in_val,
    output logic [7:0] out_val
);
    assign out_val = `SHIFT_LEFT(in_val);
endmodule
`undef SHIFT_LEFT
module array_mod #(parameter int AW = 4) (
    input  logic                 clk,
    input  logic                 we,
    input  logic  [AW-1:0]       addr,
    input  logic                 wdat,
    output logic                 rdat
);
    logic mem [0:(1<<AW)-1];
    always_ff @(posedge clk) begin
        if (we)
            mem[addr] <= wdat;
        rdat <= mem[addr];
    end
endmodule
`default_nettype wire
