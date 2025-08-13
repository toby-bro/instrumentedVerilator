`timescale 1ns/1ps
package util_pkg;
  typedef enum logic [1:0] {IDLE=2'b00, RUN=2'b01, DONE=2'b10} state_e;
endpackage
module comb_basic(input  logic a, output logic y);
  assign y = ~a;
endmodule
module param_gen #(parameter WIDTH = 8)
   (input  logic [WIDTH-1:0] a,
    output logic [WIDTH-1:0] y);
  always_comb y = a ^ {WIDTH{1'b1}};
endmodule
module gen_if #(parameter DEPTH = 4)
  (input  logic [3:0] in,
   output logic       out);
  generate
    if (DEPTH == 4) begin : g_and
      assign out = &in;
    end else begin : g_or
      assign out = |in;
    end
  endgenerate
endmodule
module unique_case_mod(input  logic [1:0] sel,
                       output logic        y);
  always_comb begin
    unique case (sel)
      2'd0: y = 1'b0;
      2'd1: y = 1'b1;
      default: y = 1'b0;
    endcase
  end
endmodule
module struct_pack(input  logic [4:0] in,
                   output logic       out);
  typedef struct packed {
    logic [3:0] n;
    logic       flag;
  } my_s;
  my_s s;
  always_comb begin
    s.n    = in[3:0];
    s.flag = in[4];
    out    = s.flag & ^s.n;
  end
endmodule
module state_machine(
    input  logic clk,
    input  logic reset,
    output logic done);
  import util_pkg::*;
  state_e state;
  always_ff @(posedge clk or posedge reset) begin
    if (reset)
      state <= IDLE;
    else begin
      case (state)
        IDLE: state <= RUN;
        RUN : state <= DONE;
        DONE: state <= DONE;
        default: state <= IDLE;
      endcase
    end
  end
  assign done = (state == DONE);
endmodule
module func_example(
    input  logic [7:0] in,
    output logic [7:0] out);
  function automatic logic [7:0] reverse_bits(logic [7:0] val);
    reverse_bits = {<<{val}};
  endfunction
  assign out = reverse_bits(in);
endmodule
module array_slice(
    input  logic [15:0] in,
    output logic [7:0]  upper,
    output logic [7:0]  lower);
  assign upper = in[15:8];
  assign lower = in[7:0];
endmodule
module generate_for #(parameter W = 8)
   (input  logic [W-1:0] in,
    output logic [W-1:0] out);
  genvar i;
  generate
    for (i = 0; i < W; i++) begin : bit_rev
      assign out[i] = in[W-1-i];
    end
  endgenerate
endmodule
