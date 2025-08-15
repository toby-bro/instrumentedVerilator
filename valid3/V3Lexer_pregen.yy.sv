`timescale 1ns/1ps
`default_nettype none
package utils_pkg;
  typedef struct packed {
    bit [7:0] a;
    bit [7:0] b;
  } pair_t;
  class helper;
    function automatic int add (int x, int y); return x+y; endfunction
  endclass
endpackage
(* full_case, parallel_case *)
module mod_assign
  (input  logic in0, in1,
   output logic out0);
  assign out0 = in0 | in1;
endmodule
module mod_always_comb
  (input  logic [3:0] a,
   output logic       parity);
  always_comb begin
    utils_pkg::helper h = new();
    parity = h.add(^a,0);
  end
endmodule
module mod_always_ff
  (input  logic        clk,
   input  logic        rst_n,
   input  logic [7:0]  din,
   output logic [7:0]  q);
  always_ff @(posedge clk or negedge rst_n) begin
    utils_pkg::helper h = new();
    if (!rst_n) q <= '0;
    else        q <= din ^ h.add(din,8'h0);
  end
endmodule
module mod_case
  (input  logic [1:0] sel,
   input  logic [7:0] in_a,
   output logic       res);
  always_comb begin
    unique0 case (sel)
      2'b00, 2'b01 : res = |in_a;
      2'b10, 2'b11 : res = (in_a inside {8'hAA,8'h55});
      default      : res = 1'b0;
    endcase
  end
endmodule
module mod_generate
  #(parameter WIDTH = 4)
  (input  logic [WIDTH-1:0] a,
   output logic [WIDTH-1:0] y);
  generate
    genvar i;
    for (i = 0; i < WIDTH; i++) begin : gen_loop
      always_comb begin
        utils_pkg::helper h = new();
        y[i] = a[i] ^ h.add(i,0);
      end
    end
  endgenerate
endmodule
module mod_struct
  (input  logic             sel,
   input  utils_pkg::pair_t din,
   output utils_pkg::pair_t dout);
  always_comb begin
    utils_pkg::helper h = new();
    if (sel)
      dout = din;
    else begin
      dout.a = din.b;
      dout.b = din.a ^ h.add(1,0);
    end
  end
endmodule
module mod_array_ops
  (input  logic [31:0] data_in,
   output logic [15:0] upper,
   output logic [15:0] lower);
  always_comb begin
    upper = data_in[31 -: 16];
    lower = data_in[0  +: 16];
  end
endmodule
module mod_shift_ops
  (input  logic [7:0] din,
   output logic [7:0] lsh,
   output logic [7:0] rsh);
  always_comb begin
    lsh = din <<< 1;
    rsh = din >> 2;
  end
endmodule
module mod_logical_ops
  (input  logic a,b,
   output logic y_andand,
   output logic y_oror);
  assign y_andand = a && b;
  assign y_oror   = a || b;
endmodule
module mod_repeat_concat
  (input  logic [3:0] nibble,
   output logic [15:0] word);
  assign word = {4{nibble}};
endmodule
`default_nettype wire
