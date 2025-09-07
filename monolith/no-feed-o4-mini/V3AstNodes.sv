module bin_ops(input  wire [3:0] a, input  wire [3:0] b, output wire [3:0] and_o, output wire [3:0] or_o, output wire [3:0] xor_o);
  assign and_o = a & b;
  assign or_o  = a | b;
  assign xor_o = a ^ b;
endmodule
module unary_ops(input  wire [3:0] a, output wire [3:0] not_o, output wire and_r, output wire or_r);
  assign not_o = ~a;
  assign and_r = &a;
  assign or_r  = |a;
endmodule
module ternary_ops(input  wire       sel, input  wire [3:0] a, input  wire [3:0] b, output wire [3:0] y);
  assign y = sel ? a : b;
endmodule
module quad_concat(input  wire [7:0] a, input  wire [7:0] b, input  wire [7:0] c, input  wire [7:0] d, output wire [31:0] y);
  assign y = {a,b,c,d};
endmodule
module part_select(input  wire [7:0] a, output wire [3:0] y);
  assign y = a[5:2];
endmodule
module dynamic_index(input  wire [7:0] a, input  wire [2:0] idx, output wire y);
  assign y = a[idx];
endmodule
module packed_unpacked(input  wire [7:0] arr [1:0], output wire [7:0] out0, output wire [7:0] out1);
  assign out0 = arr[0];
  assign out1 = arr[1];
endmodule
module assoc_array(input  wire        clk, input  wire [7:0] d, output reg  [7:0] q);
  reg [7:0] aa[string];
  always_ff @(posedge clk) begin
    aa["foo"] <= d;
    q <= aa["foo"];
  end
endmodule
module queue_ops(input  wire        clk, input  wire [7:0] d, input  wire push, input  wire pop, output reg  [7:0] qout);
  reg [7:0] q[$];
  always_ff @(posedge clk) begin
    if (push)    q.push_back(d);
    if (pop)     q.pop_front(qout);
  end
endmodule
module struct_mod(input  struct packed { logic [3:0] x; logic [7:0] y; } s_in, output logic [3:0] x_out, output logic [7:0] y_out);
  assign x_out = s_in.x;
  assign y_out = s_in.y;
endmodule
typedef logic [7:0] byte_t;
module typedef_mod(input  byte_t a, output byte_t b);
  assign b = a;
endmodule
module case_mod(input  wire [1:0] sel, input  wire [3:0] a, input  wire [3:0] b, input  wire [3:0] c, input  wire [3:0] d, output reg  [3:0] y);
  always_comb unique case(sel)
    2'b00: y = a;
    2'b01: y = b;
    2'b10: y = c;
    default: y = d;
  endcase
endmodule
import "DPI-C" function int c_add(input int x, input int y);
module dpi_mod(input  int a, input  int b, output int y);
  assign y = c_add(a,b);
endmodule
module fork_mod(input  wire        clk, input  wire [3:0] a, input  wire [3:0] b, output reg  [3:0] y1, output reg  [3:0] y2);
  always_ff @(posedge clk) fork
    y1 <= a;
    y2 <= b;
  join_none
endmodule
module cover_mod(input  wire        clk, input  wire [3:0] a);
  covergroup cg @(posedge clk);
    coverpoint a;
  endgroup
  cg cg_inst = new();
endmodule
module gen_array(input  wire [3:0] in, output wire [3:0] out [3:0]);
  genvar i;
  generate
    for (i = 0; i < 4; i = i + 1) begin
      assign out[i] = in;
    end
  endgenerate
endmodule
module clocking_mod(input  wire clk, input  wire [3:0] a, output wire [3:0] y);
  clocking cb @(posedge clk);
    input a;
  endclocking
  assign y = cb.a + 1;
endmodule
module function_mod(input  wire [3:0] a, input  wire [3:0] b, output wire [4:0] z);
  function automatic [4:0] add2(input [3:0] x, input [3:0] y);
    add2 = x + y;
  endfunction
  assign z = add2(a,b);
endmodule
module cclass_dyn(input  wire [3:0] idx, output logic [7:0] y);
  class Dyn;
    rand byte_t arr[];
    function new();
      arr = new[4];
      arr[0] = 8'hA1;
      arr[1] = 8'hB2;
      arr[2] = 8'hC3;
      arr[3] = 8'hD4;
    endfunction
  endclass
  Dyn d;
  always_comb begin
    d = new();
    y = d.arr[idx];
  end
endmodule
module constraint_mod(output int a_out);
  class C;
    rand int a;
    constraint c { a inside {[0:10]}; }
    function int get();
      if (this.randomize()) get = a;
      else get = 0;
    endfunction
  endclass
  C c_inst = new();
  assign a_out = c_inst.get();
endmodule
interface Ifc(input logic clk);
  logic [3:0] data;
  modport MP (input data);
endinterface
module ifc_mod(Ifc.MP i, output wire [3:0] o);
  assign o = i.data;
endmodule
module always_active(input  wire        clk, output reg  [7:0] count);
  always @(posedge clk) count <= count + 1;
endmodule
