module BitParts(input logic [7:0] in, output logic [3:0] out);
  assign out = in[7:4];
endmodule
module ContinuousAssign(input logic sig_in, output logic sig_out);
  assign sig_out = sig_in;
endmodule
module ProceduralAssign(input logic clk, input logic d, output logic q);
  logic q = 1'b1;
  always_ff @(posedge clk) begin
    q <= d;
  end
endmodule
module AlwaysCombLogic(input logic [3:0] a, output logic [3:0] b);
  always_comb begin
    b = {a[0], a[1], a[2], a[3]};
  end
endmodule
module GenerateReverse #(parameter N = 4)(input logic [N-1:0] in, output logic [N-1:0] out);
  genvar i;
  generate
    for (i = 0; i < N; i = i + 1) begin
      assign out[i] = in[N-1-i];
    end
  endgenerate
endmodule
module PartSelectGenerate #(parameter P = 2)(input logic [P*2-1:0] in, output logic [P-1:0] out);
  genvar j;
  generate
    for (j = 0; j < P; j = j + 1) begin
      assign out[j] = (in[j*2 +: 2] != 2'b00);
    end
  endgenerate
endmodule
import "DPI-C" function int dpi_increment(input int v);
export "DPI-C" function int dpi_decrement(input int v);
module DPITest(input logic [31:0] val, output logic [31:0] res_inc, output logic [31:0] res_dec);
  always_comb begin
    res_inc = dpi_increment(val);
    res_dec = dpi_decrement(val);
  end
endmodule
interface SimpleIfc(input logic clk);
  logic [7:0] data;
  modport slave (input clk, data);
endinterface
module InterfaceUser(input SimpleIfc.slave ifc, output logic ack);
  always_comb begin
    ack = ^ifc.data;
  end
endmodule
module InoutRef(input logic a, inout logic b, output logic y);
  always_comb begin
    y = a & b;
    b = a | b;
  end
endmodule
module TaskFunctionUse(input logic en, input logic [3:0] x, output logic [3:0] y);
  function logic [3:0] ffunc(input logic [3:0] z);
    ffunc = z + 1;
  endfunction
  task ttask(input logic sel);
    if (sel) y = ffunc(x);
  endtask
  always_comb begin
    ttask(en);
  end
endmodule
