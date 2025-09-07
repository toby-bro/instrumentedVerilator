module CombAddSub #(parameter WIDTH = 8) (input logic [WIDTH-1:0] a, b, output logic [WIDTH-1:0] sum, diff);
  always_comb begin
    sum = a + b;
    diff = a - b;
  end
endmodule
module SeqReg #(parameter N = 4) (input logic clk, reset, input logic [N-1:0] d, output logic [N-1:0] q);
  always_ff @(posedge clk or posedge reset) begin
    if (reset)
      q <= '0;
    else
      q <= d;
  end
endmodule
module MixedLogic (input logic clk, a, b, c, output logic y, z);
  always @(posedge clk) begin
    y = a & b;
    z <= b | c;
  end
endmodule
module NestedIfLogic #(parameter K = 2) (input logic clk, enable, cond, input logic [K-1:0] in_val, output logic [K-1:0] out_val);
  always @(posedge clk) begin
    if (enable) begin
      if (cond)
        out_val <= in_val + 1;
      else
        out_val <= in_val - 1;
    end else begin
      out_val = '0;
    end
  end
endmodule
module CaseBlock (input logic [1:0] sel, input logic [7:0] in0, in1, in2, in3, output logic [7:0] out0);
  always_comb begin
    case (sel)
      2'd0: out0 = in0;
      2'd1: out0 <= in1;
      2'd2: out0 = in2;
      default: out0 <= in3;
    endcase
  end
endmodule
module LoopSum (input logic [3:0] vec, output logic [2:0] sum);
  integer i;
  always_comb begin
    sum = 0;
    for (i = 0; i < 4; i = i + 1) begin
      sum = sum + vec[i];
    end
  end
endmodule
module WhileLoop (input logic en, input logic [3:0] data, output logic [3:0] result);
  integer idx;
  always_comb begin
    idx = 0;
    result = 0;
    while (idx < 4) begin
      if (en)
        result = result + data[idx];
      idx = idx + 1;
    end
  end
endmodule
module ContinuousAssign (input logic x, y, output logic z);
  assign z = x ^ y;
endmodule
module MultiAlways (input logic clk, input logic a, b, output logic y1, y2);
  always @(posedge clk) begin
    y1 <= a;
  end
  always_comb begin
    y2 = b;
  end
endmodule
