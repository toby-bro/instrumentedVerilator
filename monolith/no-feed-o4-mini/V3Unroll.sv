module UnrollFor4(input logic a, output logic [3:0] b);
  logic [3:0] sum;
  integer i;
  always_comb begin
    sum = 0;
    for (i = 0; i < 4; i = i + 1) begin
      sum = sum + a;
    end
  end
  assign b = sum;
endmodule
module UnrollWhile3(input logic [1:0] in, output logic [1:0] res);
  integer x;
  logic [1:0] flag;
  always_comb begin
    x = in;
    flag = 0;
    while (x > 0) begin
      flag = flag + 1;
      x = x - 1;
    end
  end
  assign res = flag;
endmodule
module GenLoopUnroll(input logic [3:0] in, output logic [3:0] out);
  genvar g;
  generate
    for (g = 0; g < 4; g = g + 1) begin : genu
      assign out[g] = in[g];
    end
  endgenerate
endmodule
module GenLoopZero(input logic [3:0] in, output logic [3:0] out);
  localparam M = 0;
  genvar k;
  generate
    for (k = 0; k < M; k = k + 1) begin : genz
      assign out[k] = in[k];
    end
  endgenerate
  assign out = in;
endmodule
module ForkExample(input logic a, b, output logic c, d);
  always_comb begin
    fork
      c = a & b;
      d = a | b;
    join
  end
endmodule
module ClassUse(input logic [3:0] a, output logic [3:0] b);
  class C;
    function logic [3:0] f(input logic [3:0] x);
      f = x ^ 4'hF;
    endfunction
  endclass
  always_comb begin
    C obj = new();
    b = obj.f(a);
  end
endmodule
module NestedFor(input logic [1:0] n, output logic [7:0] m);
  integer i, j;
  always_comb begin
    m = 0;
    for (i = 0; i < 2; i = i + 1)
      for (j = 0; j < 3; j = j + 1)
        m = m + i + j;
  end
endmodule
module FuncUnroll(input logic [3:0] n, output logic [7:0] fact);
  function automatic logic [7:0] fact_f(input logic [3:0] nn);
    logic [7:0] result;
    integer k;
    begin
      result = 1;
      for (k = 1; k <= nn; k = k + 1)
        result = result * k;
      fact_f = result;
    end
  endfunction
  always_comb begin
    fact = fact_f(n);
  end
endmodule
module ParamLoop(input logic [7:0] in, output logic [7:0] out);
  localparam P = 2;
  genvar idx;
  generate
    for (idx = 0; idx < P; idx = idx + 1) begin : gl
      assign out = in << idx;
    end
  endgenerate
endmodule
module MultipleIncError(input logic [3:0] a, output logic [3:0] b);
  logic [3:0] sum;
  integer i;
  always_comb begin
    sum = 0;
    for (i = 0; i < 4; i = i + 1, i = i + 2) begin
      sum = sum + a;
    end
  end
  assign b = sum;
endmodule
module VarAssignError(input logic [3:0] in, output logic [3:0] out);
  integer i;
  logic [3:0] temp;
  always_comb begin
    temp = in;
    for (i = 0; i < 3; i = i + 1) begin
      i = 5;
      temp = temp + i;
    end
  end
  assign out = temp;
endmodule
module ForkLoopError(input logic e, output logic f);
  integer i;
  logic e_temp;
  always_comb begin
    for (i = 0; i < 2; i = i + 1) begin
      fork
        e_temp = e;
      join
    end
  end
  assign f = e_temp;
endmodule
