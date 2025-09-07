class MyClass;
  rand bit [7:0] data;
  function void operate(bit [7:0] in, output bit [7:0] out);
    out = in ^ data;
  endfunction
endclass
module class_example(input logic [7:0] a, output logic [7:0] out);
  MyClass obj;
  always_comb begin
    obj = new();
    obj.operate(a, out);
  end
endmodule
module if_example(input logic a, input logic b, output logic y);
  always_comb begin
    if (a & b) begin
      y = 1;
    end else begin
      y = 0;
    end
  end
endmodule
module for_loop_example(input logic [7:0] a, output logic [7:0] result);
  logic [7:0] sum;
  always_comb begin
    sum = 0;
    for (int idx = 0; idx < 8; idx = idx + 1) begin
      sum = sum + a[idx];
    end
  end
  assign result = sum;
endmodule
module while_example(input logic [3:0] a, output logic [7:0] result);
  always_comb begin
    int i;
    result = 0;
    i = 0;
    while (i < 4) begin
      result = result + a[i];
      i = i + 1;
    end
  end
endmodule
module fork_example(input logic clk, input logic [3:0] in, output logic [3:0] out);
  always_ff @(posedge clk) begin
    logic [3:0] tmp1, tmp2;
    fork
      tmp1 = in + 1;
      tmp2 = in - 1;
    join_none
    out <= tmp1 ^ tmp2;
  end
endmodule
module genfor_example(input logic [1:0] a, output logic [3:0] outbus);
  genvar gi;
  generate
    for (gi = 0; gi < 4; gi = gi + 1) begin : gen_loop
      assign outbus[gi] = a[0];
    end
  endgenerate
endmodule
module genfor_zero(input logic a, output logic b);
  genvar iz;
  generate
    for (iz = 0; iz < 0; iz = iz + 1) begin : zero_loop
      assign b = a;
    end
  endgenerate
endmodule
function automatic int nested_func(int x);
  int j;
  nested_func = 0;
  for (j = 0; j < x; j = j + 1) begin
    nested_func = nested_func + j;
  end
endfunction
module nested_example(input logic [3:0] a, output logic [7:0] out);
  always_comb begin
    out = nested_func(a);
  end
endmodule
module constify_example(input logic [1:0] sel, input logic [7:0] a, input logic [7:0] b, output logic [7:0] y);
  localparam int CONSTVAL = 5;
  logic [7:0] tmp;
  always_comb begin
    tmp = (sel == CONSTVAL) ? a : b;
    y = tmp;
  end
endmodule
