module m1(input logic [7:0] a, input logic [7:0] b, output logic [7:0] c);
  function logic [7:0] add(input logic [7:0] x, input logic [7:0] y);
    add = x + y;
  endfunction
  assign c = add(a, b);
endmodule
module m2(input logic in, output supply0 out0, output supply1 out1);
  supply0 net0;
  supply1 net1;
  assign net0 = in;
  assign net1 = in;
  assign out0 = net0;
  assign out1 = net1;
endmodule
module m_unsized(input logic clk, output logic d);
  logic arr[];
  logic arr2 [][3:0];
  logic que[$];
  logic dyn[];
  logic assoc[int];
  logic assoc_str[string];
  assign d = clk;
endmodule
module m_sel(input logic [3:0] a [1:0], input logic [1:0] b, output logic [1:0] r);
  assign r = a[b[0]][2:1];
endmodule
module m_arrays(input logic [7:0] x, output logic [7:0] y, output logic [3:0] z);
  logic [7:0] packed_arr;
  logic unpacked_arr [3:0];
  logic dyn_arr[];
  logic que_arr[$];
  logic assoc_arr[int];
  logic sp_arr[*];
  assign packed_arr = x;
  assign unpacked_arr[2] = x[0];
  assign y = packed_arr[x[2+:4]];
  assign z = x[3-:2];
endmodule
module m_property(input logic clk, input logic rst, input logic d, output logic q);
  property p1(logic a, logic b);
    @(posedge clk) disable iff (rst) a |-> b;
  endproperty
  assert property (p1(d, q));
endmodule
module m_string(input logic sel, output string sout);
  parameter string sin = "hello";
  assign sout = sin;
endmodule
module m_portansi(input logic a, output logic b, output logic c);
  assign b = a;
  assign c = ~a;
endmodule
module m_portnon(d1, q1);
  input logic d1;
  output logic q1;
  assign q1 = d1;
endmodule
module m_generate(input logic go, output logic done);
  genvar i;
  generate
    for (i = 0; i < 4; i = i + 1) begin : gen_loop
      wire w = go;
    end
  endgenerate
  assign done = go;
endmodule
