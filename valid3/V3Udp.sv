primitive udp_and3 (y, a, b, c);
  output y;
  input  a, b, c;
  table
    0 0 0 : 0;
    0 0 1 : 0;
    0 1 0 : 0;
    0 1 1 : 0;
    1 0 0 : 0;
    1 0 1 : 0;
    1 1 0 : 0;
    1 1 1 : 1;
    ? ? x : x;
    x ? ? : x;
    ? x ? : x;
  endtable
endprimitive
primitive udp_or3 (y, a, b, c);
  output y;
  input  a, b, c;
  table
    0 0 0 : 0;
    0 0 1 : 1;
    0 1 0 : 1;
    0 1 1 : 1;
    1 0 0 : 1;
    1 0 1 : 1;
    1 1 0 : 1;
    1 1 1 : 1;
    ? ? x : x;
    x ? ? : x;
    ? x ? : x;
  endtable
endprimitive
primitive udp_mux2 (y, s, a, b);
  output y;
  input  s, a, b;
  table
    0 0 ? : 0;
    0 1 ? : 1;
    1 ? 0 : 0;
    1 ? 1 : 1;
    x ? ? : x;
  endtable
endprimitive
primitive udp_xnor2 (y, a, b);
  output y;
  input  a, b;
  table
    0 0 : 1;
    0 1 : 0;
    1 0 : 0;
    1 1 : 1;
    ? x : x;
    x ? : x;
  endtable
endprimitive
primitive udp_dff (q, clk, d);
  output q;
  reg    q;
  input  clk, d;
  table
    r 0 : ? : 0;
    r 1 : ? : 1;
    f ? : ? : -;
    * ? : ? : -;
  endtable
endprimitive
module mod_and3(
  input  logic a,
  input  logic b,
  input  logic c,
  output logic y
);
  assign y = a & b & c;
endmodule
module mod_or3(
  input  logic a,
  input  logic b,
  input  logic c,
  output logic y
);
  assign y = a | b | c;
endmodule
module mod_mux2(
  input  logic s,
  input  logic a,
  input  logic b,
  output logic y
);
  assign y = s ? b : a;
endmodule
module mod_xnor2(
  input  logic a,
  input  logic b,
  output logic y
);
  assign y = ~(a ^ b);
endmodule
module mod_dff(
  input  logic clk,
  input  logic d,
  output logic q
);
  always_ff @(posedge clk) q <= d;
endmodule
