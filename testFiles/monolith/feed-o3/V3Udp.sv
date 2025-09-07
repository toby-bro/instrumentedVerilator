primitive comb_logic (y, a, b, c);
  output y;
  input  a, b, c;
  table
    0 0 0 : 0;
    0 0 1 : 1;
    0 1 0 : 0;
    0 1 1 : 1;
    1 0 0 : 1;
    1 0 1 : 0;
    1 1 0 : 1;
    1 1 1 : 0;
    x ? ? : x;
    ? x ? : x;
  endtable
endprimitive
module comb_module(
  input  wire a,
  input  wire b,
  input  wire c,
  output wire y
);
  comb_logic u_comb (y, a, b, c);
endmodule
primitive edge_dff (q, clk, d);
  output q;
  reg q;
  input  clk, d;
  table
    (01) 0 : ? : 0;
    (01) 1 : ? : 1;
    r    0 : ? : 0;
    r    1 : ? : 1;
    f    ? : ? : -;
    *    ? : ? : -;
    ?    ? : ? : -;
  endtable
endprimitive
module seq_module(
  input  wire clk,
  input  wire d,
  output wire q
);
  edge_dff u_dff (q, clk, d);
endmodule
primitive toggle_ff (q, clk, t);
  output q;
  reg q;
  input  clk, t;
  table
    (01) 0 : ? : -;
    (01) 1 : 0 : 1;
    (01) 1 : 1 : 0;
    r    0 : ? : -;
    r    1 : 0 : 1;
    r    1 : 1 : 0;
    *    ? : ? : -;
    ?    ? : ? : -;
  endtable
endprimitive
module toggle_module(
  input  wire clk,
  input  wire t,
  output wire q
);
  toggle_ff u_toggle (q, clk, t);
endmodule
primitive sync_clear (q, clk, clr);
  output q;
  reg q;
  input  clk, clr;
  table
    (01) 1 : ? : 0;
    (01) 0 : 0 : 0;
    (01) 0 : 1 : 1;
    r    1 : ? : 0;
    r    0 : 0 : 0;
    r    0 : 1 : 1;
    *    ? : ? : -;
    ?    ? : ? : -;
  endtable
endprimitive
module sync_module(
  input  wire clk,
  input  wire clr,
  output wire q
);
  sync_clear u_sync (q, clk, clr);
endmodule
