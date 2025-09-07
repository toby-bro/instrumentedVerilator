primitive udp_and (out, a, b);
    output out;
    input  a, b;
    table
       0  0 : 0;
       0  1 : 0;
       1  0 : 0;
       1  1 : 1;
       ?  ? : x;
    endtable
endprimitive
primitive udp_mux (out, sel, in1, in0);
    output out;
    input  sel, in1, in0;
    table
       0   ?   0  : 0;
       0   ?   1  : 1;
       1   0   ?  : 0;
       1   1   ?  : 1;
       ?   x   x  : x;
    endtable
endprimitive
primitive udp_dff (q, clk, d);
    output q;
    input  clk, d;
    reg    q;
    table
       r  0 : ? : 0;
       r  1 : ? : 1;
       f  ? : ? : -;
       *  ? : ? : -;
       ?  ? : 0 : 0;
       ?  ? : 1 : 1;
    endtable
endprimitive
primitive udp_edgedff (q, clk, data);
    output q;
    input  clk, data;
    reg    q;
    table
      01   0    : ? : 0;
      01   1    : ? : 1;
      10   ?    : ? : -;
       ?   ?    : 0 : 0;
       ?   ?    : 1 : 1;
    endtable
endprimitive
module wrapper_and (
    input  logic a,
    input  logic b,
    output logic y
);
    udp_and u_and (y, a, b);
endmodule
module wrapper_mux (
    input  logic sel,
    input  logic in1,
    input  logic in0,
    output logic y
);
    udp_mux u_mux (y, sel, in1, in0);
endmodule
module wrapper_dff (
    input  logic clk,
    input  logic d,
    output logic q
);
    udp_dff u_dff (q, clk, d);
endmodule
module wrapper_edgedff (
    input  logic clk,
    input  logic data,
    output logic q
);
    udp_edgedff u_edgedff (q, clk, data);
endmodule
module pass_through (
    input  logic i,
    output logic o
);
    assign o = i;
endmodule
