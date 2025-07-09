`timescale 1ns/1ps
`resetall
`default_nettype wire
`unconnected_drive pull0
`line 100 "generated.sv" 0
`begin_keywords "1800-2017"
`define MULT2(x) ((x)*2)
`define SUM2(a,b) ((a)+(b))
`define SELECT_PASS
`define MUX(sel,a,b) ((sel)?(a):(b))
`pragma protect reset
module mod_define(input  logic [7:0] a,
                  input  logic [7:0] b,
                  output logic [7:0] y);
    assign y = `MULT2(`SUM2(a,b));
endmodule
module mod_ifdef(input  logic        sel,
                 input  logic        in0,
                 output logic        out0);
`ifdef SELECT_PASS
    assign out0 = in0;
`else
    assign out0 = ~in0;
`endif
endmodule
`celldefine
module mod_cell(input  wire a,
                output wire y);
    assign y = a;
endmodule
`endcelldefine
`default_decay_time 100
`default_trireg_strength 1
module mod_mux(input  logic        sel,
               input  logic [3:0]  in_a,
               input  logic [3:0]  in_b,
               output logic [3:0]  out_y);
    assign out_y = `MUX(sel,in_a,in_b);
endmodule
`nounconnected_drive
`default_nettype none
`end_keywords
module mod_after(input  logic a,
                 output logic b);
    assign b = a;
endmodule
`undef SELECT_PASS
`undef MULT2
`undef SUM2
`undef MUX
`undefineall
