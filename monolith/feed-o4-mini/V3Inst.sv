interface IF1;
  logic [3:0] sig;
  modport master (input sig);
  modport slave (output sig);
endinterface
module simple_mod(input  [3:0] a, output [3:0] b);
  assign b = a;
endmodule
module const_mod(input  [3:0] a, output [3:0] b);
  assign b = 4'b1010;
endmodule
module zero_extend(input  [3:0] in, output [7:0] out);
  assign out = {4'b0, in};
endmodule
module sign_extend(input  signed [3:0] in, output signed [7:0] out);
  assign out = {{4{in[3]}}, in};
endmodule
module slice_mod(input  [7:0] in, output [3:0] out);
  assign out = in[3:0];
endmodule
module concat_mod(input  [1:0] a, input  [1:0] b, output [3:0] c);
  assign c = {a, b};
endmodule
module replicate_mod(input  a, output [3:0] b);
  assign b = {4{a}};
endmodule
module iface_single(input virtual IF1.master ifc, input logic ena, output [3:0] o);
  assign o = ena ? ifc.sig : 4'b0;
endmodule
module iface_array(input virtual IF1.master ifc_arr [0:1], input logic ena, output [3:0] o0, output [3:0] o1);
  assign o0 = ena ? ifc_arr[0].sig : 4'b0;
  assign o1 = ena ? ifc_arr[1].sig : 4'b0;
endmodule
module iface_array_assign(input logic        en, input virtual IF1.master    inarr [0:1], output logic done, output virtual IF1.slave outarr [0:1]);
  assign done = en;
  always_comb begin
    outarr[0].sig = inarr[0].sig;
    outarr[1].sig = inarr[1].sig;
  end
endmodule
module inst_tester(input  [7:0] in8, output [7:0] out8);
  wire [3:0] w4a;
  wire [3:0] w4b;
  zero_extend uz(.in(in8[3:0]), .out(w4a));
  slice_mod    sm(.in(in8),       .out(w4b));
  assign out8 = {w4a, w4b};
endmodule
module inst_tester2(input  [3:0] in4, output [7:0] out8);
  wire [3:0] w2;
  wire [3:0] w3;
  replicate_mod rm(.a(in4[1]),       .b(w2));
  concat_mod    cm(.a(in4[1:0]), .b(in4[3:2]), .c(w3));
  assign out8 = {w3, w2};
endmodule
