module cont_assign(input wire in1, input wire [7:0] inbus, output wire out1, output wire outbit, output wire [3:0] outslice);
  assign out1 = in1;
  assign outbit = inbus[2];
  assign outslice = inbus[7:4];
endmodule
module proc_assign(input wire clk, input wire din, output reg dout);
  always @(posedge clk) begin
    dout <= din;
  end
endmodule
module comb_assign(input wire a, input wire b, output logic y);
  always_comb begin
    logic temp;
    temp = a & b;
    y = temp | a;
  end
endmodule
module slice_proc(input wire [15:0] bus_in, output reg [7:0] high_half, output reg low_bit);
  always @(*) begin
    high_half = bus_in[15:8];
    low_bit = bus_in[0];
  end
endmodule
module genvar_gen(input wire [3:0] inbus, output wire [3:0] outbus);
  genvar i;
  generate
    for (i = 0; i < 4; i = i + 1) begin : genblk
      assign outbus[i] = inbus[i];
    end
  endgenerate
endmodule
module param_mod #(parameter WIDTH = 4, parameter UNUSED_PARAM = 10) (input wire [WIDTH-1:0] inbus, output wire [WIDTH-1:0] outbus);
  assign outbus = inbus;
endmodule
module inout_mod(inout wire pin, input wire sel, output wire data_out);
  wire internal;
  assign internal = sel ? pin : 1'b0;
  assign data_out = internal;
endmodule
module multi_driver(input wire x, input wire y, output logic [1:0] a);
  always_comb a[0] = x;
  always_comb a[1] = y;
endmodule
interface simple_ifg(input logic a, output logic b);
endinterface
module interface_mod(input wire d, output wire q);
  simple_ifg ifc();
  assign ifc.b = d;
  assign q = ifc.b;
endmodule
