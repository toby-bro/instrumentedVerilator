package pkg;
typedef struct packed { logic [3:0] a; logic [1:0] b; } my_struct_t;
endpackage
interface intf_if(input logic clk);
  logic sig;
endinterface
(* keep = "yes" *) module attr_test(input logic a, output logic b);
  assign b = a;
endmodule
module nonansi(a, b, c);
  input a;
  output b;
  inout c;
  wire [3:0] bus;
  assign bus = 4'b1010;
  assign b = bus[2];
endmodule
module param_test#(parameter int WIDTH = 4)(input logic [WIDTH-1:0] in, output logic [WIDTH-1:0] out);
  assign out = in;
endmodule
module function_test(input logic [3:0] a, input logic [3:0] b, output logic [3:0] out);
  function automatic logic [3:0] add(input logic [3:0] x, input logic [3:0] y);
    add = x + y;
  endfunction
  assign out = add(a, b);
endmodule
module supply_test(input logic sig, supply0 net0, supply1 net1);
  assign net0 = sig;
  assign net1 = ~sig;
endmodule
module array_test(input logic [2:0] sel, input logic [7:0] pinc[], output logic bit_out);
  logic [7:0] packed_vec;
  logic [7:0] unpacked_vec [0:3];
  logic [7:0] dyn_arr[];
  logic [1:0] queue_arr[$];
  logic [31:0] assoc_arr[string];
  assign packed_vec = pinc[0];
  assign unpacked_vec[sel[1:0]] = packed_vec;
  assign dyn_arr = unpacked_vec;
  assign queue_arr = '{unpacked_vec[0], unpacked_vec[1]};
  assign assoc_arr["key"] = 32'hFF;
  assign bit_out = packed_vec[*];
endmodule
module dynport(input logic data_dyn[], output logic out_dyn);
  assign out_dyn = data_dyn[0];
endmodule
module multidim(input logic [1:0] sel, input logic [3:0] data2d [0:1], output logic outbit);
  assign outbit = data2d[sel[0]][sel[1]];
endmodule
module part_sel(input wire [7:0] bus_in, output wire [3:0] part_hi, output wire bit_lo);
  assign part_hi = bus_in[5:2];
  assign bit_lo = bus_in[3 +: 1];
endmodule
module if_use(input logic in_sig, interface intf_if iface, output logic out_sig);
  assign out_sig = in_sig & iface.sig;
endmodule
module pkg_use(input pkg::my_struct_t st, output logic out);
  assign out = st.a & st.b;
endmodule
module param_array#(parameter int N = 4)(input logic [7:0] din [N], output logic [7:0] dout [N]);
  assign dout = din;
endmodule
module mixed_sel(input logic [7:0] vec, input logic [2:0] idx, output logic bit0, output logic [1:0] slice);
  assign bit0 = vec[idx];
  assign slice = vec[5 -: 2];
endmodule
