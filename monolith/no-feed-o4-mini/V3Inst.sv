interface Intf; logic sig; endinterface
typedef struct packed { logic a; logic [2:0] b; } my_t;
class C; function void foo(input int a, output int b); b = a + 1; endfunction endclass
module simple_assign(input wire [3:0] a, output wire [3:0] b);
  assign b = a;
endmodule
module width_increase(input wire [3:0] a, output wire [7:0] b);
  assign b = a;
endmodule
module width_decrease(input wire [7:0] a, output wire [3:0] b);
  assign b = a;
endmodule
module signed_mismatch(input signed [3:0] a, output signed [7:0] b);
  assign b = a;
endmodule
module const_assign(input wire sel, output wire [3:0] b);
  assign b = sel ? 4'hA : 4'h5;
endmodule
module slice_mod(input wire [7:0] in, output wire [3:0] out);
  assign out = in[5:2];
endmodule
module inout_mod(inout wire [3:0] bus, input wire [3:0] data, input wire sel, output wire ack);
  assign bus = sel ? data : 4'bzzzz;
  assign ack = sel & data[0];
endmodule
module struct_mod(input my_t in_data, output my_t out_data);
  assign out_data = in_data;
endmodule
module pack_unpack(input wire [1:0] a,b,c,d, output wire [7:0] out);
  assign out = {a,b,c,d};
endmodule
module replicate_mod(input wire [1:0] a, output wire [7:0] out);
  assign out = {4{a}};
endmodule
module element_select(input wire [7:0] arr [1:0], output wire bit_out);
  assign bit_out = arr[1][4];
endmodule
module gen_mod #(parameter N = 3) (input wire [3:0] data [N-1:0], output wire [3:0] out [N-1:0]);
  genvar i;
  generate
    for (i = 0; i < N; i = i + 1) begin : GEN
      assign out[i] = data[i];
    end
  endgenerate
endmodule
module interface_mod(input interface Intf in_if, output wire sig_out);
  assign sig_out = in_if.sig;
endmodule
module interface_prod(output interface Intf out_if, input wire val);
  assign out_if.sig = val;
endmodule
module arr_if_mod(input interface Intf arr_if [1:0], output wire val);
  assign val = arr_if[0].sig;
endmodule
module class_mod(input int x, output int y);
  C c;
  always_comb begin
    c = new();
    c.foo(x, y);
  end
endmodule
module param_mod #(parameter P = 8) (input wire [P-1:0] in, output wire [P-1:0] out);
  assign out = in;
endmodule
module tri_mod(inout tri [3:0] bus, input wire [3:0] data, input wire sel, output wire [3:0] out);
  assign bus = sel ? data : 'bz;
  assign out = bus;
endmodule
