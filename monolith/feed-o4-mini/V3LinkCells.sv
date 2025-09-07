package pkg1;
  typedef logic [7:0] byte_t;
endpackage
package P_class;
  class CBase;
  endclass
  class CDerived extends CBase;
  endclass
endpackage
interface I1(input logic clk);
  logic d;
  modport master(input d);
endinterface
module M2(input logic a, output logic b);
  assign b = a;
endmodule
module M1(input logic in_sig, output logic out_sig);
  wire a_sig;
  assign a_sig = in_sig;
  M2 inst1(.a(a_sig), .b(out_sig));
endmodule
module M3(input interface I1.master vif, input logic sel, output logic outp);
  assign outp = sel ? vif.d : 1'b0;
endmodule
module M4(input logic x, output pkg1::byte_t y);
  import pkg1::*;
  byte_t z;
  assign z = {1'b0, x, 6'b0};
  assign y = z;
endmodule
module M6(input logic en, output logic rd);
  import P_class::*;
  typedef CBase ctype_t;
  ctype_t obj;
  always_comb begin
    obj = new CDerived();
    rd = en;
  end
endmodule
module M7 #(parameter int N = 8) (input logic [N-1:0] din, output logic [N-1:0] dout);
  typedef logic [N/2-1:0] half_t;
  typedef enum logic [1:0] {IDLE, BUSY, DONE} state_t;
  localparam int LP = 4;
  half_t idx;
  state_t st;
  assign idx = din[N/2-1:0];
  assign st = (din[0] ? BUSY : IDLE);
  assign dout = din;
endmodule
module M5(input logic clk, input logic [7:0] in_vec [3:0], output logic [7:0] vec_out [3:0]);
  genvar i;
  generate
    for (i = 0; i < 4; i = i + 1) begin : genblk
      wire [7:0] din_sig;
      wire [7:0] dout_sig;
      assign din_sig = in_vec[i];
      M7 #(.N(8)) uM7(.din(din_sig), .dout(dout_sig));
      assign vec_out[i] = dout_sig;
    end
  endgenerate
endmodule
