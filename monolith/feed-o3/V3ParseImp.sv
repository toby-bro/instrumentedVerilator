`timescale 1ns/1ps
package pkg;
  parameter int P = 8;
endpackage : pkg
import pkg::*;
interface IFACE (input logic clk);
  logic sig;
  modport mp (input sig);
endinterface : IFACE
module strength_mod (input logic in_sig, output logic out_sig);
  assign (strong1, weak0) out_sig = in_sig;
endmodule
module labelled_block_mod (input logic [7:0] data_in, output logic [7:0] data_out);
  always_comb begin
    LABEL_BLK: begin
      data_out = data_in;
    end
  end
endmodule
module constref_mod (input logic [31:0] in_val, output logic [31:0] out_val);
  function automatic logic [31:0] id_func (const ref logic [31:0] v);
    id_func = v;
  endfunction
  assign out_val = id_func(in_val);
endmodule
module new_mod (input logic clk, output logic ok);
  class C;
     bit dummy;
  endclass
  C c_inst;
  always_ff @(posedge clk) begin
    if (c_inst == null) c_inst = new();
  end
  assign ok = (c_inst != null);
endmodule
module vif_mod (input logic clk, input logic sig_in, output logic sig_out);
  virtual IFACE.mp v_mp;
  assign sig_out = sig_in ^ (v_mp == null);
endmodule
module localscope_mod (input logic [3:0] din, output logic [3:0] dout);
  class Base;
     static int val1 = 1;
  endclass
  class Derived extends Base;
     static int val2 = 2;
     function int get_val();
        return val2;
     endfunction
  endclass
  Derived d;
  always_comb begin
    if (d == null) d = new();
    dout = din ^ d.get_val();
  end
endmodule
module randomize_with_mod (input logic [3:0] din, output logic [3:0] dout);
  class RandC;
     rand int value;
     static constraint c_static { value inside {[0:15]}; }
  endclass
  RandC r;
  function automatic int get_rand();
    if (r == null) r = new();
    void'(r.randomize() with { value > 3; });
    return r.value;
  endfunction
  assign dout = din ^ get_rand();
endmodule
module pathpulse_mod (input logic x, output logic y);
  logic PATHPULSE__024signal;
  always_comb begin
    PATHPULSE__024signal = x;
    y = PATHPULSE__024signal;
  end
endmodule
module pkg_scope_mod (input logic [P-1:0] a, output logic [P-1:0] b);
  assign b = pkg::P ? a : {P{1'b0}};
endmodule
