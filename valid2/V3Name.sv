package types_pkg;
  typedef struct packed {logic [3:0] a; logic [3:0] b;} pack_t;
  typedef union packed {logic [7:0] all; pack_t s;} union_t;
  typedef struct {logic [7:0] byte0; logic [7:0] byte1;} unpack_t;
endpackage
class simple_class;
  int mult_factor;
  function new(int mf = 2);
    mult_factor = mf;
  endfunction
  function int mult(int val);
    return val * mult_factor;
  endfunction
endclass
module keyword_escape_module(input  logic in_sig,
                             output logic out_sig);
  wire \if  = in_sig;
  assign out_sig = \if ;
endmodule
module packed_struct_module(input  logic [3:0] in_a,
                            input  logic [3:0] in_b,
                            output logic [7:0] out_all);
  import types_pkg::*;
  pack_t  local_pack;
  union_t local_union;
  always_comb begin
    local_pack.a = in_a;
    local_pack.b = in_b;
    local_union.s = local_pack;
    out_all      = local_union.all;
  end
endmodule
module public_child(input  logic in_c,
                    output logic out_c);
  assign out_c = ~in_c;
endmodule
module public_hier_module(input  logic in_h,
                          output logic out_h);
  logic mid;
  /*verilator public*/ logic pub_sig;
  public_child u_child (.in_c(in_h), .out_c(mid));
  assign pub_sig = mid;
  assign out_h   = pub_sig;
endmodule
module dpi_cfunc_module(input  logic [31:0] in1,
                        input  logic [31:0] in2,
                        output logic [31:0] sum);
  import "DPI-C" function int c_add(input int a, input int b);
  always_comb begin
    sum = c_add(int'(in1), int'(in2));
  end
endmodule
module unpack_struct_module(input  logic [7:0] in0,
                            input  logic [7:0] in1,
                            output logic [15:0] out_vec);
  import types_pkg::*;
  unpack_t us;
  always_comb begin
    us.byte0 = in0;
    us.byte1 = in1;
    out_vec  = {us.byte0, us.byte1};
  end
endmodule
module class_use_module(input  logic [31:0] in_val,
                        output logic [31:0] out_val);
  simple_class c;
  always_comb begin
    c = new(3);
    out_val = c.mult(int'(in_val));
  end
endmodule
