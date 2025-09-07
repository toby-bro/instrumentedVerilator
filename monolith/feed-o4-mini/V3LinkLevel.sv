timeunit 1ns;
timeprecision 1ps;
package PkgWrap;
  typedef struct packed {
    bit [3:0] field;
  } pkg_struct_t;
  function automatic int pkg_func(input int x);
    return x * 2;
  endfunction
endpackage
interface Ifc;
  logic sig;
  modport im(input sig);
  modport om(output sig);
endinterface
module cmpLevel_mod(input logic [7:0] lvl_lhs, input logic [7:0] lvl_rhs, output logic cmp);
  class CmpLevel;
    function bit compare(logic [7:0] a, logic [7:0] b);
      return a < b;
    endfunction
  endclass
  always_comb begin
    static CmpLevel c = new();
    cmp = c.compare(lvl_lhs, lvl_rhs);
  end
endmodule
module modSortByLevel_mod(input logic [7:0] levels [0:7], output logic [7:0] sorted_levels [0:7]);
  integer i, j;
  logic [7:0] temp;
  always_comb begin
    for (i = 0; i < 8; i = i + 1)
      sorted_levels[i] = levels[i];
    for (i = 0; i < 8; i = i + 1) begin
      for (j = i + 1; j < 8; j = j + 1) begin
        if (sorted_levels[i] > sorted_levels[j]) begin
          temp = sorted_levels[i];
          sorted_levels[i] = sorted_levels[j];
          sorted_levels[j] = temp;
        end
      end
    end
  end
endmodule
module timescaling_mod(input time in_time, output time out_time);
  assign out_time = in_time;
endmodule
module wrapTop_mod(input bit [3:0] in_field, output bit [3:0] out_field);
  import PkgWrap::*;
  pkg_struct_t s;
  assign s.field = in_field;
  assign out_field = pkg_func(s.field);
endmodule
module wrapTopCell_mod(input logic [3:0] arr_in [0:3], output logic [3:0] arr_out [0:3]);
  Ifc ifc_inst();
  logic [3:0] arr_tmp [0:3];
  genvar gi;
  generate
    for (gi = 0; gi < 4; gi = gi + 1) begin : gen_loop
      assign arr_tmp[gi] = arr_in[gi] + 1;
    end
  endgenerate
  always_comb begin
    for (int k = 0; k < 4; k = k + 1) begin
      arr_out[k] = arr_tmp[k];
    end
  end
endmodule
module dumpTreeLevel_mod(input logic [7:0] in_vec [0:3], output logic [7:0] out_vec [0:3]);
  genvar i;
  generate
    for (i = 0; i < 4; i = i + 1) begin : LEVEL_LOOP
      assign out_vec[i] = in_vec[i] ^ 8'hFF;
    end
  endgenerate
endmodule
module dumpTreeJsonLevel_mod(input logic [7:0] idx, output logic [7:0] len);
  string s;
  function automatic string make_json(input int id);
    return $sformatf("{\"id\":%0d}", id);
  endfunction
  always_comb begin
    s = make_json(idx);
    len = s.len();
  end
endmodule
module debug_mod(input logic a, output logic ok);
  class DebugClass;
    function bit check(input bit v);
      return v;
    endfunction
  endclass
  always_comb begin
    static DebugClass dbg = new();
    ok = dbg.check(a);
  end
endmodule
module dynamic_mod(input int size, output int last);
  int darr[];
  always_comb begin
    darr = new[size];
    foreach (darr[i]) darr[i] = i;
    last = darr[size-1];
  end
endmodule
