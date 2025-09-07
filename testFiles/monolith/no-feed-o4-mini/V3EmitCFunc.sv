interface Ifc; logic sig; endinterface
module simple_ok(input logic [3:0] a, b, output logic [3:0] z);
  assign z = a + b;
endmodule
module op_name_test(input logic [7:0] x, y, output logic [7:0] u, v, w, s, shl, shr);
  assign u = -x;
  assign v = &y;
  assign w = |x;
  assign s = x ^ y;
  assign shl = x << 1;
  assign shr = y >> 2;
endmodule
module ternary_test(input logic a, input logic b, input logic [3:0] c, output logic [3:0] y);
  assign y = a ? c : b ? 4'd1 : 4'd0;
endmodule
module reduction_shift(input logic [7:0] x, output logic [7:0] y);
  assign y = ~|x << 1;
endmodule
module wide_ops(input logic [63:0] a, b, output logic [63:0] z);
  assign z = a + b;
endmodule
module ccall_dpi(input int a, output int b);
  import "DPI-C" function int foop(input int x);
  assign b = foop(a);
endmodule
module deref_module(input logic in, output logic out);
  Ifc ifc_inst();
  assign out = ifc_inst.sig;
endmodule
module cvt_pack_str(input logic [7:0] x, output string s);
  always_comb s = $sformatf("Val=%0d", x);
endmodule
module cvt_wide_array(input logic [15:0] in_arr [0:1], output logic [15:0] out_arr [0:1]);
  assign out_arr = in_arr;
endmodule
module constant_test(input logic [7:0] in, output logic [7:0] o1, output logic [63:0] o64, output real r);
  assign o1 = 8'd15;
  assign o64 = 64'hdead_beef_dead_beef;
  assign r = 3.14;
endmodule
module constant_string_test(input logic en, output string s);
  always_comb if (en) s = {"Hello"}; else s = "";
endmodule
module set_var_constant(input logic en, output logic [3:0] o);
  reg [3:0] r = 4'd9;
  assign o = en ? r : ~r;
endmodule
module var_reset_test(input logic clk, input logic rst, output logic [3:0] d);
  typedef struct packed { logic [1:0] f1; integer f2; } st_t;
  logic [1:0][3:0] arr2d;
  logic [3:0] arr_unp [0:3];
  string strvar;
  int dyn_arr [];
  int assoc_arr [string];
  int queue_arr [$];
  st_t st;
  always_ff @(posedge clk) if (rst) begin
    arr_unp[0] <= 4'd1;
    arr_unp[1] <= 4'd2;
    st.f1 <= 2'b01;
    st.f2 <= 10;
    strvar <= "A";
    dyn_arr = new[2];
    assoc_arr["key"] = 5;
    queue_arr.push_back(7);
  end
  assign d = arr_unp[0];
endmodule
module scan_format(input logic [7:0] in, output int out);
  string s;
  always_comb begin
    s = $sformatf("%02d", in);
    $sscanf(s, "%d", out);
  end
endmodule
