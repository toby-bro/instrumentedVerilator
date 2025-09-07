class DistClass;
  rand bit [7:0] a;
  constraint c1 { a dist { 1 := 10, 2 := 20 }; }
endclass
class ConstraintClass;
  rand bit [3:0] b;
  constraint cb { b > 2; }
endclass
module varref_mod(input logic [3:0] in, output logic [3:0] out);
  assign out = in;
endmodule
module assign_mod(input logic sig, output logic out);
  logic tmp;
  always_comb tmp = sig;
  assign out = tmp;
endmodule
module pin_mod(input wire p_in, output wire p_out);
  wire internal;
  assign internal = p_in;
  assign p_out = internal;
endmodule
module force_release_mod(input logic y, output logic x);
  always_comb begin
    force x = y;
    release x;
  end
endmodule
module cast_dynamic_mod(input logic [7:0] a, output logic signed [7:0] b);
  assign b = $signed(a);
endmodule
module ferror_mod(input int fh, input string s, output int e);
  assign e = $ferror(fh, s);
endmodule
module fgets_mod(input int fh, input string buf, output int r);
  assign r = $fgets(buf, fh);
endmodule
module fread_mod(input int fh, output int r);
  logic [7:0] mem [0:15];
  assign r = $fread(mem, fh);
endmodule
module fscanf_mod(input int fh, input string fmt, output int c, output int v);
  assign c = $fscanf(fh, fmt, v);
endmodule
module fungetc_mod(input int fh, input int ch, output int r);
  assign r = $ungetc(ch, fh);
endmodule
module sscan_mod(input string s, input string fmt, output int r, output int v);
  assign r = $sscanf(s, fmt, v);
endmodule
module rand_mod(output int r1, output int r2);
  assign r1 = $urandom;
  assign r2 = $random;
endmodule
module testplusargs_mod(output bit ok);
  assign ok = $test$plusargs("ARG");
endmodule
module valueplusargs_mod(output bit ok, output int v);
  assign ok = $value$plusargs("ARG", v);
endmodule
module prepost_mod(input logic [3:0] a, input logic [3:0] b, output logic [5:0] sum);
  logic [3:0] x = a, y = b;
  always_comb sum = (++x) + (y++) + (--x) + (y--);
endmodule
module partselect_mod(input logic [7:0] data, output logic bit_out, output logic [2:0] part_out);
  assign bit_out = data[3];
  assign part_out = data[5:3];
endmodule
module dynpart_mod(input logic [7:0] data, input logic [2:0] off, input logic [2:0] w, output logic [2:0] up, output logic [2:0] down);
  assign up   = data[off +: w];
  assign down = data[off -: w];
endmodule
typedef struct { int f; bit [1:0] g; } MyStruct;
module member_sel_mod(input MyStruct s_in, output int f_out, output bit [1:0] g_out);
  assign f_out = s_in.f;
  assign g_out = s_in.g;
endmodule
function automatic int myfunc(input int v);
  return v + 1;
endfunction
module ftaskref_mod(input int in, output int out);
  assign out = myfunc(in);
endmodule
module constraint_mod(input bit clk, output bit done);
  ConstraintClass cc = new;
  always_comb begin
    cc.randomize();
    done = (cc.b > 0);
  end
endmodule
module distbin_mod(input bit clk, output bit done);
  DistClass dc = new;
  always_comb begin
    dc.randomize();
    done = (dc.a != 0);
  end
endmodule
module generic_node_mod(input logic [1:0] a, output logic [1:0] b);
  wire [1:0] tmp = a + 1;
  assign b = tmp;
endmodule
