module mod_countones(input  logic [7:0] in, output logic [3:0] out);
  function automatic logic [3:0] countones(input logic [7:0] x);
    int i;
    begin
      countones = 0;
      for (i = 0; i < 8; i = i + 1)
        countones = countones + x[i];
    end
  endfunction
  assign out = countones(in);
endmodule
module mod_replicate(input  logic [1:0] in, output logic [7:0] out);
  assign out = {4{in}};
endmodule
module mod_bitrange(input  logic [15:0] in, output logic [7:0] low, output logic [7:0] high);
  assign low  = in[7:0];
  assign high = in[15:8];
endmodule
module mod_inside(input  logic [3:0] value, output logic flag);
  assign flag = (value == 4'd0) || (value == 4'd1) || (value == 4'd2) || (value == 4'd3);
endmodule
module mod_array_unpack(input  logic [3:0] arr [0:3], input logic [1:0] idx, output logic [3:0] val);
  assign val = arr[idx];
endmodule
module mod_dynamic_array(input  logic [3:0] da[], output logic [3:0] val);
  always_comb begin
    val = da[da.size()-1];
  end
endmodule
module mod_struct(input  struct packed { bit x; bit y; } s, output logic y_out);
  assign y_out = s.y;
endmodule
module mod_class_randomize(input  logic [3:0] in_var, output logic [3:0] out_var);
  class C; rand bit [3:0] a; endclass
  C c;
  always_comb begin
    c = new();
    c.randomize();
    out_var = c.a ^ in_var;
  end
endmodule
module mod_class_inline(input  logic [3:0] in_var, output logic ok);
  class D; rand bit [3:0] a; endclass
  D d;
  always_comb begin
    d = new();
    if (d.randomize() with { a inside {4'h3,4'h5}; })
      ok = 1;
    else
      ok = 0;
  end
endmodule
module mod_class_rand_mode(input  logic [3:0] in_var, output logic [3:0] out_var);
  class E; rand bit [3:0] a; endclass
  E e;
  always_comb begin
    e = new();
    e.a.rand_mode(1);
    e.randomize();
    out_var = e.a + in_var;
  end
endmodule
