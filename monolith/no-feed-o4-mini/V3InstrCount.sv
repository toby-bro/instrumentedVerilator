module sel_bit(input logic [7:0] din, input logic [2:0] sel, output logic dout);
  always_comb begin
    dout = din[sel];
  end
endmodule
module sel_range(input logic [31:0] din, input logic [4:0] msb, input logic [4:0] lsb, output logic [15:0] dout);
  always_comb begin
    dout = din[msb:lsb];
  end
endmodule
module dyn_partsel(input logic [31:0] din, input logic [4:0] pos, input logic [3:0] width, output logic [31:0] out_inc, output logic [31:0] out_dec);
  assign out_inc = din[pos +: width];
  assign out_dec = din[pos -: width];
endmodule
module concat_mod(input logic [3:0] a, input logic [3:0] b, input logic [3:0] c, input logic [3:0] d, output logic [15:0] out);
  assign out = {a, b, c, d};
endmodule
module if_else_mod(input logic cond, input logic [7:0] a, input logic [7:0] b, output logic [7:0] out);
  always_comb begin
    if (cond)
      out = a + 1;
    else
      out = b - 1;
  end
endmodule
module ternary_mod(input logic cond, input logic [7:0] a, input logic [7:0] b, output logic [7:0] out);
  assign out = cond ? a : b;
endmodule
module func_mod(input logic [7:0] a, input logic [7:0] b, output logic [7:0] out);
  function logic [7:0] add_f(input logic [7:0] x, input logic [7:0] y);
    add_f = x + y;
  endfunction
  assign out = add_f(a, b);
endmodule
module for_loop_mod(input logic [3:0] n, input logic [7:0] arr_in [0:15], output logic [7:0] arr_out [0:15]);
  integer i;
  always_comb begin
    for (i = 0; i < n; i = i + 1)
      arr_out[i] = arr_in[i] + i;
    for (i = n; i < 16; i = i + 1)
      arr_out[i] = 0;
  end
endmodule
module class_inst_mod(input logic clk, input logic rst, output logic [7:0] data);
  class C;
    rand logic [7:0] x;
    function new();
      x = 8'hFF;
    endfunction
  endclass
  C c_inst;
  always_ff @(posedge clk) begin
    if (rst) begin
      c_inst = new();
      data <= c_inst.x;
    end else begin
      data <= data;
    end
  end
endmodule
