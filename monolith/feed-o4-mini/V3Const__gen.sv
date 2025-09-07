module is_pow2(input logic [31:0] v, output logic pow2);
  assign pow2 = (v & (v - 1)) == 0;
endmodule
module count_trailing_zeroes(input logic [31:0] v, output logic [5:0] tz);
  function automatic [5:0] ctz(input logic [31:0] v_in);
    int j;
    begin
      ctz = 0;
      for (j = 0; j < 32; j = j + 1) begin
        if (v_in[j]) begin
          ctz = j;
          break;
        end
      end
    end
  endfunction
  assign tz = (v != 0) ? ctz(v) : 6'd0;
endmodule
module bit_slice(input logic [31:0] data, input logic [4:0] idx, output logic bit_out);
  assign bit_out = data[idx];
endmodule
module word_sel(input logic [127:0] data, input logic [1:0] widx, output logic [31:0] word);
  assign word = data[(widx * 32) +: 32];
endmodule
module concat_rep(input logic [7:0] a, b, output logic [15:0] conc, output logic [15:0] rep2);
  assign conc = {a, b};
  assign rep2 = {2{a}};
endmodule
module cond_assign(input logic sel, input logic [3:0] a, output logic [3:0] out);
  assign out = sel ? a : 4'b1111;
endmodule
module reduce_tree(input logic [7:0] in, output logic and_o, or_o, xor_o);
  assign and_o = &in;
  assign or_o  = |in;
  assign xor_o = ^in;
endmodule
module eq_case(input logic [3:0] a, b, output logic eq);
  assign eq = (a == b) ? 1'b1 : 1'b0;
endmodule
module big_arith(input logic signed [15:0] x, input logic [3:0] y, output logic signed [15:0] out);
  assign out = (x << y) + x - y;
endmodule
module type_cast_range(input logic [7:0] a, output logic [3:0] b);
  assign b = a[7:4];
endmodule
module generate_example #(parameter int N = 8)(input logic [N-1:0] in, output logic [N-1:0] out);
  genvar i;
  generate
    for (i = 0; i < N; i = i + 1) begin
      assign out[i] = in[i] & in[(i + 1) % N];
    end
  endgenerate
endmodule
module class_example(input logic clk, input logic rst, input logic [7:0] in, output logic [7:0] out);
  class CExp;
    int rnd;
    function new(); rnd = 0; endfunction
    function void execute(int v); rnd = v * 2; endfunction
    function int get(); return rnd; endfunction
  endclass
  CExp c;
  always_ff @(posedge clk) begin
    if (rst)
      c = new();
    else begin
      c = new();
      c.execute(in);
    end
    out <= c.get();
  end
endmodule
