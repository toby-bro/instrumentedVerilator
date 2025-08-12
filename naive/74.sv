package math_pkg;
function automatic logic [3:0] add4(input logic [3:0] x, y);
  add4 = x + y;
endfunction
endpackage
interface simple_if(input logic clk);
  logic en;
  logic [3:0] data;
  modport master(input clk, en, data);
  modport slave(output en, data, input clk);
endinterface
module comb_logic(input logic [3:0] a, b, output logic [3:0] y);
  always_comb y = a ^ b;
endmodule
module seq_logic(input logic clk, reset, d, output logic q);
  always_ff @(posedge clk or posedge reset) begin
    if (reset) q <= 1'b0;
    else      q <= d;
  end
endmodule
module param_gen #(parameter WIDTH = 8) (input logic [WIDTH-1:0] din, output logic [WIDTH-1:0] dout);
  genvar i;
  generate
    for (i = 0; i < WIDTH; i = i + 1) begin : gen_loop
      assign dout[i] = din[WIDTH-1-i];
    end
  endgenerate
endmodule
module array_bus(input logic [7:0] bus_in [3:0], output logic [7:0] bus_out [3:0]);
  genvar j;
  generate
    for (j = 0; j < 4; j = j + 1) begin : arr_loop
      assign bus_out[j] = bus_in[3-j];
    end
  endgenerate
endmodule
module struct_union(input logic in_valid, input logic [3:0] a, b, output logic [3:0] sum);
  typedef struct packed { logic [3:0] x; logic [3:0] y; } my_struct_t;
  typedef union packed { logic [7:0] all; my_struct_t s; } my_union_t;
  my_union_t u;
  always_comb begin
    u.s.x = a;
    u.s.y = b;
    sum  = u.s.x + u.s.y;
  end
endmodule
module task_func(input logic clk, input logic [3:0] in_data, output logic [3:0] out_data);
  function automatic logic [3:0] invert_bits(input logic [3:0] v);
    invert_bits = ~v;
  endfunction
  task automatic show_and_assign(input logic [3:0] v, output logic [3:0] out);
    out = invert_bits(v);
  endtask
  always_ff @(posedge clk) begin
    show_and_assign(in_data, out_data);
  end
endmodule
module case_uniq(input logic [1:0] sel, output logic [3:0] data_out);
  always_comb begin
    unique case (sel)
      2'b00: data_out = 4'hA;
      2'b01: data_out = 4'hB;
      2'b10: data_out = 4'hC;
      2'b11: data_out = 4'hD;
    endcase
  end
endmodule
module generate_if #(parameter USE_B = 1) (input logic a, b, output logic y);
  generate
    if (USE_B) begin
      assign y = a & b;
    end else begin
      assign y = a | b;
    end
  endgenerate
endmodule
module cover_assert(input logic clk, input logic en, input logic [3:0] data, output logic ok);
  covergroup cg @(posedge clk);
    coverpoint data;
    coverpoint en;
    cross data, en;
  endgroup
  cg my_cg = new();
  property p_never_zero;
    @(posedge clk) disable iff (!en) data != 4'd0;
  endproperty
  assert property (p_never_zero);
  always_ff @(posedge clk) begin
    ok <= en & (data != 4'd0);
  end
endmodule
module pkg_user(input logic [3:0] a, b, output logic [3:0] c);
  import math_pkg::*;
  always_comb c = add4(a, b);
endmodule
module if_user(input logic clk, input logic rst, output logic [3:0] out);
  simple_if i_f(clk);
  always_ff @(posedge clk or posedge rst) begin
    if (rst)         out <= '0;
    else if (i_f.en) out <= i_f.data;
    else             out <= out;
  end
endmodule
