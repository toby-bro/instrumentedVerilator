package my_pkg;
  parameter int PKG_PARAM = 5;
  typedef enum logic [1:0] {S0, S1, S2, S3} my_enum_t;
endpackage
module mod_var(input  logic [7:0] a, output logic [7:0] b);
  logic [3:0] temp_var;
  assign temp_var = a[3:0];
  assign b = {temp_var, 4'hA};
endmodule
module mod_func(input  logic [3:0] in, output logic [3:0] out);
  function automatic logic [3:0] invert(input logic [3:0] x);
    invert = ~x;
  endfunction
  assign out = invert(in);
endmodule
module mod_class(input  logic [3:0] a, output logic [3:0] b);
  class Calc;
    function logic [3:0] add_one(input logic [3:0] x);
      add_one = x + 1;
    endfunction
  endclass
  always_comb begin
    Calc c = new();
    b = c.add_one(a);
  end
endmodule
module mod_struct_packed(input  logic [15:0] din, output logic [7:0] dout);
  typedef struct packed {
    logic [7:0] hi;
    logic [7:0] lo;
  } packed_s_t;
  typedef union packed {
    logic [15:0] word;
    packed_s_t parts;
  } packed_u_t;
  packed_u_t pu;
  assign pu.word = din;
  assign dout = pu.parts.lo;
endmodule
module mod_struct_unpacked(input  logic [15:0] din,
                           output logic [7:0] out0,
                           output logic [7:0] out1);
  typedef struct {
    logic [7:0] a;
    logic [7:0] b;
  } unpacked_s_t;
  unpacked_s_t arr [1:0];
  assign arr[0].a = din[7:0];
  assign arr[0].b = din[15:8];
  assign arr[1]   = arr[0];
  assign out0     = arr[1].a;
  assign out1     = arr[1].b;
endmodule
module mod_gen(input  logic        sel,
               input  logic [3:0]  din,
               output logic [7:0]  dout);
  genvar i;
  generate
    for (i = 0; i < 2; i = i + 1) begin : gen_loop
      assign dout[i*4 +: 4] = sel ? din : {4{i}};
    end
  endgenerate
endmodule
module child_sub(input  logic x, output logic y);
  assign y = ~x;
endmodule
module mod_cell_inst(input  logic in1, output logic out1);
  wire w1;
  child_sub u_child(.x(in1), .y(w1));
  assign out1 = w1;
endmodule
module mod_pkg(input  logic [1:0] sel, output my_pkg::my_enum_t out);
  import my_pkg::*;
  assign out = my_enum_t'(sel + PKG_PARAM);
endmodule
