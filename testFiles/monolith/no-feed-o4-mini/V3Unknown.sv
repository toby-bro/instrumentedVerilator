typedef struct packed { logic [3:0] a; logic b; } my_t;
module mod_assign(input  logic [3:0] in1, in2, output logic [3:0] out);
  assign out = in1 + in2;
endmodule
module mod_delayed(input  logic        clk,
                   input  logic [7:0]  data,
                   output logic [7:0]  q);
  always_ff @(posedge clk) q <= data;
endmodule
module mod_case(input  logic [1:0] sel,
                input  logic [3:0] data,
                output logic [3:0] out);
  always_comb begin
    case (sel)
      2'b00: out = data;
      2'b01: out = 4'b1010;
      2'b1?: out = 4'bz1z0;
      default: out = 4'bx1xz;
    endcase
  end
endmodule
module mod_casex(input  logic [1:0] sel,
                 input  logic [3:0] data,
                 output logic [3:0] out);
  always_comb casex (sel)
    2'bx1: out = data;
    default: out = 4'bx1xz;
  endcase
endmodule
module mod_casez(input  logic [1:0] sel,
                 input  logic [3:0] data,
                 output logic [3:0] out);
  always_comb casez (sel)
    2'bz1: out = data;
    default: out = 4'bx1xz;
  endcase
endmodule
module mod_eqneq(input  logic [3:0] a, b,
                 output logic       eq_e,
                 output logic       eq_se,
                 output logic       neq_ne,
                 output logic       neq_sn);
  assign eq_e  = (a == b);
  assign eq_se = (a === b);
  assign neq_ne = (a != b);
  assign neq_sn = (a !== b);
endmodule
module mod_popcount(input  logic [7:0] in,
                    output logic [3:0] count);
  assign count = $countones(in);
endmodule
module mod_bit_sel(input  logic [3:0] vec,
                   input  logic [2:0] idx,
                   output logic       bit_out);
  assign bit_out = (idx < 4) ? vec[idx] : 1'bx;
endmodule
module mod_array_sel(input  logic [7:0] arr_in [0:3],
                     input  logic [1:0] idx,
                     output logic [7:0] elt_out);
  assign elt_out = (idx < 4) ? arr_in[idx] : 8'bx;
endmodule
module mod_slice(input  logic [7:0] in,
                 output logic [3:0] slice);
  assign slice = in[7:4];
endmodule
module mod_var_init(input  logic [3:0] in,
                    output logic [3:0] out);
  logic [4:0] temp = 5'bx1xz0;
  assign out = temp[3:0] & in;
endmodule
module mod_struct(input  my_t        s,
                  output logic       flag,
                  output logic [3:0] aval);
  assign aval = s.a;
  assign flag = s.b;
endmodule
