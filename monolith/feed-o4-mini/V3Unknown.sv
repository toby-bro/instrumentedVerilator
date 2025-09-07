module mod_assign(input [3:0] in, output [3:0] out);
  assign out = in;
endmodule
module mod_blocking(input clk, input [7:0] d, output reg [7:0] q);
  always_ff @(posedge clk) begin
    q = d;
  end
endmodule
module mod_nonblocking(input clk, input [7:0] d, output reg [7:0] q);
  always_ff @(posedge clk) begin
    q <= d;
  end
endmodule
module mod_sel_var(input [3:0] a, input [1:0] idx, output out);
  assign out = a[idx];
endmodule
module mod_sel_const(input [3:0] a, output out);
  assign out = a[2];
endmodule
module mod_sel_const_oob(input [5:0] a, input [1:0] i, output out);
  assign out = a[5] | a[i];
endmodule
module mod_array(input [1:0] idx, output [7:0] out);
  reg [7:0] arr [0:3];
  assign out = arr[idx];
endmodule
module mod_array_mod(input [15:0] addr, output [7:0] out);
  reg [7:0] arr [0:3];
  assign out = arr[addr % 4];
endmodule
module mod_xconst(input [4:0] in, output [4:0] out);
  assign out = in & 5'bx1_x;
endmodule
module mod_eqcase(input [3:0] a, input [3:0] b, output eq1, output eq2, output eq3, output eq4);
  assign eq1 = (a == b);
  assign eq2 = (a != b);
  assign eq3 = (a === b);
  assign eq4 = (a !== b);
endmodule
module mod_conditional(input a, input b, input c, output y);
  assign y = a ? b : c;
endmodule
module mod_case(input [1:0] sel, output reg q);
  always_comb begin
    case (sel)
      2'b00: q = 1'b0;
      2'b01: q = 1'b1;
      default: q = 1'bx;
    endcase
  end
endmodule
module mod_struct(input [3:0] a, input [1:0] b, output out);
  typedef struct packed { logic [3:0] f; } st_t;
  st_t s;
  always_comb begin
    s.f = a;
  end
  assign out = s.f[b];
endmodule
