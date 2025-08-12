class simple_class;
  bit a;
  function new(bit a_in);
    a = a_in;
  endfunction
  function bit get();
    return a;
  endfunction
endclass
typedef struct packed {
  logic [3:0] x;
  logic [3:0] y;
} s_t;
typedef union {
  logic [7:0] u_byte;
  logic [3:0] hi;
  logic [3:0] lo;
} u_t;
typedef enum logic [1:0] {
  IDLE = 2'b00,
  BUSY = 2'b01,
  DONE = 2'b10
} st_t;
module mod_assign (
  input  logic [3:0] in,
  output logic [3:0] out
);
  assign out = in ^ 4'hA;
endmodule
module mod_ff (
  input  logic       clk,
  input  logic       rst,
  input  logic [7:0] d,
  output logic [7:0] q
);
  always_ff @(posedge clk or posedge rst) begin
    if (rst)
      q <= '0;
    else
      q <= d;
  end
endmodule
module mod_comb_case (
  input  logic [1:0] sel,
  input  logic [3:0] a,
  input  logic [3:0] b,
  output logic [3:0] y
);
  always_comb begin
    case (sel)
      2'b00: y = a;
      2'b01: y = b;
      default: y = '0;
    endcase
  end
endmodule
module mod_param #(
  parameter int WIDTH = 8
) (
  input  logic [WIDTH-1:0] in,
  output logic [WIDTH-1:0] out
);
  localparam int HALF = WIDTH / 2;
  genvar i;
  generate
    for (i = 0; i < WIDTH; i = i + 1) begin : gen_loop
      assign out[i] = in[WIDTH-1-i];
    end
  endgenerate
endmodule
module mod_struct (
  input  s_t s,
  output logic [3:0] sum
);
  assign sum = s.x + s.y;
endmodule
module mod_union_enum (
  input  u_t u,
  input  st_t st,
  output logic [7:0] out
);
  always_comb begin
    case (st)
      IDLE: out = u.u_byte;
      BUSY: out = {u.hi, u.lo};
      default: out = '0;
    endcase
  end
endmodule
module mod_function (
  input  logic [7:0] x,
  output logic [7:0] y
);
  function logic [7:0] thr(input logic [7:0] v);
    thr = (v > 8'h80) ? 8'hFF : 8'h00;
  endfunction
  assign y = thr(x);
endmodule
module mod_class_inst (
  input  logic       flag,
  input  logic [3:0] val,
  output logic [3:0] out
);
  always_comb begin
    simple_class sc = new(val[0]);
    out = sc.get() ? val : 4'h0;
  end
endmodule
module mod_array (
  input  logic [7:0] arr_in  [0:2],
  output logic [7:0] arr_out [0:2]
);
  genvar j;
  generate
    for (j = 0; j < 3; j = j + 1) begin : arr_loop
      assign arr_out[j] = arr_in[2-j];
    end
  endgenerate
endmodule
module mod_multidim (
  input  logic [3:0] mat_in  [0:3],
  output logic [3:0] mat_out [0:3]
);
  always_comb begin
    mat_out = mat_in;
  end
endmodule
