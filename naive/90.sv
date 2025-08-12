module mod_param #(parameter int WIDTH = 8) (
    input  logic [WIDTH-1:0] in,
    output logic [WIDTH-1:0] out
);
  localparam int HALF = WIDTH / 2;
  genvar i;
  generate
    for (i = 0; i < HALF; i++) begin
      assign out[i] = in[i] ^ in[WIDTH-1-i];
    end
    for (i = HALF; i < WIDTH; i++) begin
      assign out[i] = in[i] & in[WIDTH-1-i];
    end
  endgenerate
endmodule
module mod_types (
    input  logic [3:0] a,
    input  logic [3:0] b,
    output logic [3:0] sum
);
  typedef enum logic [1:0] { IDLE, BUSY, DONE, ERR } state_t;
  typedef struct packed { logic [3:0] x; logic [3:0] y; } pair_t;
  state_t state;
  pair_t p;
  always_comb begin
    p.x   = a;
    p.y   = b;
    sum   = p.x + p.y;
    state = (sum > 4'd9) ? ERR : DONE;
  end
endmodule
module mod_union (
    input  logic [7:0] u_in,
    output logic [2:0] nibble
);
  union {
    logic [7:0] byte_val;
    logic [3:0] lo;
    logic [3:0] hi;
  } u;
  always_comb begin
    u.byte_val = u_in;
    nibble     = (u.lo > u.hi) ? u.lo[2:0] : u.hi[2:0];
  end
endmodule
module mod_class_inst (
    input  logic       clk,
    output logic [7:0] data_out
);
  class MyCalc;
    function logic [7:0] add(input logic [7:0] a, b);
      return a + b;
    endfunction
    function logic [7:0] sub(input logic [7:0] a, b);
      return a - b;
    endfunction
  endclass
  always_ff @(posedge clk) begin
    static MyCalc calc = new();
    data_out    <= calc.add(8'd10, 8'd5);
  end
endmodule
module mod_forloop (
    input  logic [7:0] in_vec,
    output logic [7:0] out_vec
);
  integer i;
  always_comb begin
    for (i = 0; i < 8; i++) begin
      out_vec[i] = (^in_vec) ? in_vec[i] : ~in_vec[i];
    end
  end
endmodule
module mod_assert_check (
    input  logic a,
    input  logic b,
    output logic y
);
  always_comb begin
    y = a ^ b;
    assert (y == (a ^ b));
  end
endmodule
module mod_latch (
    input  logic en,
    input  logic d,
    output logic q
);
  always_latch begin
    if (en) q = d;
  end
endmodule
