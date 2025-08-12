interface IBus(input logic clk);
  logic [7:0] data;
  modport master(input data);
endinterface
typedef struct packed { logic [3:0] a; logic [3:0] b; } struct_t;
typedef union packed { logic [7:0] u; struct_t s; } union_t;
typedef enum logic [1:0] { IDLE = 2'b00, BUSY = 2'b01, DONE = 2'b10 } state_t;
module mod_arith #(parameter WIDTH = 8) (
  input  logic [WIDTH-1:0] a,
  input  logic [WIDTH-1:0] b,
  output logic [WIDTH-1:0] sum
);
  always_comb sum = a + b;
endmodule
module mod_bitwise (
  input  logic [3:0] a,
  input  logic [3:0] b,
  output logic [3:0] and_o,
  output logic [3:0] or_o,
  output logic [3:0] xor_o
);
  assign and_o = a & b;
  assign or_o  = a | b;
  assign xor_o = a ^ b;
endmodule
module mod_shift (
  input  logic [7:0] data,
  input  logic [2:0] sh,
  output logic [7:0] lshift,
  output logic [7:0] rshift
);
  always_comb begin
    lshift = data << sh;
    rshift = data >> sh;
  end
endmodule
module mod_reduction (
  input  logic [7:0] d,
  output logic and_r,
  output logic or_r,
  output logic xor_r
);
  assign and_r = &d;
  assign or_r  = |d;
  assign xor_r = ^d;
endmodule
module mod_concat_slice (
  input  logic [7:0] d0,
  input  logic [7:0] d1,
  output logic [7:0] result
);
  assign result = { d0[3:0], d1[3:0] };
endmodule
module mod_struct_union (
  input  struct_t in,
  input  union_t uin,
  output struct_t out,
  output logic [7:0] uout
);
  assign out  = in;
  assign uout = uin.u;
endmodule
module mod_enum (
  input  logic    go,
  input  state_t  cur,
  output state_t  next
);
  always_comb begin
    case (cur)
      IDLE: next = go ? BUSY : IDLE;
      BUSY: next = DONE;
      DONE: next = IDLE;
      default: next = IDLE;
    endcase
  end
endmodule
module mod_genif #(parameter WIDTH = 8) (
  input  logic [WIDTH-1:0] in,
  output logic [WIDTH-1:0] out
);
  generate
    if (WIDTH > 4) begin
      assign out = in + {{(WIDTH-1){1'b0}},1'b1};
    end else begin
      assign out = in - {{(WIDTH-1){1'b0}},1'b1};
    end
  endgenerate
endmodule
module mod_genfor #(parameter N = 4) (
  input  logic [N-1:0] a,
  output logic [N-1:0] b
);
  genvar i;
  generate
    for (i = 0; i < N; i = i + 1) begin
      assign b[i] = a[i] ^ a[N-1-i];
    end
  endgenerate
endmodule
module mod_gencase #(parameter logic [1:0] SEL = 2'b00) (
  input  logic [7:0] d0,
  input  logic [7:0] d1,
  input  logic [7:0] d2,
  input  logic [7:0] d3,
  output logic [7:0] out
);
  generate
    case (SEL)
      2'b00: assign out = d0;
      2'b01: assign out = d1;
      2'b10: assign out = d2;
      default: assign out = d3;
    endcase
  endgenerate
endmodule
module mod_func (
  input  logic [7:0] x,
  input  logic [7:0] y,
  output logic [7:0] z
);
  function logic [7:0] add2(input logic [7:0] a, input logic [7:0] b);
    add2 = a + b;
  endfunction
  always_comb z = add2(x, y);
endmodule
module mod_class (
  input  logic [3:0] a,
  input  logic [3:0] b,
  output logic [7:0] y
);
  class C;
    function logic [7:0] f(input logic [3:0] x, input logic [3:0] y_in);
      f = x * y_in;
    endfunction
  endclass
  always_comb begin
    static C inst = new();
    y = inst.f(a, b);
  end
endmodule
module mod_iface (
  input  logic clk,
  output logic [7:0] o
);
  IBus ib(.clk(clk));
  always_comb o = ib.data;
endmodule
