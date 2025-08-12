`default_nettype none
package util_pkg;
  typedef struct packed {
    logic [3:0] a;
    logic [3:0] b;
  } add_pair_t;
  typedef enum logic [1:0] {OP_ADD = 2'd0, OP_XOR = 2'd1, OP_SUB = 2'd2} op_t;
  function automatic logic [4:0] arithmetic(input add_pair_t p, input op_t op);
    case (op)
      OP_ADD : arithmetic = p.a + p.b;
      OP_XOR : arithmetic = p.a ^ p.b;
      OP_SUB : arithmetic = p.a - p.b;
      default: arithmetic = '0;
    endcase
  endfunction
endpackage
interface simple_if #(parameter WIDTH = 8)(input logic clk);
  logic [WIDTH-1:0] data_in;
  logic [WIDTH-1:0] data_out;
  modport proc(
    input  clk,
    input  data_in,
    output data_out
  );
endinterface
module arithmetic_unit #(parameter WIDTH = 8)(
  input  logic [WIDTH-1:0] a,
  input  logic [WIDTH-1:0] b,
  input  logic             sel,
  output logic [WIDTH-1:0] y
);
  always_comb begin
    if (sel)
      y = a + b;
    else
      y = a - b;
  end
endmodule
module struct_demo(
  input  logic [3:0] in_a,
  input  logic [3:0] in_b,
  input  logic [1:0] op,
  output logic [4:0] result
);
  import util_pkg::*;
  add_pair_t pair_s;
  always_comb begin
    pair_s = '{a: in_a, b: in_b};
    result = arithmetic(pair_s, op_t'(op));
  end
endmodule
module class_demo(
  input  logic       clk,
  input  logic       rst_n,
  input  logic [7:0] data_in,
  output logic [7:0] acc_out
);
  class accumulator;
    rand logic [7:0] sum;
    function void add(input logic [7:0] val);
      sum = sum + val;
    endfunction
  endclass
  accumulator acc_h;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      acc_out <= '0;
      acc_h   = new();
      acc_h.sum = '0;
    end else begin
      if (acc_h == null) acc_h = new();
      acc_h.add(data_in);
      acc_out <= acc_h.sum;
    end
  end
endmodule
module generate_demo #(parameter WIDTH = 8, parameter DEPTH = 4)(
  input  logic [DEPTH*WIDTH-1:0] vec_in,
  output logic [WIDTH-1:0]       vec_sum
);
  logic [WIDTH-1:0] pieces [DEPTH];
  genvar i;
  generate
    for (i = 0; i < DEPTH; i = i + 1) begin : SLICE_ASSIGN
      assign pieces[i] = vec_in[i*WIDTH +: WIDTH];
    end
  endgenerate
  always_comb begin
    vec_sum = '0;
    for (int j = 0; j < DEPTH; j++) begin
      vec_sum = vec_sum + pieces[j];
    end
  end
endmodule
module enum_fsm(
  input  logic clk,
  input  logic rst_n,
  input  logic in_sig,
  output logic [1:0] state_o
);
  typedef enum logic [1:0] {S0, S1, S2} state_t;
  state_t state, next_state;
  always_comb begin
    unique case (state)
      S0     : next_state = in_sig ? S1 : S0;
      S1     : next_state = in_sig ? S2 : S1;
      S2     : next_state = in_sig ? S0 : S2;
      default: next_state = S0;
    endcase
  end
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
      state <= S0;
    else
      state <= next_state;
  end
  assign state_o = state;
endmodule
module union_demo(
  input  logic [7:0] in_byte,
  input  logic       sel_nibble,
  output logic [3:0] out_nibble
);
  typedef union packed {
    logic [7:0] full;
    struct packed {
      logic [3:0] lo;
      logic [3:0] hi;
    } nibbles;
  } byte_u;
  byte_u data_u;
  always_comb begin
    data_u.full = in_byte;
    out_nibble  = sel_nibble ? data_u.nibbles.hi : data_u.nibbles.lo;
  end
endmodule
module assert_demo(
  input logic       clk,
  input logic       rst_n,
  input logic [3:0] x,
  output logic [3:0] y
);
  assign y = x + 4'd1;
  property no_overflow;
    @(posedge clk) disable iff (!rst_n) x < 4'hF |-> y != 4'h0;
  endproperty
  assert property(no_overflow);
endmodule
`default_nettype wire
