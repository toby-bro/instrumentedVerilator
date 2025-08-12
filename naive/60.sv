module param_mod #(
  parameter int WIDTH = 8,
  parameter bit [WIDTH-1:0] INIT_VAL = '0
) (
  input  logic [WIDTH-1:0] in,
  output logic [WIDTH-1:0] out
);
  localparam int DOUBLE = WIDTH * 2;
  logic [DOUBLE-1:0] buffer;
  genvar i;
  generate
    for (i = 0; i < WIDTH; i = i + 1) begin : bit_xor
      assign buffer[i] = in[i] ^ INIT_VAL[i];
    end
  endgenerate
  assign out = buffer[WIDTH +: WIDTH];
endmodule
module enum_mod (
  input  logic        clk,
  output logic [1:0]  state_out
);
  typedef enum logic [1:0] {IDLE=2'b00, RUN=2'b01, DONE=2'b10} state_t;
  state_t state, next_state;
  always_ff @(posedge clk) begin
    state <= next_state;
  end
  always_comb begin
    case (state)
      IDLE:   next_state = RUN;
      RUN:    next_state = DONE;
      DONE:   next_state = IDLE;
      default: next_state = IDLE;
    endcase
  end
  assign state_out = state;
endmodule
module struct_union_mod (
  input  logic [3:0] a,
  input  logic [3:0] b,
  output logic [3:0] sum,
  output logic [3:0] diff
);
  typedef struct packed {
    logic [3:0] high;
    logic [3:0] low;
  } half_t;
  typedef union packed {
    logic [7:0] full;
    half_t       parts;
  } data_u;
  function logic [3:0] add4(input logic [3:0] x, input logic [3:0] y);
    add4 = x + y;
  endfunction
  function logic [3:0] sub4(input logic [3:0] x, input logic [3:0] y);
    sub4 = x - y;
  endfunction
  data_u du;
  always_comb begin
    du.parts.high = a;
    du.parts.low  = b;
    sum  = add4(du.parts.high, du.parts.low);
    diff = sub4(du.parts.high, du.parts.low);
  end
endmodule
module class_mod (
  input  logic [7:0] in_value,
  output logic [7:0] out_value
);
  class calc_c;
    rand logic [7:0] val;
    function logic [7:0] incr(input logic [7:0] x);
      return x + 1;
    endfunction
    function void compute(input logic [7:0] in, output logic [7:0] out);
      out = incr(in);
    endfunction
  endclass
  calc_c inst;
  always_comb begin
    inst = new;
    inst.compute(in_value, out_value);
  end
endmodule
module generate_mod (
  input  logic en,
  output logic done
);
  localparam int N = 4;
  logic [N-1:0] flags;
  genvar j;
  generate
    for (j = 0; j < N; j = j + 1) begin : gen_flags
      assign flags[j] = en & (j[0] ? 1'b1 : 1'b0);
    end
  endgenerate
  assign done = &flags;
endmodule
module fsm_mod (
  input  logic clk,
  input  logic reset,
  output logic flag
);
  typedef enum logic [1:0] {S0, S1, S2, S3} st_t;
  st_t curr, nxt;
  function st_t next_state(input st_t s, input bit r);
    case (s)
      S0: next_state = r ? S1 : S0;
      S1: next_state = r ? S2 : S0;
      S2: next_state = r ? S3 : S0;
      S3: next_state = S0;
      default: next_state = S0;
    endcase
  endfunction
  always_ff @(posedge clk or posedge reset) begin
    if (reset) curr <= S0;
    else       curr <= nxt;
  end
  always_comb begin
    nxt = next_state(curr, flag);
  end
  assign flag = (curr == S3);
endmodule
