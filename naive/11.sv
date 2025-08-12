module logic_ops
  #(parameter int WIDTH = 8)
  (
    input  logic [WIDTH-1:0] in_a,
    input  logic [WIDTH-1:0] in_b,
    output logic [WIDTH-1:0] out_and,
    output logic [WIDTH-1:0] out_or,
    output logic [WIDTH-1:0] out_xor
  );
  always_comb begin
    out_and = in_a & in_b;
    out_or  = in_a | in_b;
    out_xor = in_a ^ in_b;
  end
endmodule
module fsm_example
  (
    input  logic clk,
    input  logic rst_n,
    input  logic start,
    output logic busy
  );
  typedef enum logic [1:0] { IDLE, RUN, DONE } state_t;
  state_t state;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      state <= IDLE;
    end else begin
      unique case (state)
        IDLE: if (start) state <= RUN;
        RUN : state <= DONE;
        DONE: state <= IDLE;
      endcase
    end
  end
  assign busy = (state == RUN);
endmodule
module param_counter
  #(parameter int WIDTH = 4)
  (
    input  logic clk,
    input  logic rst_n,
    output logic [WIDTH-1:0] count
  );
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
      count <= '0;
    else
      count <= count + 1'b1;
  end
endmodule
module class_arith
  #(parameter int WIDTH = 8)
  (
    input  logic [WIDTH-1:0] a,
    input  logic [WIDTH-1:0] b,
    output logic [WIDTH-1:0] sum,
    output logic [WIDTH-1:0] diff
  );
  class calc;
    function automatic logic [WIDTH-1:0] add(input logic [WIDTH-1:0] x, y);
      add = x + y;
    endfunction
    function automatic logic [WIDTH-1:0] sub(input logic [WIDTH-1:0] x, y);
      sub = x - y;
    endfunction
  endclass
  always_comb begin
    calc c = new();
    sum  = c.add(a, b);
    diff = c.sub(a, b);
  end
endmodule
module struct_union_demo
  (
    input  logic [31:0] in_word,
    output logic [7:0]  out_byte0,
    output logic [7:0]  out_byte1,
    output logic [7:0]  out_byte2,
    output logic [7:0]  out_byte3
  );
  typedef struct packed {
    logic [7:0] b0;
    logic [7:0] b1;
    logic [7:0] b2;
    logic [7:0] b3;
  } word_t;
  always_comb begin
    word_t w = word_t'(in_word);
    out_byte0 = w.b0;
    out_byte1 = w.b1;
    out_byte2 = w.b2;
    out_byte3 = w.b3;
  end
endmodule
module array_demo
  #(parameter int DEPTH = 4)
  (
    input  logic [7:0] in_data [DEPTH-1:0],
    output logic [7:0] out_sum
  );
  integer idx;
  always_comb begin
    out_sum = '0;
    for (idx = 0; idx < DEPTH; idx++) begin
      out_sum += in_data[idx];
    end
  end
endmodule
