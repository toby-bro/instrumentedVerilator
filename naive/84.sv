module class_demo(input  logic [7:0] a, b, output logic [7:0] y);
  class Adder;
    function logic [7:0] add(input logic [7:0] x, input logic [7:0] z);
      add = x + z;
    endfunction
  endclass
  always_comb begin
    static Adder ad = new();
    y = ad.add(a, b);
  end
endmodule
module enum_fsm(input  logic clk, reset, output logic [1:0] state_out);
  typedef enum logic [1:0] {IDLE = 2'b00, START = 2'b01, STOP = 2'b10} state_t;
  state_t state, next_state;
  always_comb begin
    case (state)
      IDLE : next_state = START;
      START: next_state = STOP;
      STOP : next_state = IDLE;
      default: next_state = IDLE;
    endcase
  end
  always_ff @(posedge clk or posedge reset) begin
    if (reset) state <= IDLE;
    else       state <= next_state;
  end
  assign state_out = state;
endmodule
module params_demo #(parameter WIDTH = 8) (input logic [WIDTH-1:0] in, output logic [WIDTH-1:0] out);
  localparam DOUBLE = WIDTH * 2;
  assign out = ~in;
endmodule
module struct_union_demo(input  logic [7:0] in, output logic signed [7:0] out);
  typedef struct packed { logic [3:0] hi; logic [3:0] lo; } nibble_t;
  typedef union packed { nibble_t n; logic [7:0] b; } u_t;
  u_t uu;
  always_comb begin
    uu.b = in;
  end
  assign out = uu.n.hi - uu.n.lo;
endmodule
module function_demo(input  logic [3:0] a, b, output logic [4:0] sum);
  function logic [4:0] addfunc(input logic [3:0] x, input logic [3:0] y);
    addfunc = x + y;
  endfunction
  always_comb sum = addfunc(a, b);
endmodule
module mem_array_demo(input  logic [1:0] addr, input logic [7:0] data_in, input logic we, output logic [7:0] data_out);
  logic [7:0] mem [0:3];
  always_ff @(posedge addr[0] or posedge we) begin
    if (we) mem[addr] <= data_in;
  end
  assign data_out = mem[addr];
endmodule
module gen_demo(input logic en, output logic [3:0] bits);
  genvar i;
  generate
    for (i = 0; i < 4; i = i + 1) begin
      assign bits[i] = en ? i[0] : 1'b0;
    end
  endgenerate
endmodule
module edge_detect_demo(input  logic clk, sig, output logic det_pos);
  logic prev;
  always_ff @(posedge clk) begin
    det_pos <= (~prev) & sig;
    prev     <= sig;
  end
endmodule
