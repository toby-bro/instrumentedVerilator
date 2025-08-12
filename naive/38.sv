package utils_pkg;
  typedef enum logic [1:0] {IDLE = 2'b00, RUN = 2'b01, STOP = 2'b10} state_e;
  typedef struct packed {
    logic [7:0] data;
    logic       valid;
  } packet_s;
endpackage
module and_gate (
  input  logic a,
  input  logic b,
  output logic y
);
  assign y = a & b;
endmodule
module aggregator #(
  parameter int N     = 4,
  parameter int WIDTH = 8
) (
  input  logic [WIDTH-1:0] in_bus [N],
  output logic [WIDTH-1:0] sum
);
  integer i;
  always_comb begin
    sum = '0;
    for (i = 0; i < N; i++) begin
      sum += in_bus[i];
    end
  end
endmodule
module fsm (
  input  logic          clk,
  input  logic          rst_n,
  input  logic          start,
  output logic          done
);
  import utils_pkg::*;
  state_e state, next;
  always_comb begin
    next = state;
    done = 1'b0;
    unique case (state)
      IDLE:  if (start) next = RUN;
      RUN:   begin
               next = STOP;
               done = 1'b1;
             end
      STOP:  if (!start) next = IDLE;
      default: next = IDLE;
    endcase
  end
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
      state <= IDLE;
    else
      state <= next;
  end
endmodule
class adder_c;
  function automatic int add (input int a, b);
    return a + b;
  endfunction
endclass
module class_user (
  input  logic [31:0] a,
  input  logic [31:0] b,
  input  logic        clk,
  output logic [31:0] result
);
  adder_c handle;
  always_ff @(posedge clk) begin
    handle = new();
    result <= handle.add(a, b);
  end
endmodule
module packet_handler (
  input  logic [7:0]  data_in,
  input  logic        valid_in,
  output logic [15:0] data_out
);
  typedef struct packed {
    logic [7:0] data;
    logic       valid;
    logic [6:0] rsvd;
  } packet16_s;
  typedef union packed {
    packet16_s        pkt;
    logic     [15:0]  raw;
  } u_packet_t;
  u_packet_t u_data;
  always_comb begin
    u_data.pkt.data  = data_in;
    u_data.pkt.valid = valid_in;
    u_data.pkt.rsvd  = 7'd0;
    data_out         = u_data.raw;
  end
endmodule
module parity_gen #(
  parameter int WIDTH = 16
) (
  input  logic [WIDTH-1:0] din,
  output logic             parity
);
  integer i;
  always_comb begin
    parity = 1'b0;
    for (i = 0; i < WIDTH; i++) begin
      parity ^= din[i];
    end
  end
endmodule
module functions_demo (
  input  logic [7:0] v_in,
  output logic [3:0] popcnt
);
  function automatic [3:0] count_ones (input logic [7:0] v);
    integer idx;
    begin
      count_ones = 4'd0;
      for (idx = 0; idx < 8; idx++) begin
        count_ones += v[idx];
      end
    end
  endfunction
  assign popcnt = count_ones(v_in);
endmodule
module bit_manip (
  input  logic [31:0] in_val,
  output logic [31:0] out_val
);
  logic [7:0] bytes [4];
  integer i;
  always_comb begin
    for (i = 0; i < 4; i++) begin
      bytes[i] = in_val[i*8 +: 8];
    end
    out_val = {bytes[0], bytes[1], bytes[2], bytes[3]};
  end
endmodule
module assert_demo (
  input  logic clk,
  input  logic a,
  input  logic b,
  output logic y
);
  assign y = a | b;
  property p_or;
    @(posedge clk) y |-> (a || b);
  endproperty
  assert property (p_or);
endmodule
