package common_pkg;
  typedef enum logic [1:0] {IDLE, RUN, DONE} state_e;
  typedef struct packed {
    logic [7:0]  header;
    logic [23:0] payload;
  } packet_s;
  class math_c;
    function automatic logic [31:0] add(input logic [31:0] x, y);
      add = x + y;
    endfunction
    function automatic logic [31:0] sub(input logic [31:0] x, y);
      sub = x - y;
    endfunction
  endclass
endpackage
module arithmetic_mod (
  input  logic [31:0] in_a,
  input  logic [31:0] in_b,
  output logic [31:0] out_sum,
  output logic [31:0] out_diff
);
  import common_pkg::*;
  always_comb begin
    math_c m = new;
    out_sum  = m.add(in_a, in_b);
    out_diff = m.sub(in_a, in_b);
  end
endmodule
module state_machine_mod (
  input  logic clk,
  input  logic rst_n,
  input  logic start,
  output logic done
);
  import common_pkg::*;
  state_e state, next_state;
  always_comb begin
    next_state = state;
    case (state)
      IDLE:  if (start)      next_state = RUN;
      RUN:                   next_state = DONE;
      DONE: if (!start)      next_state = IDLE;
      default:               next_state = IDLE;
    endcase
  end
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
      state <= IDLE;
    else
      state <= next_state;
  end
  assign done = (state == DONE);
endmodule
module struct_union_mod (
  input  logic [31:0] raw_data,
  output common_pkg::packet_s pkt_out
);
  import common_pkg::*;
  union packed {
    packet_s       pkt;
    logic [31:0]   word;
  } converter_u;
  always_comb begin
    converter_u.word = raw_data;
    pkt_out         = converter_u.pkt;
  end
endmodule
module generate_mod #(
  parameter int WIDTH     = 8,
  parameter int REPLICATE = 4
) (
  input  logic [WIDTH-1:0]                 data_in,
  output logic [WIDTH*REPLICATE-1:0]       data_out
);
  genvar i;
  generate
    for (i = 0; i < REPLICATE; i++) begin : gen_blk
      assign data_out[(i+1)*WIDTH-1 -: WIDTH] = data_in;
    end
  endgenerate
endmodule
module array_mod #(
  parameter int DEPTH = 16
)(
  input  logic [7:0]                      write_data,
  input  logic [$clog2(DEPTH)-1:0]        write_addr,
  input  logic                            we,
  input  logic [$clog2(DEPTH)-1:0]        read_addr,
  output logic [7:0]                      read_data,
  input  logic                            clk
);
  logic [7:0] mem [0:DEPTH-1];
  always_ff @(posedge clk) begin
    if (we)
      mem[write_addr] <= write_data;
  end
  assign read_data = mem[read_addr];
endmodule
module function_task_mod (
  input  logic [15:0] in_val,
  output logic [15:0] out_val
);
  function automatic logic [15:0] reverse_bits(input logic [15:0] din);
    integer j;
    for (j = 0; j < 16; j++) begin
      reverse_bits[j] = din[15-j];
    end
  endfunction
  always_comb begin
    out_val = reverse_bits(in_val);
  end
endmodule
module logic_reduction_mod (
  input  logic [31:0] in_vector,
  output logic        parity
);
  always_comb begin
    parity = ^in_vector;
  end
endmodule
