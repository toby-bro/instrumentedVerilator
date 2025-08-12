package types_pkg;
  typedef struct packed {
    logic [3:0] nibble0;
    logic [3:0] nibble1;
  } byte_split_t;
  typedef union packed {
    byte_split_t parts;
    logic [7:0]  whole;
  } byte_union_t;
endpackage
interface wide_bus_if #(parameter WIDTH = 32) ();
  logic [WIDTH-1:0] data;
  modport dut (input  data);
  modport tb  (output data);
endinterface
module bitwise_ops #(parameter WIDTH = 8)
  (input  logic [WIDTH-1:0] a,
   input  logic [WIDTH-1:0] b,
   output logic [WIDTH-1:0] and_o,
   output logic [WIDTH-1:0] or_o,
   output logic [WIDTH-1:0] xor_o);
  always_comb begin
    and_o = a & b;
    or_o  = a | b;
    xor_o = a ^ b;
  end
endmodule
module param_adder #(parameter WIDTH = 16)
  (input  logic                 clk,
   input  logic [WIDTH-1:0]     a,
   input  logic [WIDTH-1:0]     b,
   output logic [WIDTH:0]       sum);
  always_ff @(posedge clk) begin
    sum <= a + b;
  end
endmodule
module interface_user #(parameter WIDTH = 32)
  (input  logic [WIDTH-1:0] din,
   input  logic             enable,
   output logic             valid,
   output logic [WIDTH-1:0] dout);
  wide_bus_if #(.WIDTH(WIDTH)) bus_i();
  assign bus_i.data = din;
  assign valid      = enable & (bus_i.data != '0);
  assign dout       = bus_i.data;
endmodule
module state_machine
  (input  logic clk,
   input  logic rst_n,
   input  logic start,
   output logic busy,
   output logic done);
  typedef enum logic [1:0] {
    IDLE, PROCESS, FINISH
  } state_t;
  state_t state, next;
  always_comb begin
    next = state;
    case (state)
      IDLE:    if (start) next = PROCESS;
      PROCESS: next = FINISH;
      FINISH:  next = IDLE;
      default: next = IDLE;
    endcase
  end
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
      state <= IDLE;
    else
      state <= next;
  end
  assign busy = (state == PROCESS);
  assign done = (state == FINISH);
  property p_no_stuck;
    @(posedge clk) disable iff(!rst_n)
      state == FINISH |=> state == IDLE;
  endproperty
  assert property (p_no_stuck);
endmodule
module struct_packer
  (input  types_pkg::byte_union_t in_byte,
   output logic [7:0]             swapped);
  always_comb begin
    swapped = {in_byte.parts.nibble1, in_byte.parts.nibble0};
  end
endmodule
module gen_counter #(parameter DEPTH = 4)
  (input  logic               clk,
   output logic [DEPTH-1:0]   tc);
  logic [DEPTH-1:0] counters;
  genvar i;
  generate
    for (i = 0; i < DEPTH; i++) begin : gen_block
      always_ff @(posedge clk) begin
        counters[i] <= counters[i] + 1;
      end
    end
  endgenerate
  assign tc = counters;
endmodule
module class_demo
  (input  logic       clk,
   input  logic [31:0] in_value,
   output logic [31:0] out_sum);
  class accumulator_c;
    int acc;
    function new(); acc = 0; endfunction
    function void add(int v); acc += v; endfunction
    function int get(); return acc; endfunction
  endclass
  accumulator_c accum;
  always_ff @(posedge clk) begin
    if (accum == null)
      accum = new();
    accum.add(in_value);
    out_sum <= accum.get();
  end
endmodule
