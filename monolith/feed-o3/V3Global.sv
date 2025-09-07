package util_pkg;
  typedef enum logic [1:0] {ST_IDLE, ST_RUN, ST_DONE} state_e;
  typedef struct packed {
    logic [7:0] a;
    logic [7:0] b;
  } pair_t;
endpackage
interface bus_if #(parameter int WIDTH = 8) (input logic clk);
  logic [WIDTH-1:0] data;
  logic             valid;
  modport master (output data, output valid);
  modport slave  (input  data, input  valid);
endinterface
module m_dumpTreeEitherLevel (input logic in, output logic out);
  assign out = ~in;
endmodule
module m_dumpTreeJsonLevel (input logic a, output logic b);
  assign b = a;
endmodule
module m_dumpTreeLevel (input logic sig_in, output logic sig_out);
  assign sig_out = sig_in;
endmodule
module m_boot #(parameter WIDTH = 8)
  (input  logic [WIDTH-1:0] in,
   output logic [WIDTH-1:0] out);
  import util_pkg::*;
  pair_t p;
  always_comb begin
    p.a = in;
    p.b = ~in;
    out = p.a ^ p.b;
  end
endmodule
module m_shutdown #(parameter WIDTH = 8)
  (input  logic clk,
   input  logic [WIDTH-1:0] in,
   output logic [WIDTH-1:0] out);
  bus_if #(WIDTH) b_if (clk);
  always_ff @(posedge clk) begin
    b_if.data  <= in;
    b_if.valid <= 1'b1;
  end
  assign out = b_if.data;
endmodule
module m_checkTree (input logic [3:0] in0, output logic [7:0] out0);
  typedef struct packed {logic [3:0] low, high;} nibble_t;
  typedef union packed {nibble_t n; logic [7:0] byte_v;} byte_u;
  byte_u u;
  always_comb begin
    u.n.low  = in0;
    u.n.high = ~in0;
    out0     = u.byte_v;
  end
endmodule
module m_readFiles #(parameter BUS_WIDTH = 8, parameter DEPTH = 4)
  (input  logic [BUS_WIDTH*DEPTH-1:0] data_in_flat,
   output logic [BUS_WIDTH*DEPTH-1:0] data_out_flat);
  genvar i;
  generate
    for (i = 0; i < DEPTH; i++) begin : gen_block
      localparam int LO = i*BUS_WIDTH;
      localparam int HI = LO + BUS_WIDTH - 1;
      assign data_out_flat[HI:LO] = ~data_in_flat[HI:LO];
    end
  endgenerate
endmodule
module m_removeStd #(parameter SIZE = 4)
  (input  logic [SIZE-1:0] in,
   output logic [SIZE-1:0] out);
  localparam logic [SIZE-1:0] MASK = {SIZE{1'b1}};
  assign out = in & MASK;
endmodule
module m_debugFilename (input logic [31:0] in, output logic [31:0] out);
  function automatic [31:0] bit_reverse (input [31:0] x);
    integer i;
    for (i = 0; i < 32; i++) bit_reverse[i] = x[31 - i];
  endfunction
  assign out = bit_reverse(in);
endmodule
module m_digitsFilename (input logic [7:0] in, output logic [3:0] out);
  function automatic [3:0] popcount (input [7:0] x);
    integer j;
    popcount = 0;
    for (j = 0; j < 8; j++) popcount += x[j];
  endfunction
  assign out = popcount(in);
endmodule
module m_dumpCheckGlobalTree (input logic clk, input logic rst, output logic done);
  logic state;
  always_ff @(posedge clk) begin
    if (rst) state <= 1'b0;
    else     state <= 1'b1;
  end
  assign done = state;
endmodule
module m_idPtrMapDumpJson (
  input  logic [15:0] in0,
  input  logic [15:0] in1,
  output logic [15:0] out0,
  output logic [15:0] out1
);
  logic [15:0] mem [0:1];
  always_comb begin
    mem[0] = in0;
    mem[1] = in1;
    out0   = mem[1];
    out1   = mem[0];
  end
endmodule
module m_saveJsonPtrFieldName (input logic enable, output logic ack);
  assign ack = enable;
endmodule
module m_ptrNamesDumpJson (input logic [7:0] in, output logic [7:0] out);
  logic [7:0] arr [0:3];
  always_comb begin
    arr[0] = in;
    arr[1] = ~in;
    arr[2] = in ^ 8'hFF;
    arr[3] = in & 8'h0F;
    out    = arr[2];
  end
endmodule
module m_ptrToId (input logic [7:0] in, output logic [7:0] out);
  class bit_reverse_c;
    function automatic [7:0] reverse (input [7:0] x);
      int i;
      for (i = 0; i < 8; i++) reverse[i] = x[7 - i];
    endfunction
  endclass
  bit_reverse_c br;
  initial br = new();
  always_comb begin
    if (br == null) out = 8'h00;
    else            out = br.reverse(in);
  end
endmodule
module m_verilatedCppFiles (input logic [3:0] in, output logic [3:0] out);
  logic [3:0] temp [0:3];
  integer     idx;
  always_comb begin
    for (idx = 0; idx < 4; idx++) temp[idx] = in + idx[3:0];
    out = temp[3];
  end
endmodule
