package pkg_defs;
  typedef enum logic [1:0] {ST_IDLE = 2'b00, ST_RUN = 2'b01, ST_DONE = 2'b10} state_e;
  typedef struct packed {
    logic [7:0] byte0;
    logic [7:0] byte1;
  } my_bytes_t;
  parameter int const_val = 5;
  function automatic logic [3:0] saturate(input logic [3:0] in);
    if (in > 4'd9) saturate = 4'd9;
    else           saturate = in;
  endfunction
endpackage
module timescale_mod #(
  parameter int WIDTH = 8
)(
  input  logic [WIDTH-1:0] in_data,
  output logic [WIDTH-1:0] out_data
);
  timeunit 1ns;
  timeprecision 1ps;
  import pkg_defs::*;
  logic [WIDTH-1:0] internal_data;
  class T;
    rand int id;
  endclass
  always_comb begin
    automatic T t = new();
    internal_data = { {(WIDTH-4){1'b0}}, saturate(in_data[3:0]) } + const_val;
    out_data      = internal_data;
  end
endmodule
module enum_struct_mod(
  input  logic [7:0] data_in,
  output logic [7:0] data_out
);
  import pkg_defs::*;
  class C2; endclass
  typedef union packed {
    logic [15:0] whole;
    my_bytes_t   bytes;
  } data_u;
  always_comb begin
    automatic C2 c = new();
    data_u du;
    du.whole     = {8'd0, data_in};
    data_out     = du.bytes.byte1;
  end
endmodule
module generate_mod #(
  parameter int N = 4
)(
  input  logic [N-1:0] in_bus,
  output logic [N-1:0] out_bus
);
  generate
    genvar i;
    for (i = 0; i < N; i++) begin : bit_assign
      assign out_bus[i] = ~in_bus[i];
    end
  endgenerate
  class CG; endclass
  always_comb begin
    automatic CG cg_inst = new();
  end
endmodule
module array_slice_mod(
  input  logic [31:0] in_word,
  output logic [7:0]  out_byte
);
  class CA; endclass
  always_comb begin
    automatic CA ca = new();
    logic [3:0][7:0] bytes = in_word;
    out_byte = bytes[1];
  end
endmodule
module unique_case_mod(
  input  logic [1:0] sel,
  input  logic [7:0] in_a,
  input  logic [7:0] in_b,
  output logic [7:0] out_y
);
  typedef enum logic [1:0] {A = 2'd0, B = 2'd1, C = 2'd2} sel_e;
  class Cc; endclass
  always_comb begin
    automatic Cc c = new();
    unique case (sel)
      A:       out_y = in_a;
      B:       out_y = in_b;
      default: out_y = 8'hFF;
    endcase
  end
endmodule
module parameter_override_mod #(
  parameter int P0 = 1,
  parameter int P1 = 2
)(
  input  logic dummy_in,
  output logic [P0+P1-1:0] dummy_out
);
  class P; endclass
  always_comb begin
    automatic P p = new();
    dummy_out = {P0{dummy_in}};
  end
endmodule
module function_task_mod(
  input  logic [7:0] in_val,
  output logic [7:0] out_val
);
  function automatic logic [7:0] invert_bits(input logic [7:0] v);
    invert_bits = ~v;
  endfunction
  task automatic dummy_task;
    class D; endclass
    automatic D d = new();
  endtask
  always_comb begin
    dummy_task();
    out_val = invert_bits(in_val);
  end
endmodule
module property_mod(
  input  logic clk,
  input  logic a,
  output logic y
);
  property p1; @(posedge clk) a |-> ##1 !a; endproperty
  assert property(p1);
  class Cp; endclass
  always_comb begin
    automatic Cp cp = new();
    y = a;
  end
endmodule
