module ComplexDeclarations (
  input logic [7:0] in_data,
  input int         in_addr,
  output logic [15:0] out_result
);
  logic                   logic_var;
  bit                     bit_var;
  byte                    byte_var = 8'hAA;
  int                     int_var;
  longint                 longint_var;
  shortint                shortint_var;
  real                    real_var;
  double                  double_var;
  supply0 s0_net;
  supply1 s1_net;
  genvar i;
  (* verilog_attr = "some_value" *) logic attr_var;
  automatic int auto_var;
  static  int static_var;
  typedef struct packed {
    logic [3:0] field1;
    logic       field2;
  } my_struct_t;
  my_struct_t struct_var;
  typedef logic [7:0] my_byte_t;
  my_byte_t byte_alias;
  logic [31:0] packed_array_1D;
  logic [7:0][15:0] packed_array_2D; 
  logic unpacked_array_1D [0:63];
  logic unpacked_array_2D [7:0][15:0]; 
  logic dynamic_array [];
  logic queue_var [$];
  logic [7:0] byte_queue [$];
  logic assoc_int_array [int];
  logic assoc_string_array [string];
  logic assoc_wildcard_array [*];
  parameter string PARAM_STRING_1 = "Hello, World!";
  parameter string PARAM_STRING_2 = "Escaped chars: \\\" \\n \\t";
  output logic non_ansi_out_signal;
  input  logic non_ansi_in_signal;
  always_comb begin
    logic_var = in_data[0];
    bit_var = in_data[1];
    int_var = in_addr;
    longint_var = 64'hFFFF_FFFF_FFFF_FFFF;
    shortint_var = 16'hABCD;
    real_var = 3.14159;
    double_var = 2.718281828459045;
    packed_array_1D = {in_data, in_data, in_data, in_data};
    unpacked_array_1D[in_addr % 64] = in_data[2];
    assoc_int_array[in_addr] = in_data[3];
    assoc_string_array[PARAM_STRING_1] = in_data[4];
    assoc_wildcard_array[in_addr] = in_data[5]; 
    struct_var.field1 = in_data[3:0];
    struct_var.field2 = in_data[4];
    byte_alias = in_data;
    if (in_data[0]) begin
      out_result = int_var + byte_var;
    end else begin
      out_result = packed_array_1D[15:0];
    end
    non_ansi_out_signal = logic_var;
  end
  generate
    for (i=0; i<4; i=i+1) begin : gen_block
      logic genvar_local_sig;
      assign genvar_local_sig = in_data[i];
    end
  endgenerate
endmodule
module ProceduralAndSelections (
  input logic [63:0]  val_in,
  input logic [7:0]   select_idx,
  input int           func_arg_a,
  input int           func_arg_b,
  output logic [31:0] result_out
);
  logic [63:0] internal_reg;
  logic [7:0]  byte_array [0:7]; 
  logic        flag;
  function automatic int my_adder(int a, int b, int c);
    return a + b + c;
  endfunction
  task automatic my_multiplier(input int x, input int y, output int z);
    z = x * y;
  endtask
  always_comb begin : comb_block_example
    int temp_val;
    internal_reg = val_in;
    result_out = internal_reg[31:0]; 
    flag = internal_reg[select_idx];  
    result_out = internal_reg[select_idx + 8 +: 32]; 
    result_out = internal_reg[select_idx + 40 -: 32]; 
    byte_array[0] = internal_reg[7:0];
    byte_array[1] = internal_reg[15:8];
    result_out[7:0] = byte_array[select_idx % 8][3:0]; 
    temp_val = my_adder(func_arg_a, func_arg_b, 10);
    my_multiplier(temp_val, 2, result_out[31:0]); 
    if (select_idx == 8'h00) begin
      result_out = internal_reg[63:32];
    end else if (select_idx == 8'h01) begin
      result_out = internal_reg[31:0];
    end else begin
      result_out = {8'hFF, internal_reg[23:0]}; 
    end
    case (select_idx[1:0])
      2'b00: result_out = 32'hAAAA_AAAA;
      2'b01: result_out = 32'hBBBB_BBBB;
      2'b10: result_out = 32'hCCCC_CCCC;
      default: result_out = 32'hDDDD_DDDD;
    endcase
  end
  always_ff @(posedge val_in[0] or posedge val_in[1]) begin : ff_block_example
    internal_reg <= val_in;
  end
endmodule
module BasicIOModule (
    input logic basic_in,
    output logic basic_out
);
  logic temp_signal;
  always_comb begin
    temp_signal = basic_in;
    basic_out = temp_signal;
  end
endmodule
