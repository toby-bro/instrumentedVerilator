package my_package;
  typedef enum logic [1:0] {
    STATE_IDLE = 2'b00,
    STATE_READ = 2'b01,
    STATE_WRITE = 2'b10,
    STATE_ERROR = 2'b11
  } fsm_state_e;
  function automatic int get_next_power_of_2(input int value);
    if (value <= 0) return 1;
    return 1 << ($clog2(value-1) + 1);
  endfunction
endpackage
module Module_A_SimpleComb (
  input logic [7:0] in_data_a,
  input logic [7:0] in_data_b,
  output logic [8:0] out_sum_c
);
  assign out_sum_c = in_data_a + in_data_b;
endmodule
module Module_B_Sequential (
  input logic clk,
  input logic rst_n,
  input logic start_i,
  output logic done_o,
  output logic [3:0] count_o
);
  localparam [1:0] S0 = 2'b00, S1 = 2'b01, S2 = 2'b10, S3 = 2'b11;
  logic [1:0] current_state, next_state;
  logic [3:0] internal_count;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      current_state <= S0;
      internal_count <= 4'b0;
    end else begin
      current_state <= next_state;
      internal_count <= (current_state == S2) ? internal_count + 1 : internal_count;
    end
  end
  always_comb begin
    next_state = current_state;
    done_o = 1'b0;
    case (current_state)
      S0: if (start_i) next_state = S1;
      S1: next_state = S2;
      S2: if (internal_count == 4'd9) begin
            next_state = S3;
            done_o = 1'b1;
          end else begin
            next_state = S2;
          end
      S3: if (!start_i) next_state = S0;
    endcase
  end
  assign count_o = internal_count;
endmodule
module Module_C_MixedLogic (
  input logic [7:0] d_in,
  input logic en_latch,
  input logic clk,
  input logic rst,
  output logic [7:0] q_latch,
  output logic [7:0] q_ff_out
);
  logic [7:0] ff_reg;
  always_latch begin
    if (en_latch) begin
      q_latch = d_in;
    end
  end
  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      ff_reg <= 8'b0;
    end else begin
      ff_reg <= d_in;
    end
  end
  assign q_ff_out = ff_reg;
endmodule
module Module_D_TypesAndArrays (
  input logic [15:0] in_word,
  input byte in_byte,
  output int out_int_val,
  output longint out_long_val,
  output real out_real_val,
  output logic [3:0][7:0] out_packed_array,
  output logic [7:0] out_unpacked_array [0:3]
);
  int i_val;
  longint l_val;
  real r_val;
  logic [3:0][7:0] packed_arr;
  logic [7:0] unpacked_arr [0:3];
  initial begin
    i_val = 0;
    l_val = 0;
    r_val = 0.0;
    packed_arr = 0;
    for (int i=0; i<4; i++) begin
      unpacked_arr[i] = 0;
    end
  end
  always_comb begin
    i_val = int'(in_word);
    l_val = longint'(in_word) + in_byte;
    r_val = real'(in_word) / 2.0;
    packed_arr = in_word;
    for (int i=0; i<4; i++) begin
      unpacked_arr[i] = in_byte + i;
    end
    out_int_val = i_val;
    out_long_val = l_val;
    out_real_val = r_val;
    out_packed_array = packed_arr;
    for (int i=0; i<4; i++) begin
      out_unpacked_array[i] = unpacked_arr[i];
    end
  end
endmodule
module Module_E_ClassesAndDPI (
  input bit clk_i,
  input int seed_i,
  output int random_val_o,
  output int dpi_result_o
);
  import "DPI-C" function int c_add_one(input int val);
  class MyGenerator;
    rand int rand_num;
    int fixed_offset;
    constraint c_rand_num {
      rand_num > 10;
      rand_num < 100;
      rand_num % 2 == 0;
    }
    function new(int offset);
      fixed_offset = offset;
    endfunction
    function int get_next_val();
      return rand_num + fixed_offset;
    endfunction
  endclass
  MyGenerator gen_h;
  int current_rand_val;
  int current_dpi_val;
  always_ff @(posedge clk_i) begin
    if (gen_h == null) begin
      gen_h = new(seed_i);
      void'(gen_h.randomize());
    end else begin
      void'(gen_h.randomize());
    end
    current_rand_val = gen_h.get_next_val();
    current_dpi_val = c_add_one(current_rand_val);
  end
  assign random_val_o = current_rand_val;
  assign dpi_result_o = current_dpi_val;
endmodule
module Module_F_AssertionsAndCoverage (
  input logic clk,
  input logic rst_n,
  input logic [1:0] state_in,
  input logic data_valid,
  input logic [7:0] data_value,
  output logic ok_out
);
  localparam S_IDLE = 2'b00, S_BUSY = 2'b01, S_DONE = 2'b10;
  logic [1:0] current_fsm_state;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      current_fsm_state <= S_IDLE;
    end else begin
      case (current_fsm_state)
        S_IDLE: if (data_valid) current_fsm_state <= S_BUSY;
        S_BUSY: current_fsm_state <= S_DONE;
        S_DONE: current_fsm_state <= S_IDLE;
        default: current_fsm_state <= S_IDLE;
      endcase
    end
  end
  property p_data_valid_one_cycle;
    @(posedge clk) (data_valid && current_fsm_state == S_IDLE) |-> (!data_valid || current_fsm_state == S_BUSY);
  endproperty
  assert property (p_data_valid_one_cycle) else $warning("Assertion failed: data_valid held too long");
  assign ok_out = (current_fsm_state == S_DONE);
endmodule
module Module_G_GenerateBlock #(
  parameter NUM_WIDTH = 8,
  parameter ENABLE_A = 1
) (
  input logic [NUM_WIDTH-1:0] in_val,
  output logic [NUM_WIDTH-1:0] out_val
);
  logic [NUM_WIDTH-1:0] intermediate_val;
  if (ENABLE_A) begin : gen_block_A
    assign intermediate_val = in_val + 1;
  end else begin : gen_block_B
    assign intermediate_val = in_val - 1;
  end
  genvar i;
  for (i = 0; i < NUM_WIDTH; i = i + 1) begin : gen_bit_inv
    assign out_val[i] = ~intermediate_val[i];
  end
endmodule
module Module_H_Parameters #(
  parameter ADDR_WIDTH = 8,
  parameter DATA_WIDTH = 32,
  parameter MEM_SIZE = 256
) (
  input logic [ADDR_WIDTH-1:0] address,
  input logic [DATA_WIDTH-1:0] data_in,
  input logic write_en,
  output logic [DATA_WIDTH-1:0] data_out
);
  logic [DATA_WIDTH-1:0] memory [0:MEM_SIZE-1];
  initial begin
    for (int i=0; i<MEM_SIZE; i++) begin
      memory[i] = 0;
    end
  end
  always_comb begin
    if (write_en) begin
      memory[address] = data_in;
      data_out = '0;
    end else begin
      data_out = memory[address];
    end
  end
endmodule
interface Simple_Bus_IF #(parameter DATA_W = 8);
  logic [DATA_W-1:0] data;
  logic valid;
  logic ready;
  modport master (output data, output valid, input ready);
  modport slave (input data, input valid, output ready);
endinterface
module Module_I_Interface (
  Simple_Bus_IF.master master_if,
  input logic [3:0] transaction_count_in,
  input logic clk,
  input logic rst_n,
  output logic done_transaction_out
);
  logic [3:0] internal_count;
  logic [3:0] next_internal_count;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      internal_count <= 4'b0;
    end else begin
      internal_count <= next_internal_count;
    end
  end
  always_comb begin
    master_if.valid = (internal_count < transaction_count_in);
    master_if.data = internal_count + 1;
    next_internal_count = internal_count;
    if (master_if.valid && master_if.ready) begin
      next_internal_count = internal_count + 1;
    end
    done_transaction_out = (internal_count == transaction_count_in);
  end
endmodule
import my_package::*;
module Module_J_PackageUsage (
  input logic clk,
  input logic rst_n,
  input logic enable_proc,
  output fsm_state_e current_state_out,
  output int next_pow2_val_out
);
  fsm_state_e current_fsm_state_local;
  localparam int input_for_pow2 = 13;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      current_fsm_state_local <= STATE_IDLE;
    } else if (enable_proc) begin
      case (current_fsm_state_local)
        STATE_IDLE: current_fsm_state_local <= STATE_READ;
        STATE_READ: current_fsm_state_local <= STATE_WRITE;
        STATE_WRITE: current_fsm_state_local <= STATE_IDLE;
        default: current_fsm_state_local <= STATE_ERROR;
      endcase
    end
  end
  assign current_state_out = current_fsm_state_local;
  assign next_pow2_val_out = get_next_power_of_2(input_for_pow2);
endmodule
module Module_K_ComplexLogic (
  input logic [31:0] data_in_k,
  input logic [7:0] addr_k,
  input logic [1:0] op_mode_k,
  output logic [31:0] result_k
);
  logic [31:0] mem [0:255];
  logic [31:0] temp_val_a, temp_val_b;
  initial begin
    for (int i=0; i<256; i++) begin
      mem[i] = i * 3 + 1;
    end
  end
  always_comb begin
    temp_val_a = data_in_k;
    temp_val_b = mem[addr_k];
    case (op_mode_k)
      2'b00: result_k = temp_val_a + temp_val_b;
      2'b01: begin
        result_k = temp_val_a - temp_val_b;
        if (result_k[31]) result_k = ~result_k + 1;
      end
      2'b10: begin
        result_k = temp_val_a ^ temp_val_b;
        for (int i = 0; i < 32; i++) begin
          if (i % 3 == 0) result_k[i] = ~result_k[i];
        end
      end
      2'b11: begin
        result_k = (temp_val_a <<< (addr_k[4:0])) | (temp_val_b >>> (addr_k[4:0]));
      end
      default: result_k = '0;
    endcase
  end
endmodule
module Module_L_ManyInputsOutputs (
  input logic i_a, i_b, i_c, i_d, i_e, i_f, i_g, i_h,
  input logic [7:0] i_data_0, i_data_1, i_data_2, i_data_3,
  output logic o_x, o_y, o_z, o_w,
  output logic [7:0] o_res_0, o_res_1, o_res_2, o_res_3
);
  assign o_x = i_a && i_b;
  assign o_y = i_c || i_d;
  assign o_z = i_e ^ i_f;
  assign o_w = ~(i_g && i_h);
  assign o_res_0 = i_data_0 + i_data_1;
  assign o_res_1 = i_data_1 - i_data_2;
  assign o_res_2 = i_data_2 * i_data_3;
  assign o_res_3 = i_data_3 / (i_data_0 + 1);
endmodule
module Module_M_LargeArrayLogic #(
  parameter ARRAY_DEPTH = 1024
) (
  input logic [7:0] write_data_m,
  input logic [$clog2(ARRAY_DEPTH)-1:0] write_addr_m,
  input logic write_en_m,
  output logic [7:0] read_data_m,
  input logic [$clog2(ARRAY_DEPTH)-1:0] read_addr_m
);
  logic [7:0] large_memory [0:ARRAY_DEPTH-1];
  initial begin
    for (int i=0; i<ARRAY_DEPTH; i++) begin
      large_memory[i] = i % 256;
    end
  end
  always_comb begin
    if (write_en_m) begin
      large_memory[write_addr_m] = write_data_m;
    end
    read_data_m = large_memory[read_addr_m];
  end
endmodule
module Internal_Sub_Module (
  input logic sub_clk,
  input logic sub_rst,
  input logic [7:0] sub_in,
  output logic [7:0] sub_out
);
  logic [7:0] sub_reg;
  always_ff @(posedge sub_clk or posedge sub_rst) begin
    if (sub_rst) sub_reg <= 8'b0;
    else sub_reg <= sub_in;
  end
  assign sub_out = sub_reg;
endmodule
module Module_N_HierarchicalPossibility (
  input logic clk_n,
  input logic rst_n_n,
  input logic [7:0] data_in_n,
  output logic [7:0] data_out_n
);
  logic [7:0] processed_data;
  logic [7:0] sub_module_output;
  Internal_Sub_Module sub_inst (
    .sub_clk(clk_n),
    .sub_rst(rst_n_n),
    .sub_in(data_in_n),
    .sub_out(sub_module_output)
  );
  assign processed_data = sub_module_output + 1;
  assign data_out_n = processed_data;
endmodule
module Module_O_DPIExports (
  input int in_val_o,
  output int out_val_o
);
  export "DPI-C" function sv_multiply_by_two;
  function automatic int sv_multiply_by_two(input int val);
    return val * 2;
  endfunction
  assign out_val_o = sv_multiply_by_two(in_val_o);
endmodule
module Module_P_EnumLogic (
  input logic [1:0] op_code_p,
  input logic [7:0] data_a_p,
  input logic [7:0] data_b_p,
  output logic [7:0] result_p
);
  typedef enum logic [1:0] {
    ADD_OP = 2'b00,
    SUB_OP = 2'b01,
    AND_OP = 2'b10,
    OR_OP   = 2'b11
  } operation_e;
  operation_e current_op;
  always_comb begin
    current_op = operation_e'(op_code_p);
    case (current_op)
      ADD_OP: result_p = data_a_p + data_b_p;
      SUB_OP: result_p = data_a_p - data_b_p;
      AND_OP: result_p = data_a_p & data_b_p;
      OR_OP:  result_p = data_a_p | data_b_p;
      default: result_p = '0;
    endcase
  end
endmodule
module Module_Q_StructUnion (
  input logic [15:0] in_packed_val,
  input logic [15:0] in_unpacked_val_a,
  input logic [15:0] in_unpacked_val_b,
  input logic select_union,
  output logic [7:0] out_struct_field,
  output logic [15:0] out_union_data
);
  typedef struct packed {
    logic [7:0] field_a;
    logic [7:0] field_b;
  } my_packed_struct_t;
  typedef struct {
    logic [7:0] val1;
    logic [7:0] val2;
  } my_unpacked_struct_t;
  typedef union packed {
    logic [15:0] combined_val;
    my_packed_struct_t fields_val;
  } my_union_t;
  my_packed_struct_t  packed_s;
  my_unpacked_struct_t unpacked_s;
  my_union_t          u_val;
  always_comb begin
    packed_s = in_packed_val;
    unpacked_s.val1 = in_unpacked_val_a[7:0];
    unpacked_s.val2 = in_unpacked_val_b[7:0];
    if (select_union) begin
      u_val.combined_val = in_unpacked_val_a;
    end else begin
      u_val.fields_val.field_a = in_unpacked_val_a[7:0];
      u_val.fields_val.field_b = in_unpacked_val_b[7:0];
    end
    out_struct_field = packed_s.field_a;
    out_union_data = u_val.combined_val;
  end
endmodule
module Module_R_SignedUnsigned (
  input logic signed [31:0] in_signed_a,
  input logic signed [31:0] in_signed_b,
  input logic unsigned [31:0] in_unsigned_c,
  input logic unsigned [31:0] in_unsigned_d,
  output logic signed [31:0] out_signed_sum,
  output logic unsigned [31:0] out_unsigned_product
);
  int temp_signed;
  logic unsigned [31:0] temp_unsigned;
  always_comb begin
    temp_signed = in_signed_a + in_signed_b;
    temp_unsigned = in_unsigned_c * in_unsigned_d;
    out_signed_sum = temp_signed;
    out_unsigned_product = temp_unsigned;
    if (in_signed_a < 0) begin
      out_unsigned_product = unsigned'(in_signed_a) + in_unsigned_c;
    end
  end
endmodule
module Module_S_TasksFunctions (
  input logic [7:0] value1_s,
  input logic [7:0] value2_s,
  input logic enable_add_s,
  input logic reset_counter_s,
  input logic clk_s,
  output logic [7:0] sum_s,
  output logic [3:0] counter_s
);
  logic [3:0] internal_counter;
  function automatic logic [7:0] calculate_sum(input logic [7:0] a, input logic [7:0] b);
    return a + b;
  endfunction
  task automatic increment_counter(output logic [3:0] current_val);
    current_val = current_val + 1;
  endtask
  initial begin
    internal_counter = 4'b0;
  end
  always_comb begin
    if (enable_add_s) begin
      sum_s = calculate_sum(value1_s, value2_s);
    end else begin
      sum_s = '0;
    end
  end
  always_ff @(posedge clk_s or posedge reset_counter_s) begin
    if (reset_counter_s) begin
      internal_counter <= 4'b0;
    end else begin
      increment_counter(internal_counter);
    end
  end
  assign counter_s = internal_counter;
endmodule
module Module_T_RealTime (
  input logic clk_t,
  input logic rst_n_t,
  input logic toggle_t,
  output real current_real_val_t,
  output int current_scaled_val_t
);
  real reg_real_val;
  int reg_int_val;
  always_ff @(posedge clk_t or negedge rst_n_t) begin
    if (!rst_n_t) begin
      reg_real_val <= 0.0;
      reg_int_val <= 0;
    end else if (toggle_t) begin
      reg_real_val <= reg_real_val + 1.0;
      reg_int_val <= reg_int_val + 1;
    end else begin
      reg_real_val <= reg_real_val;
      reg_int_val <= reg_int_val;
    end
  end
  assign current_real_val_t = reg_real_val;
  assign current_scaled_val_t = reg_int_val;
endmodule
