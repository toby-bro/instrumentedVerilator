module CombinationalProcessor (
  input logic [7:0] a_in,
  input logic [7:0] b_in,
  input logic       sel_in,
  output logic [7:0] out_add_sub,
  output logic [7:0] out_mul_div,
  output logic [7:0] out_logic_shift,
  output logic [7:0] out_cond
);
  logic [7:0] temp_val;
  assign out_add_sub = sel_in ? (a_in + b_in) : (a_in - b_in);
  assign out_mul_div = (b_in == 0) ? 8'b0 : (a_in / b_in);
  assign out_logic_shift = (a_in & b_in) | (a_in << 1);
  assign out_cond = (a_in > b_in) ? a_in : b_in;
endmodule
module SimpleRegisterCounter (
  input logic         clk,
  input logic         rst_n,
  input logic [3:0]   data_in,
  input logic         load_en,
  input logic         count_en,
  output logic [3:0]  q_reg_out,
  output logic [3:0]  q_counter_out
);
  logic [3:0] internal_register;
  logic [3:0] internal_counter;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      internal_register <= 4'b0;
    end else if (load_en) begin
      internal_register <= data_in;
    end
  end
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      internal_counter <= 4'b0;
    end else if (count_en) begin
      internal_counter <= internal_counter + 1;
    end
  end
  assign q_reg_out = internal_register;
  assign q_counter_out = internal_counter;
endmodule
module DataTypeProcessor (
  input logic [1:0] op_code_in,
  input logic [7:0] value_a_in,
  input logic [7:0] value_b_in,
  output logic [15:0] result_out
);
  typedef enum logic [1:0] {
    ADD_OP,
    SUB_OP,
    MUL_OP,
    DIV_OP
  } OperationType_e;
  typedef struct packed {
    logic [7:0] operand1;
    logic [7:0] operand2;
    OperationType_e operation;
  } OperationPacket_t;
  typedef union packed {
    logic [15:0] full_result;
    struct packed {
      logic [7:0] low_byte;
      logic [7:0] high_byte;
    } bytes;
  } ResultUnion_u;
  OperationPacket_t current_packet;
  ResultUnion_u internal_result_union;
  logic [15:0] temp_result_val;
  always_comb begin
    current_packet.operand1 = value_a_in;
    current_packet.operand2 = value_b_in;
    current_packet.operation = OperationType_e'(op_code_in);
    temp_result_val = 16'b0;
    case (current_packet.operation)
      ADD_OP: temp_result_val = current_packet.operand1 + current_packet.operand2;
      SUB_OP: temp_result_val = current_packet.operand1 - current_packet.operand2;
      MUL_OP: temp_result_val = current_packet.operand1 * current_packet.operand2;
      DIV_OP: temp_result_val = (current_packet.operand2 == 8'b0) ? 16'hFFFF : (current_packet.operand1 / current_packet.operand2);
      default: temp_result_val = 16'hXXXX;
    endcase
    internal_result_union.full_result = temp_result_val;
    result_out = internal_result_union.full_result;
  end
endmodule
module MemoryArray (
  input logic         clk,
  input logic         rst_n,
  input logic         we_in,
  input logic [3:0]   addr_in,
  input logic [7:0]   data_wr_in,
  output logic [7:0]  data_rd_out
);
  logic [7:0] memory [0:15];
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      for (int i = 0; i < 16; i++) begin
        memory[i] <= 8'h00;
      end
    end else if (we_in) begin
      memory[addr_in] <= data_wr_in;
    end
  end
  assign data_rd_out = memory[addr_in];
endmodule
module FuncTaskProcessor (
  input logic [15:0] val1_in,
  input logic [15:0] val2_in,
  input logic        op_en,
  input logic        trigger_task,
  output logic [15:0] func_result_out,
  output logic [15:0] task_result_out
);
  logic [15:0] internal_func_res;
  logic [15:0] internal_task_res;
  function automatic logic [15:0] calculate_sum_diff (input logic [15:0] a, input logic [15:0] b, input logic do_sum);
    if (do_sum) begin
      return a + b;
    end else begin
      return a - b;
    end
  endfunction
  task automatic perform_complex_op (input logic [15:0] x, input logic [15:0] y, output logic [15:0] z);
    logic [15:0] temp_val_task;
    temp_val_task = (x * y) >> 1;
    z = temp_val_task;
  endtask
  always_comb begin
    internal_func_res = calculate_sum_diff(val1_in, val2_in, op_en);
    func_result_out = internal_func_res;
    if (trigger_task) begin
      perform_complex_op(val1_in, val2_in, internal_task_res);
    end else begin
      internal_task_res = 16'b0;
    end
    task_result_out = internal_task_res;
  end
endmodule
module ClassHandler (
  input logic         clk,
  input logic         rst_n,
  input logic         trigger_alloc_set_read,
  input logic [7:0]   initial_val_in,
  output logic [7:0]  class_data_out,
  output logic        class_valid_out
);
  class MySimpleClass;
    local logic [7:0] m_data;
    function new(logic [7:0] init_val);
      m_data = init_val;
    endfunction
    function void set_data(logic [7:0] new_val);
      m_data = new_val;
    endfunction
    function logic [7:0] get_data();
      return m_data;
    endfunction
  endclass
  MySimpleClass my_instance;
  logic [7:0] internal_class_data;
  logic internal_class_valid;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      my_instance = null;
      internal_class_data = 8'b0;
      internal_class_valid = 1'b0;
    end else if (trigger_alloc_set_read) begin
      if (my_instance == null) begin
        my_instance = new(initial_val_in);
      end else begin
        my_instance.set_data(initial_val_in + 1);
      end
      internal_class_data = my_instance.get_data();
      internal_class_valid = 1'b1;
    end else begin
      if (my_instance != null) begin
        internal_class_data = my_instance.get_data();
        internal_class_valid = 1'b1;
      end else begin
        internal_class_data = 8'b0;
        internal_class_valid = 1'b0;
      end
    end
  end
  assign class_data_out = internal_class_data;
  assign class_valid_out = internal_class_valid;
endmodule
module ParametrizedAdder #(
  parameter WIDTH = 8
) (
  input logic [WIDTH-1:0] data_a_in,
  input logic [WIDTH-1:0] data_b_in,
  input logic             carry_in,
  output logic [WIDTH-1:0] sum_out,
  output logic             carry_out
);
  logic [WIDTH:0] carries;
  assign carries[0] = carry_in;
  generate
    for (genvar i = 0; i < WIDTH; i++) begin : gen_adder_bits
      logic bit_a, bit_b, bit_sum, bit_carry_out;
      assign bit_a = data_a_in[i];
      assign bit_b = data_b_in[i];
      assign bit_sum = bit_a ^ bit_b ^ carries[i];
      assign bit_carry_out = (bit_a & bit_b) | (bit_a & carries[i]) | (bit_b & carries[i]);
      assign sum_out[i] = bit_sum;
      assign carries[i+1] = bit_carry_out;
    end
  endgenerate
  assign carry_out = carries[WIDTH];
endmodule
module AssertionChecker (
  input logic clk,
  input logic rst_n,
  input logic req_in,
  input logic gnt_in,
  output logic assertion_ok
);
  logic busy_state;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      busy_state <= 1'b0;
    end else begin
      if (req_in) begin
        busy_state <= 1'b1;
      end else if (gnt_in) begin
        busy_state <= 1'b0;
      end
    end
  end
  always_ff @(posedge clk) begin
    if (busy_state && req_in) begin
      assert (gnt_in || !busy_state);
    end
  end
  property req_not_concurrent_with_gnt;
    @(posedge clk) req_in |-> !gnt_in;
  endproperty
  assert property (req_not_concurrent_with_gnt);
  assign assertion_ok = 1'b1;
endmodule
