package my_package;
  typedef struct packed {
    logic [7:0] id;
    logic [31:0] address;
  } my_request_t;
  typedef enum logic [1:0] {
    STATE_IDLE,
    STATE_BUSY,
    STATE_DONE
  } my_state_e;
  function automatic int add_two(int a, int b);
    return a + b;
  endfunction
  function automatic int multiply_two(int a, int b);
    return a * b;
  endfunction
endpackage
interface my_interface(input logic clk);
  logic req;
  logic [7:0] data;
  logic ack;
  logic [15:0] response;
  modport Master (output req, output data, input ack, input response, input clk);
  modport Slave (input req, input data, output ack, output response, input clk);
endinterface
module Module_CombinationalLogic(
  input logic [7:0] i_data_in,
  input logic [1:0] i_sel,
  input logic i_enable_parity,
  output logic [7:0] o_processed_data,
  output logic o_parity_out
);
  logic [7:0] temp_result;
  always_comb begin
    case (i_sel)
      2'b00: temp_result = i_data_in + 8'd5;
      2'b01: temp_result = i_data_in << 1;
      2'b10: temp_result = i_data_in ^ 8'hFF;
      default: temp_result = i_data_in;
    endcase
  end
  assign o_processed_data = temp_result;
  always_comb begin
    if (i_enable_parity) begin
      o_parity_out = ^temp_result;
    end else begin
      o_parity_out = 1'b0;
    end
  end
endmodule
module Module_SequentialLogic(
  input logic i_clk,
  input logic i_rst_n,
  input logic [15:0] i_data_in,
  input logic i_load_data,
  output logic [15:0] o_registered_data
);
  logic [15:0] current_data;
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
      current_data <= 16'h0000;
    end else if (i_load_data) begin
      current_data <= i_data_in;
    end else begin
      current_data <= current_data + 1;
    end
  end
  assign o_registered_data = current_data;
endmodule
module Module_ComplexTypes(
  input logic [7:0] i_struct_val_a,
  input logic [7:0] i_struct_val_b,
  input logic [1:0] i_enum_select,
  input logic [31:0] i_union_raw_val,
  output logic [7:0] o_struct_sum,
  output logic [1:0] o_enum_state,
  output int o_union_int_val
);
  typedef struct packed {
    logic [7:0] field_a;
    logic [7:0] field_b;
  } my_local_struct_t;
  typedef enum {
    STATE_A,
    STATE_B,
    STATE_C
  } my_local_state_e;
  typedef union packed {
    logic [31:0] raw_bits;
    int          as_int;
  } my_local_union_t;
  my_local_struct_t current_struct;
  my_local_state_e  current_enum_state;
  my_local_union_t  current_union;
  always_comb begin
    current_struct.field_a = i_struct_val_a;
    current_struct.field_b = i_struct_val_b;
    o_struct_sum = current_struct.field_a + current_struct.field_b;
    case (i_enum_select)
      2'b00: current_enum_state = STATE_A;
      2'b01: current_enum_state = STATE_B;
      default: current_enum_state = STATE_C;
    endcase
    o_enum_state = current_enum_state;
    current_union.raw_bits = i_union_raw_val;
    o_union_int_val = current_union.as_int;
  end
endmodule
module Module_ArraysAndQueues(
  input logic [7:0] i_input_val,
  input logic [3:0] i_fixed_idx,
  input logic i_add_assoc,
  input logic [7:0] i_assoc_key,
  input logic [7:0] i_assoc_val,
  input logic i_push_dyn,
  input logic i_pop_dyn,
  input logic i_push_q,
  output logic [7:0] o_fixed_array_val,
  output logic [7:0] o_assoc_array_val,
  output logic [7:0] o_dynamic_array_sum,
  output logic [7:0] o_queue_front_val
);
  logic [7:0] fixed_array [0:9];
  logic [7:0] dynamic_array [];
  logic [7:0] associative_array [logic [7:0]];
  logic [7:0] data_queue [$];
  initial begin
    for (int k = 0; k < 10; k++) begin
      fixed_array[k] = k;
    end
  end
  always_comb begin
    o_fixed_array_val = fixed_array[i_fixed_idx % 10];
    if (i_add_assoc) begin
      associative_array[i_assoc_key] = i_assoc_val;
    end
    if (associative_array.exists(i_assoc_key)) begin
      o_assoc_array_val = associative_array[i_assoc_key];
    end else begin
      o_assoc_array_val = 8'h00;
    end
    dynamic_array = new[2];
    dynamic_array[0] = i_input_val;
    dynamic_array[1] = i_input_val + 1;
    o_dynamic_array_sum = dynamic_array[0] + dynamic_array[1];
    if (i_push_q) begin
      data_queue.push_back(i_input_val);
    end
    if (i_pop_dyn && data_queue.size() > 0) begin
      void'(data_queue.pop_front()); 
    end
    if (data_queue.size() > 0) begin
      o_queue_front_val = data_queue[0];
    end else begin
      o_queue_front_val = 8'hFF;
    end
  end
endmodule
module Module_SystemVerilogClasses(
  input logic i_clk,
  input logic i_rst_n,
  input logic [31:0] i_param_a,
  input logic [31:0] i_param_b,
  input logic i_trigger_calc,
  output logic [31:0] o_class_result,
  output logic o_class_valid
);
  class BaseCalculator;
    protected int m_val_a;
    protected int m_val_b;
    function new();
      m_val_a = 0;
      m_val_b = 0;
    endfunction
    function void set_params(int p_a, int p_b);
      this.m_val_a = p_a;
      this.m_val_b = p_b;
    endfunction
    virtual function automatic int calculate();
      return m_val_a + m_val_b;
    endfunction
  endclass
  class Multiplier extends BaseCalculator;
    function new();
      super.new();
    endfunction
    virtual function automatic int calculate();
      return m_val_a * m_val_b;
    endfunction
  endclass
  BaseCalculator my_calculator_handle;
  logic [31:0] local_class_result_reg;
  logic local_class_valid_reg;
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
      local_class_result_reg <= 0;
      local_class_valid_reg <= 0;
      my_calculator_handle <= null; 
    end else begin
      if (my_calculator_handle == null) begin
        my_calculator_handle <= Multiplier::new(); 
      end
      if (i_trigger_calc) begin
        my_calculator_handle.set_params(i_param_a, i_param_b);
        local_class_result_reg <= my_calculator_handle.calculate();
        local_class_valid_reg <= 1'b1;
      end else begin
        local_class_valid_reg <= 1'b0;
      end
    end
  end
  assign o_class_result = local_class_result_reg;
  assign o_class_valid = local_class_valid_reg;
endmodule
module Module_FunctionsAndTasks(
  input int i_input_a,
  input int i_input_b,
  input logic i_enable_task,
  output int o_func_out,
  output int o_task_out
);
  function automatic int recursive_factorial(int n);
    if (n < 0 || n > 12) return 0; 
    if (n <= 1) return 1;
    return n * recursive_factorial(n - 1);
  endfunction
  task automatic process_values(input int val1, input int val2, ref int result);
    result = val1 * 2 + val2 * 3;
  endtask
  int local_task_result;
  always_comb begin
    o_func_out = recursive_factorial(i_input_a % 7); 
    local_task_result = 0;
    if (i_enable_task) begin
      process_values(i_input_a, i_input_b, local_task_result);
    end
    o_task_out = local_task_result;
  end
endmodule
module Module_ParameterGenerators #(
  parameter WIDTH = 8,
  parameter NUM_UNITS = 2
) (
  input logic [WIDTH-1:0] i_data_in,
  input logic [NUM_UNITS-1:0] i_enables,
  input int i_select_unit,
  output logic [WIDTH-1:0] o_processed_data,
  output logic o_any_unit_enabled
);
  localparam ADD_VALUE = 4;
  logic [WIDTH-1:0] unit_outputs [NUM_UNITS-1:0];
  logic [NUM_UNITS-1:0] unit_enabled_flags;
  generate
    for (genvar i = 0; i < NUM_UNITS; i++) begin : gen_units
      localparam UNIT_OFFSET = i * 2;
      if (i == 0) begin
        always_comb begin
          unit_outputs[i] = i_data_in + ADD_VALUE;
          unit_enabled_flags[i] = i_enables[i];
        end
      end else begin
        always_comb begin
          unit_outputs[i] = i_data_in ^ UNIT_OFFSET;
          unit_enabled_flags[i] = i_enables[i];
        end
      end
    end
  endgenerate
  always_comb begin
    if (i_select_unit >= 0 && i_select_unit < NUM_UNITS) begin
      o_processed_data = unit_outputs[i_select_unit];
    end else begin
      o_processed_data = '0; 
    end
    o_any_unit_enabled = |unit_enabled_flags;
  end
endmodule
module Module_InterfaceAndPackage(
  input logic i_clk,
  input logic i_slave_req,
  input logic [7:0] i_slave_data,
  output logic o_slave_ack,
  output logic [15:0] o_slave_response,
  output logic [7:0] o_slave_data_processed,
  output logic o_master_req,
  output logic [7:0] o_master_data,
  input logic i_master_ack,
  input logic [15:0] i_master_response,
  output logic [15:0] o_master_response_received,
  input int i_pkg_val1,
  input int i_pkg_val2,
  output my_package::my_request_t o_pkg_request_type,
  output my_package::my_state_e o_pkg_enum_state,
  output int o_pkg_sum_result,
  output int o_pkg_mul_result
);
  import my_package::*;
  always_comb begin
    o_slave_response = {8'hAB, i_slave_data};
    o_slave_ack = i_slave_req;
    o_slave_data_processed = i_slave_data;
  end
  always_comb begin
    o_master_req = 1'b1;
    o_master_data = {i_pkg_val1[7:0]}; 
    o_master_response_received = i_master_response;
  end
  my_package::my_request_t local_request;
  my_package::my_state_e local_enum_state;
  always_comb begin
    local_request.id = i_pkg_val1[7:0]; 
    local_request.address = i_pkg_val2;
    o_pkg_request_type = local_request;
    local_enum_state = (i_pkg_val1 > 10) ? STATE_BUSY : STATE_IDLE;
    o_pkg_enum_state = local_enum_state;
    o_pkg_sum_result = add_two(i_pkg_val1, i_pkg_val2);
    o_pkg_mul_result = multiply_two(i_pkg_val1, i_pkg_val2);
  end
endmodule
