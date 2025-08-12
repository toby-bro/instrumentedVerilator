package sv_types_pkg;
  typedef enum {
    IDLE,
    PROCESSING,
    DONE,
    ERROR_STATE
  } fsm_state_e;
  typedef struct packed {
    logic [7:0] header_byte;
    logic [15:0] payload_word;
    bit         valid;
  } packet_t;
  typedef class MyGenericClass;
  class MyGenericClass;
    int m_value;
    string m_name;
    function new(int initial_value, string name);
      m_value = initial_value;
      m_name = name;
    endfunction
    function int get_value();
      return m_value;
    endfunction
    function void set_value(int new_value);
      m_value = new_value;
    endfunction
    function string get_name();
      return m_name;
    endfunction
  endclass
endpackage
import sv_types_pkg::*;
module CombinationalProcessor (
  input  logic [15:0] in_data_a,
  input  logic [15:0] in_data_b,
  output logic [15:0] out_result,
  output packet_t     out_processed_packet
);
  logic [15:0] intermediate_sum;
  logic [7:0]  data_buffer [8]; 
  assign intermediate_sum = in_data_a + in_data_b;
  assign out_result = intermediate_sum ^ {16{1'b1}}; 
  always_comb begin
    for (int i = 0; i < 8; i++) begin
      data_buffer[i] = in_data_a[7:0] + i;
    end
    out_processed_packet.header_byte = data_buffer[0];
    out_processed_packet.payload_word = {data_buffer[1], data_buffer[2]};
    out_processed_packet.valid = (out_result != 0);
  end
endmodule
module StateMachineLogic (
  input  logic        clk,
  input  logic        reset_n,
  input  logic        start_operation,
  output logic        operation_complete,
  output fsm_state_e  current_fsm_state
);
  fsm_state_e current_state_reg;
  fsm_state_e next_state_wire;
  localparam int PROCESS_CYCLES = 4;
  int cycle_counter;
  always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      current_state_reg <= IDLE;
      cycle_counter <= 0;
    end else begin
      current_state_reg <= next_state_wire;
      if (next_state_wire == PROCESSING && current_state_reg == PROCESSING) begin
        cycle_counter <= cycle_counter + 1;
      end else begin
        cycle_counter <= 0;
      end
    end
  end
  always_comb begin
    next_state_wire = current_state_reg;
    operation_complete = 1'b0;
    case (current_state_reg)
      IDLE: begin
        if (start_operation) begin
          next_state_wire = PROCESSING;
        end
      end
      PROCESSING: begin
        if (cycle_counter >= PROCESS_CYCLES - 1) begin 
          next_state_wire = DONE;
        end
      end
      DONE: begin
        operation_complete = 1'b1;
        if (!start_operation) begin 
          next_state_wire = IDLE;
        end
      end
      default: begin 
        next_state_wire = IDLE; 
      end
    endcase
    current_fsm_state = current_state_reg;
  end
endmodule
module DataManipulator (
  input  logic [7:0]  data_to_store,
  input  int          key_input,
  input  int          key_to_retrieve,
  output logic [7:0]  retrieved_data,
  output logic        key_found_flag
);
  logic [7:0] storage_map [*];
  function logic [7:0] invert_and_add_one(logic [7:0] in_byte);
    return (~in_byte) + 1; 
  endfunction
  task add_data_to_map(logic [7:0] value, int key);
    storage_map[key] = value;
  endtask
  task remove_data_from_map(int key);
    if (storage_map.exists(key)) begin
      storage_map.delete(key);
    end
  endtask
  always_comb begin
    add_data_to_map(data_to_store, key_input);
    if (storage_map.exists(key_to_retrieve)) begin
      retrieved_data = invert_and_add_one(storage_map[key_to_retrieve]);
      key_found_flag = 1'b1;
    end else begin
      retrieved_data = '0;
      key_found_flag = 1'b0;
    end
    if (key_input == 0) begin
        remove_data_from_map(0);
    end
  end
endmodule
module ClassUser (
  input  logic        clk,
  input  logic        reset_n,
  input  logic [31:0] initial_value_in,
  input  logic [31:0] update_value_in,
  input  logic        do_update_op,
  output logic [31:0] current_value_out,
  output string       instance_name_out
);
  MyGenericClass my_class_handle; 
  logic          is_instantiated; 
  always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      my_class_handle <= null; 
      is_instantiated <= 1'b0;
    end else begin
      if (!is_instantiated && my_class_handle == null) begin
        my_class_handle <= new(initial_value_in, "MyFirstInstance");
        is_instantiated <= 1'b1;
      end else if (is_instantiated && do_update_op && my_class_handle != null) begin
        my_class_handle.set_value(update_value_in);
      end
    end
  end
  always_comb begin
    if (is_instantiated && my_class_handle != null) begin
      current_value_out = my_class_handle.get_value();
      instance_name_out = my_class_handle.get_name();
    end else begin
      current_value_out = '0;
      instance_name_out = ""; 
    end
  end
endmodule
module ParameterizedProcessor #(
  parameter int DATA_WIDTH = 16,
  parameter int SHIFT_AMOUNT = 4
) (
  input  logic [DATA_WIDTH-1:0] input_data,
  output logic [DATA_WIDTH-1:0] output_data
);
  localparam logic [DATA_WIDTH-1:0] MASK = (DATA_WIDTH > SHIFT_AMOUNT) ? ({DATA_WIDTH{1'b1}} << SHIFT_AMOUNT) : '0;
  logic [DATA_WIDTH-1:0] shifted_data;
  assign shifted_data = input_data << SHIFT_AMOUNT;
  assign output_data = shifted_data & MASK; 
endmodule
module UnpackedArraySorter (
  input  logic [7:0] data_in_array [4], 
  input  logic       sort_enable,
  output logic [7:0] sorted_max_val_out
);
  logic [7:0] internal_storage [4]; 
  logic [7:0] current_max_val;
  always_comb begin
    for (int i = 0; i < 4; i++) begin
      internal_storage[i] = data_in_array[i];
    end
    current_max_val = '0; 
    if (sort_enable) begin
      for (int i = 0; i < 4; i++) begin
        if (internal_storage[i] > current_max_val) begin
          current_max_val = internal_storage[i];
        end
      end
    end else begin
      current_max_val = data_in_array[0];
    end
    sorted_max_val_out = current_max_val;
  end
endmodule
module ProtocolParser (
  input  logic [31:0] raw_data_word,
  input  logic        is_command_type,
  output logic [15:0] parsed_header_info,
  output logic [7:0]  parsed_data_field
);
  typedef struct packed {
    logic [15:0] protocol_id;
    logic [15:0] message_length;
  } message_header_s;
  typedef struct packed {
    logic [7:0] command_code;
    logic [7:0] target_address;
    logic [15:0] crc_value;
  } command_packet_s;
  typedef union packed {
    message_header_s message_pkt;
    command_packet_s command_pkt;
    logic [31:0]     full_word;
  } protocol_union_u;
  protocol_union_u current_protocol_data;
  always_comb begin
    current_protocol_data.full_word = raw_data_word;
    if (is_command_type) begin
      parsed_header_info = {current_protocol_data.command_pkt.command_code, current_protocol_data.command_pkt.target_address};
      parsed_data_field = current_protocol_data.command_pkt.command_code; 
    end else begin
      parsed_header_info = current_protocol_data.message_pkt.protocol_id;
      parsed_data_field = current_protocol_data.message_pkt.message_length[7:0]; 
    end
  end
endmodule
module FloatingPointProcessor (
  input  real       operand_a,
  input  real       operand_b,
  output real       result_sum,
  output shortreal  result_product
);
  real intermediate_sum_val;
  shortreal intermediate_prod_val;
  assign intermediate_sum_val = operand_a + operand_b;
  assign intermediate_prod_val = $realtobits(operand_a) * $realtobits(operand_b); 
  assign result_sum = intermediate_sum_val;
  assign result_product = intermediate_prod_val;
endmodule
interface RegisterAccessInterface (
  input logic clk,
  input logic reset
);
  logic        valid;
  logic        ready;
  logic [7:0]  addr;
  logic [31:0] wdata;
  logic [31:0] rdata;
  logic        wr_nrd; 
  modport Master (
    output valid, addr, wdata, wr_nrd,
    input  ready, rdata
  );
  modport Slave (
    input  valid, addr, wdata, wr_nrd,
    output ready, rdata
  );
endinterface
module SafetyChecker (
  input  logic [7:0]  input_pressure,
  input  logic        sensor_active,
  input  logic        system_enabled,
  output logic        safety_violation
);
  logic local_violation;
  always_comb begin
    local_violation = 1'b0;
    assert (sensor_active == 1'b0 || (input_pressure >= 10 && input_pressure <= 200))
    else begin
      local_violation = 1'b1;
    end
    assert (!(system_enabled && input_pressure > 220))
    else begin
      local_violation = 1'b1;
    end
    safety_violation = local_violation;
  end
endmodule
module FunctionalCoverageMonitor (
  input  logic [1:0]  mode_setting,
  input  logic [7:0]  data_value,
  input  logic        event_trigger,
  output logic        sampling_done
);
  covergroup ControlDataCoverage;
    option.per_instance = 1; 
    mode_cp: coverpoint mode_setting {
      bins M_IDLE = {2'b00};
      bins M_ACTIVE = {2'b01, 2'b10};
      bins M_ERROR = {2'b11};
    }
    data_cp: coverpoint data_value iff (event_trigger) {
      bins D_ZERO = {8'h00};
      bins D_LOW  = {[1:63]};
      bins D_HIGH = {[64:255]};
    }
    mode_data_cross: cross mode_cp, data_cp;
  endgroup
  ControlDataCoverage cg_instance = new();
  always_comb begin
    sampling_done = 1'b0;
    if (event_trigger) begin
      cg_instance.sample();
      sampling_done = 1'b1;
    end
  end
endmodule
