module SimpleLogicAndParams #(
  parameter WIDTH = 8,
  parameter INIT_VAL = 4'hA
) (
  input  logic [WIDTH-1:0] in_data,
  input  logic             clk,
  input  logic             reset_n,
  input  logic             control_sel,
  output logic [WIDTH-1:0] out_reg_q,
  output logic [WIDTH-1:0] out_comb_result
);
  localparam ADD_OFFSET = 1;
  logic [WIDTH-1:0] internal_wire_a;
  logic [WIDTH-1:0] internal_wire_b;
  always_comb begin
    if (control_sel) begin
      internal_wire_a = in_data + ADD_OFFSET;
    end else begin
      internal_wire_a = in_data - ADD_OFFSET;
    end
    internal_wire_b = ~internal_wire_a;
    out_comb_result = internal_wire_b | {WIDTH{1'b0}};
  end
  always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      out_reg_q <= INIT_VAL;
    end else begin
      out_reg_q <= out_comb_result;
    end
  end
endmodule
module EnumAndStructHandler (
  input  logic       clk,
  input  logic       reset_n,
  input  logic [7:0] data_in,
  input  logic [1:0] opcode_in,
  output logic [7:0] processed_data_out,
  output logic        error_flag
);
  typedef enum logic [1:0] {
    OP_NOP    = 2'b00,
    OP_ADD    = 2'b01,
    OP_SUB    = 2'b10,
    OP_MUL    = 2'b11
  } operation_e;
  typedef struct packed {
    logic [7:0] value;
    logic       valid;
  } data_packet_t;
  operation_e current_op;
  data_packet_t input_packet;
  data_packet_t output_packet;
  always_comb begin
    current_op = operation_e'(opcode_in);
    input_packet.value = data_in;
    input_packet.valid = 1'b1;
    output_packet.value = 8'h00;
    output_packet.valid = 1'b0;
    error_flag = 1'b0;
    case (current_op)
      OP_NOP: begin
        output_packet.value = input_packet.value;
        output_packet.valid = input_packet.valid;
      end
      OP_ADD: begin
        output_packet.value = input_packet.value + 8'h01;
        output_packet.valid = input_packet.valid;
      end
      OP_SUB: begin
        output_packet.value = input_packet.value - 8'h01;
        output_packet.valid = input_packet.valid;
      end
      OP_MUL: begin
        output_packet.value = input_packet.value * 8'h02;
        output_packet.valid = input_packet.valid;
      end
      default: begin
        error_flag = 1'b1;
        output_packet.value = 8'hFF;
      end
    endcase
    processed_data_out = output_packet.value;
  end
endmodule
module FunctionAndTaskDemo (
  input  logic [7:0] operand_a,
  input  logic [7:0] operand_b,
  input  logic [1:0] operation_code,
  output logic [7:0] func_result_out,
  output logic        task_completed_flag
);
  logic [7:0] task_internal_val;
  logic       task_active;
  function automatic logic [7:0] calculate_sum_or_diff(
    input logic [7:0] val1,
    input logic [7:0] val2,
    input logic       is_add
  );
    if (is_add) begin
      return val1 + val2;
    end else begin
      return val1 - val2;
    end
  endfunction
  task automatic process_operation(
    input  logic [7:0] val_a,
    input  logic [7:0] val_b,
    input  logic [1:0] op_code,
    output logic [7:0] task_out_val,
    output logic       task_status
  );
    task_out_val = 8'h00;
    task_status = 1'b0;
    unique case (op_code)
      2'b00: begin
        task_out_val = val_a & val_b;
      end
      2'b01: begin
        task_out_val = val_a | val_b;
      end
      2'b10: begin
        task_out_val = val_a ^ val_b;
      end
      2'b11: begin
        task_out_val = ~val_a;
      end
    endcase
    task_status = 1'b1;
  endtask
  always_comb begin
    func_result_out = calculate_sum_or_diff(operand_a, operand_b, (operation_code == 2'b00));
    process_operation(operand_a, operand_b, operation_code, task_internal_val, task_active);
    task_completed_flag = task_active;
  end
endmodule
module ArrayAndMemoryBlock (
  input  logic [7:0] addr,
  input  logic [7:0] write_data,
  input  logic       write_enable,
  input  logic       clk,
  input  logic       reset_n,
  output logic [7:0] read_data_out,
  output logic [7:0] array_sum_out
);
  logic [7:0] memory [0:255];
  logic [31:0] packed_vector_a;
  logic [3:0][7:0] packed_vector_b;
  always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      for (int i = 0; i < 256; i++) begin
        memory[i] <= 8'h00;
      end
    end else if (write_enable) begin
      memory[addr] <= write_data;
    end
  end
  assign read_data_out = memory[addr];
  always_comb begin
    packed_vector_a = {write_data, {3{8'h00}}};
    packed_vector_b = {4{write_data}};
    array_sum_out = 8'h00;
    for (int i = 0; i < 4; i++) begin
      array_sum_out = array_sum_out + packed_vector_b[i];
    end
  end
endmodule
module ClassDemo (
  input  logic       clk,
  input  logic       reset_n,
  input  logic [7:0] cmd_in,
  input  logic [7:0] data_in_class,
  output logic [7:0] data_out_class,
  output logic       status_flag
);
  class MyDataProcessor;
    randc logic [7:0] internal_data;
    logic [7:0] processed_data;
    logic       is_initialized;
    function new();
      is_initialized = 1'b0;
      internal_data = 8'hAA;
      processed_data = 8'h00;
    endfunction
    function void initialize();
      is_initialized = 1'b1;
      internal_data = 8'h55;
    endfunction
    function void process_command(input logic [7:0] command, input logic [7:0] input_val);
      if (is_initialized) begin
        case (command)
          8'h01: begin
            internal_data = input_val;
          end
          8'h02: begin
            internal_data = internal_data + input_val;
          end
          8'h03: begin
            processed_data = internal_data;
          end
          default: begin
          end
        endcase
      end
    endfunction
    function logic [7:0] get_processed_data();
      return processed_data;
    endfunction
    function logic get_status();
      return is_initialized;
    endfunction
  endclass : MyDataProcessor
  MyDataProcessor my_processor_handle;
  always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      my_processor_handle = null;
      data_out_class <= 8'h00;
      status_flag <= 1'b0;
    end else begin
      if (my_processor_handle == null) begin
        my_processor_handle = new();
        my_processor_handle.initialize();
      end
      my_processor_handle.process_command(cmd_in, data_in_class);
      data_out_class <= my_processor_handle.get_processed_data();
      status_flag <= my_processor_handle.get_status();
      void'(my_processor_handle.randomize() with {internal_data > 8'h10; internal_data < 8'hF0;});
    end
  end
endmodule
module GenerateBlockDemo #(
  parameter NUM_STAGES = 3,
  parameter DATA_WIDTH = 4
) (
  input  logic [DATA_WIDTH-1:0] input_val,
  input  logic                  control_en,
  output logic [DATA_WIDTH-1:0] output_val,
  output logic [NUM_STAGES-1:0] stage_active_flags
);
  logic [DATA_WIDTH-1:0] internal_pipeline [NUM_STAGES:0];
  genvar i;
  generate
    if (NUM_STAGES > 0) begin : gen_pipeline_exists
      for (i = 0; i < NUM_STAGES; i++) begin : gen_stage
        logic [DATA_WIDTH-1:0] current_stage_input;
        logic [DATA_WIDTH-1:0] current_stage_output;
        if (i == 0) begin
          assign current_stage_input = input_val;
        end else begin
          assign current_stage_input = internal_pipeline[i];
        end
        always_comb begin
          if (control_en) begin
            current_stage_output = current_stage_input + DATA_WIDTH'(1);
            stage_active_flags[i] = 1'b1;
          end else begin
            current_stage_output = current_stage_input;
            stage_active_flags[i] = 1'b0;
          end
        end
        assign internal_pipeline[i+1] = current_stage_output;
      end
    end else begin : gen_no_pipeline
      assign output_val = input_val;
      assign stage_active_flags = {NUM_STAGES{1'b0}};
    end
  endgenerate
  assign output_val = internal_pipeline[NUM_STAGES];
endmodule
module ComplexTypesAndArrays (
  input  logic [15:0] raw_input_data,
  input  logic [1:0]  selector,
  output logic [7:0]  processed_byte_out,
  output logic [1:0]  status_out
);
  typedef struct packed {
    logic [7:0] low_byte;
    logic [7:0] high_byte;
  } two_byte_data_t;
  two_byte_data_t data_buffer [0:3];
  typedef union packed {
    logic [15:0] word;
    struct packed {
      logic [7:0] byte1;
      logic [7:0] byte0;
    } bytes;
  } word_or_bytes_u;
  word_or_bytes_u current_union_val;
  typedef two_byte_data_t two_byte_array_t [2];
  two_byte_array_t my_fixed_array;
  logic [7:0] temp_processed_byte;
  logic [1:0] temp_status;
  always_comb begin
    current_union_val.word = raw_input_data;
    case (selector)
      2'b00: temp_processed_byte = current_union_val.bytes.byte0;
      2'b01: temp_processed_byte = current_union_val.bytes.byte1;
      2'b10: temp_processed_byte = current_union_val.word[7:0];
      2'b11: temp_processed_byte = current_union_val.word[15:8];
    endcase
    data_buffer[0].low_byte = raw_input_data[7:0];
    data_buffer[0].high_byte = raw_input_data[15:8];
    data_buffer[1].low_byte = raw_input_data[7:0] + 1;
    data_buffer[1].high_byte = raw_input_data[15:8] + 1;
    if (selector == 2'b00 || selector == 2'b01) begin
      temp_processed_byte = data_buffer[0].low_byte;
    end else begin
      temp_processed_byte = data_buffer[1].high_byte;
    end
    my_fixed_array[0] = {8'h11, 8'h22};
    my_fixed_array[1] = {8'h33, 8'h44};
    if (selector[0]) begin
      temp_processed_byte = my_fixed_array[0].low_byte;
    end else begin
      temp_processed_byte = my_fixed_array[1].high_byte;
    end
    temp_status = 2'b00;
    if (temp_processed_byte > 8'h80) begin
      temp_status[0] = 1'b1;
    end
    if (raw_input_data[15:0] == 16'hFFFF) begin
      temp_status[1] = 1'b1;
    end
    processed_byte_out = temp_processed_byte;
    status_out = temp_status;
  end
endmodule
