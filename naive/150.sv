typedef struct packed {
  logic [7:0] data;
  logic       valid;
} my_packet_t;
class DataProcessor;
  rand int m_internal_value;
  logic [15:0] m_processed_sum;
  function new();
    m_internal_value = 0;
    m_processed_sum = 0;
  endfunction
  function my_packet_t process(my_packet_t input_packet);
    automatic my_packet_t output_packet;
    if (input_packet.valid) begin
      m_internal_value = m_internal_value + input_packet.data;
      m_processed_sum = m_processed_sum + input_packet.data;
      output_packet.data = input_packet.data * 2;
      output_packet.valid = 1'b1;
    end else begin
      output_packet.data = '0;
      output_packet.valid = 1'b0;
    end
    return output_packet;
  endfunction
  function logic [15:0] get_sum();
    return m_processed_sum;
  endfunction
endclass
module CombinationalAndSequentialExample (
  input  logic        clk,
  input  logic        reset_n,
  input  logic [7:0]  input_a,
  input  logic [7:0]  input_b,
  output logic [8:0]  sum_out,
  output logic [7:0]  reg_out
);
  logic [7:0] next_reg_val;
  logic       and_result;
  logic       or_result;
  assign and_result = input_a[0] && input_b[0];
  assign or_result = input_a[1] || input_b[1];
  always_comb begin
    sum_out = input_a + input_b;
    if (and_result) begin
      next_reg_val = input_a;
    end else if (or_result) begin
      next_reg_val = input_b;
    end else begin
      next_reg_val = 8'd0;
    end
  end
  always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      reg_out <= '0;
    end else begin
      reg_out <= next_reg_val;
    end
  end
endmodule
module ParameterizedMemoryController #(
  parameter ADDR_WIDTH = 4,
  parameter DATA_WIDTH = 8
) (
  input  logic                   clk,
  input  logic                   reset_n,
  input  logic                   write_en,
  input  logic                   read_en,
  input  logic [ADDR_WIDTH-1:0]  addr_in,
  input  logic [DATA_WIDTH-1:0]  data_in,
  output logic [DATA_WIDTH-1:0]  data_out,
  output logic                   mem_busy
);
  localparam MEM_DEPTH = 1 << ADDR_WIDTH;
  logic [DATA_WIDTH-1:0] memory [MEM_DEPTH-1:0];
  typedef enum logic [1:0] { IDLE, WRITE, READ, BUSY } fsm_state_t;
  fsm_state_t current_state, next_state;
  logic [DATA_WIDTH-1:0] internal_data_read;
  logic                  internal_mem_busy;
  always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      current_state <= IDLE;
    end else begin
      current_state <= next_state;
    end
  end
  always_comb begin
    next_state = current_state;
    internal_data_read = '0;
    internal_mem_busy = 1'b0;
    unique case (current_state)
      IDLE: begin
        if (write_en) begin
          next_state = WRITE;
          internal_mem_busy = 1'b1;
        end else if (read_en) begin
          next_state = READ;
          internal_mem_busy = 1'b1;
        end
      end
      WRITE: begin
        next_state = IDLE;
      end
      READ: begin
        internal_data_read = memory[addr_in];
        next_state = IDLE;
      end
      default: begin
        next_state = IDLE;
      end
    endcase
  end
  always_ff @(posedge clk) begin
    if (current_state == WRITE) begin
      memory[addr_in] <= data_in;
    end
  end
  assign data_out = internal_data_read;
  assign mem_busy = internal_mem_busy;
endmodule
module FunctionAndTaskUser (
  input  logic [7:0] operand1,
  input  logic [7:0] operand2,
  input  logic       enable_calc,
  output logic [15:0] sum_out,
  output logic [15:0] product_out
);
  logic [15:0] internal_sum;
  logic [15:0] internal_product;
  function automatic logic [15:0] calculate_sum(logic [7:0] a, logic [7:0] b);
    return a + b;
  endfunction
  task automatic calculate_product(input logic [7:0] a, input logic [7:0] b, output logic [15:0] result);
    result = a * b;
  endtask
  always_comb begin
    if (enable_calc) begin
      internal_sum = calculate_sum(operand1, operand2);
      calculate_product(operand1, operand2, internal_product);
    end else begin
      internal_sum = '0;
      internal_product = '0;
    end
  end
  assign sum_out = internal_sum;
  assign product_out = internal_product;
endmodule
module GenerateBlockBasedLogic #(
  parameter NUM_SLICES = 2,
  parameter USE_INVERTER = 1
) (
  input  logic [NUM_SLICES-1:0][7:0] input_data_array,
  output logic [NUM_SLICES-1:0][7:0] output_data_array,
  input  logic                       master_enable,
  output logic                       all_enabled_and_sum
);
  logic [NUM_SLICES-1:0] enabled_signals;
  logic [7:0] total_sum_elements;
  genvar i;
  generate
    for (i = 0; i < NUM_SLICES; i = i + 1) begin : slice_gen
      if (USE_INVERTER) begin : inverter_block
        assign output_data_array[i] = master_enable ? ~input_data_array[i] : '0;
      end else begin : buffer_block
        assign output_data_array[i] = master_enable ? input_data_array[i] : '0;
      end
      assign enabled_signals[i] = (input_data_array[i] > 8'd10);
    end
  endgenerate
  always_comb begin
    int loop_idx;
    total_sum_elements = '0;
    for (loop_idx = 0; loop_idx < NUM_SLICES; loop_idx = loop_idx + 1) begin
      total_sum_elements = total_sum_elements + input_data_array[loop_idx];
    end
    all_enabled_and_sum = &enabled_signals && (total_sum_elements > 8'd100);
  end
endmodule
module DataStructureAndClassHandler (
  input  logic clk,
  input  logic rst_n,
  input  my_packet_t in_data_packet,
  input  logic write_to_history,
  output my_packet_t out_data_packet,
  output logic [15:0] total_processed_sum,
  output logic [7:0] history_data_out
);
  DataProcessor processor_inst;
  my_packet_t   next_out_data_packet;
  logic [15:0]  next_total_processed_sum;
  my_packet_t history_buffer [3:0];
  logic [1:0] history_ptr;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      if (processor_inst != null) begin
        processor_inst = null;
      end
      next_out_data_packet = '{data:'0, valid:1'b0};
      next_total_processed_sum = '0;
      history_ptr = '0;
      foreach (history_buffer[i]) history_buffer[i] = '{data:'0, valid:1'b0};
    end else begin
      if (processor_inst == null) begin
        processor_inst = new();
      end
      next_out_data_packet = processor_inst.process(in_data_packet);
      next_total_processed_sum = processor_inst.get_sum();
      if (write_to_history && in_data_packet.valid) begin
        history_buffer[history_ptr] = in_data_packet;
        history_ptr = (history_ptr + 1) % 4;
      end
    end
  end
  assign out_data_packet = next_out_data_packet;
  assign total_processed_sum = next_total_processed_sum;
  assign history_data_out = history_buffer[history_ptr].data;
endmodule
module AssertionAndTypeSystem (
  input  logic        clk,
  input  logic        in_enable,
  input  byte         byte_data_in,
  input  int unsigned int_data_in,
  input  logic [3:0]  vector_in,
  output logic [7:0]  byte_data_out,
  output int unsigned int_data_out,
  output logic [3:0]  vector_out,
  output logic        assertion_failed_flag
);
  logic [7:0]  byte_reg;
  int unsigned int_reg;
  logic [3:0]  vector_reg;
  logic        any_assertion_failed;
  always_ff @(posedge clk) begin
    byte_reg <= byte_data_in;
    int_reg <= int_data_in;
    vector_reg <= vector_in;
    any_assertion_failed = 1'b0;
    assert (byte_data_in != 8'hFF) else begin
      $error("AssertionFailed: byte_data_in should not be 0xFF!");
      any_assertion_failed = 1'b1;
    end
    if (in_enable) begin
      assert (int_data_in > 100) else begin
        $warning("AssertionWarning: int_data_in <= 100 when enabled!");
        any_assertion_failed = 1'b1;
      end
    end
    if (vector_in != 4'b0) begin
      automatic int log_val = $clog2(vector_in);
      assert (log_val < 4) else begin
        $error("AssertionFailed: clog2 of vector_in too large!");
        any_assertion_failed = 1'b1;
      end
      byte_reg <= byte'(vector_in);
    end else begin
        byte_reg <= 8'h00;
    end
  end
  assign byte_data_out = byte_reg;
  assign int_data_out = int_reg;
  assign vector_out = vector_reg;
  assign assertion_failed_flag = any_assertion_failed;
endmodule
