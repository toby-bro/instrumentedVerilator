module SimpleCombinationalLogic (
  input  logic a_in,
  input  logic b_in,
  output logic xor_out,
  output logic and_out
);
  assign xor_out = a_in ^ b_in;
  always_comb begin
    and_out = a_in & b_in;
  end
endmodule
module SequentialRegister #(
  parameter WIDTH = 8
) (
  input  logic              clk,
  input  logic              rst_n,
  input  logic [WIDTH-1:0]  data_in,
  output logic [WIDTH-1:0]  data_out
);
  logic [WIDTH-1:0] internal_reg;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      internal_reg <= '0;
    end else begin
      internal_reg <= data_in;
    end
  end
  assign data_out = internal_reg;
endmodule
module EnumCaseProcessor (
  input  logic [1:0] op_sel,
  input  logic [7:0] val1,
  input  logic [7:0] val2,
  output logic [7:0] result_val
);
  typedef enum logic [1:0] {
    OP_ADD = 2'b00,
    OP_SUB = 2'b01,
    OP_MUL = 2'b10,
    OP_DIV = 2'b11
  } Operation_e;
  Operation_e current_op;
  always_comb begin
    current_op = Operation_e'(op_sel);
    case (current_op)
      OP_ADD: result_val = val1 + val2;
      OP_SUB: result_val = val1 - val2;
      OP_MUL: result_val = val1 * val2;
      OP_DIV: begin
                if (val2 != 0) result_val = val1 / val2;
                else result_val = 'X;
              end
      default: result_val = '0;
    endcase
  end
endmodule
module StructAndArrayHandler (
  input  logic                 enable,
  input  logic [7:0]           data_input_array [4],
  output struct packed {
    logic [3:0] id;
    logic [7:0] value;
  }                            output_data
);
  typedef struct {
    logic [2:0]  tag;
    logic [15:0] payload;
  } PacketHeader_t;
  PacketHeader_t packet_headers[2];
  struct packed {
    logic [3:0] status;
    logic [7:0] checksum;
  } local_status_info;
  always_comb begin
    if (enable) begin
      output_data.id    = 4'hA;
      output_data.value = data_input_array[0] + data_input_array[1];
      local_status_info = '{status: 4'hF, checksum: data_input_array[2]};
      packet_headers[0] = '{tag: 3'b001, payload: 16'h1234};
      packet_headers[1] = '{tag: 3'b010, payload: 16'hABCD};
    end else begin
      output_data = '{id: 4'h0, value: 8'h0};
      local_status_info = '0;
      packet_headers[0].tag = '0;
      packet_headers[0].payload = '0;
      packet_headers[1].tag = '0;
      packet_headers[1].payload = '0;
    end
  end
endmodule
module ClassBasedLogic (
  input  logic clk,
  input  logic reset,
  input  int   input_val_a,
  input  int   input_val_b,
  output int   output_sum
);
  class MySimpleCalculator;
    rand int member_sum;
    int    member_product;
    function new();
      member_sum     = 0;
      member_product = 1;
    endfunction
    function void calculate_sum(int a, int b);
      member_sum = a + b;
    endfunction
    function void calculate_product(int a, int b);
      member_product = a * b;
    endfunction
  endclass
  MySimpleCalculator calc_handle;
  always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
      calc_handle = null;
      output_sum <= 0;
    end else begin
      if (calc_handle == null) begin
        calc_handle = new();
      end
      calc_handle.calculate_sum(input_val_a, input_val_b);
      calc_handle.calculate_product(input_val_a, input_val_b);
      output_sum <= calc_handle.member_sum;
    end
  end
endmodule
module FunctionAndTaskModule (
  input  logic [7:0] val1_in,
  input  logic [7:0] val2_in,
  input  logic       op_sel_func,
  input  logic       op_sel_task,
  output logic [7:0] func_result,
  output logic [7:0] task_result
);
  function automatic logic [7:0] perform_arithmetic_func(logic [7:0] a, logic [7:0] b, logic subtract);
    if (subtract) begin
      return a - b;
    end else begin
      return a + b;
    end
  endfunction
  task automatic perform_arithmetic_task(input logic [7:0] a, input logic [7:0] b, input logic divide, output logic [7:0] res);
    if (divide) begin
      if (b != 0) res = a / b;
      else res = 'X;
    end else begin
      res = a * b;
    end
  endtask
  always_comb begin
    func_result = perform_arithmetic_func(val1_in, val2_in, op_sel_func);
    perform_arithmetic_task(val1_in, val2_in, op_sel_task, task_result);
  end
endmodule
module GenerateBlockLogic #(
  parameter NUM_STAGES = 4
) (
  input  logic [7:0]           data_in,
  input  logic [NUM_STAGES-1:0] enable_stages,
  output logic [7:0]           processed_data
);
  logic [7:0] stage_output [NUM_STAGES];
  assign stage_output[0] = data_in;
  genvar i;
  generate
    for (i = 1; i < NUM_STAGES; i++) begin : stage_processing_loop
      always_comb begin
        if (enable_stages[i]) begin
          stage_output[i] = stage_output[i-1] + i;
        end else begin
          stage_output[i] = stage_output[i-1];
        end
      end
    end
  endgenerate
  assign processed_data = stage_output[NUM_STAGES-1];
endmodule
module MemorySlaveModule #(
  parameter ADDR_WIDTH = 16,
  parameter DATA_WIDTH = 32
) (
  input  logic                   clk,
  input  logic                   reset_n,
  input  logic                   read_en,
  input  logic [ADDR_WIDTH-1:0]  addr,
  input  logic                   write_en,
  input  logic [DATA_WIDTH-1:0]  write_data,
  input  logic [DATA_WIDTH/8-1:0] byte_en,
  output logic [DATA_WIDTH-1:0]  read_data,
  output logic                   ready
);
  logic [DATA_WIDTH-1:0] internal_memory [1 << ADDR_WIDTH];
  always_comb begin
    ready = 1'b1;
    if (read_en) begin
      read_data = internal_memory[addr];
    end else begin
      read_data = '0;
    end
  end
  always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
    end else if (write_en) begin
      for (int i = 0; i < DATA_WIDTH/8; i++) begin
        if (byte_en[i]) begin
          internal_memory[addr][(i*8)+:8] <= write_data[(i*8)+:8];
        end
      end
    end
  end
endmodule
