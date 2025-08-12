module DataPathLogic (
  input logic [7:0] in_data_a,
  input logic [7:0] in_data_b,
  input bit         in_sel,
  output logic [7:0] out_result,
  output int        out_sum_int,
  output real       out_avg_real
);
  logic [7:0] temp_mux_result;
  int         sum_internal;
  real        average_internal;
  assign out_result = temp_mux_result;
  always_comb begin
    if (in_sel) begin
      temp_mux_result = in_data_a + in_data_b;
    end else begin
      temp_mux_result = in_data_a - in_data_b;
    end
    sum_internal = in_data_a + in_data_b + temp_mux_result;
    average_internal = $itor(sum_internal) / 3.0;
    out_sum_int = sum_internal;
    out_avg_real = average_internal;
  end
endmodule
module MemoryUnit (
  input logic        clk,
  input logic        reset_n,
  input logic [3:0]  addr_in,
  input logic [7:0]  data_in,
  input logic        write_en,
  output logic [7:0] data_out
);
  logic [7:0] mem_fixed [0:15];
  logic [7:0] mem_dynamic[];
  logic [7:0] mem_associative [int];
  logic [7:0] q_data_out;
  always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      for (int i = 0; i < 16; i++) begin
        mem_fixed[i] <= '0;
      end
      q_data_out <= '0;
      mem_dynamic = new[0];
      mem_associative.delete();
    end else begin
      if (write_en) begin
        mem_fixed[addr_in] <= data_in;
      end
      q_data_out <= mem_fixed[addr_in];
      if (mem_dynamic.size() == 0) begin
        mem_dynamic = new[2];
        mem_dynamic[0] = 8'hAA;
        mem_dynamic[1] = 8'hBB;
      end
      mem_associative[10] = 8'hCC;
      if (mem_associative.exists(5)) begin
        mem_associative[5] = 8'hDD;
      end else begin
        mem_associative[5] = 8'hEE;
      end
    end
  end
  assign data_out = q_data_out;
endmodule
module DataStructures (
  input logic [1:0] operation_sel,
  input int         input_val1,
  input int         input_val2,
  output int        output_calc_result
);
  typedef struct packed {
    logic [7:0] field_a;
    logic [7:0] field_b;
  } my_packed_struct_t;
  typedef struct {
    int   val1;
    int   val2;
    logic flag;
  } my_unpacked_struct_t;
  typedef enum logic [1:0] {
    OP_ADD    = 2'b00,
    OP_SUB    = 2'b01,
    OP_MUL    = 2'b10,
    OP_INVALID = 2'b11
  } operation_e;
  typedef union {
    int     i_val;
    logic [31:0] l_val;
    real    r_val;
  } my_union_t;
  my_unpacked_struct_t  config_data;
  my_packed_struct_t    packed_data_instance;
  operation_e           current_op;
  my_union_t            data_union;
  always_comb begin
    current_op = operation_e'(operation_sel);
    config_data.val1 = input_val1;
    config_data.val2 = input_val2;
    config_data.flag = (input_val1 > input_val2);
    packed_data_instance.field_a = 8'hF0;
    packed_data_instance.field_b = 8'h0F;
    data_union.i_val = input_val1 + input_val2;
    case (current_op)
      OP_ADD:
        output_calc_result = config_data.val1 + config_data.val2;
      OP_SUB:
        output_calc_result = config_data.val1 - config_data.val2;
      OP_MUL:
        output_calc_result = config_data.val1 * config_data.val2;
      default:
        output_calc_result = 0;
    endcase
  end
endmodule
module FunctionTaskExample (
  input int in_val_a,
  input int in_val_b,
  input bit enable_task,
  output int out_func_result,
  output int out_task_result
);
  int func_local_result;
  int task_local_result;
  function automatic int calculate_sum_diff(int a, int b);
    if (a > b) begin
      return a + b;
    end else begin
      return a - b;
    end
  endfunction
  task automatic perform_operation(input int val1, input int val2, output int res);
    if (enable_task) begin
      res = val1 * val2;
    end else begin
      res = val1 / val2;
    end
  endtask
  always_comb begin
    func_local_result = calculate_sum_diff(in_val_a, in_val_b);
    out_func_result = func_local_result;
    task_local_result = 0;
    perform_operation(in_val_a, in_val_b, task_local_result);
    out_task_result = task_local_result;
  end
endmodule
module ClassExample (
  input logic clk_i,
  input logic rst_ni,
  input int   set_value_i,
  input bit   op_read_i,
  output int  read_value_o
);
  class MyDataProcessor;
    int data_storage;
    function new();
      data_storage = 0;
    endfunction
    function void set_data(int val);
      data_storage = val;
    endfunction
    function int get_data();
      return data_storage;
    endfunction
    function int process_data(int multiplier);
      return data_storage * multiplier;
    endfunction
  endclass
  MyDataProcessor my_processor_h;
  int current_read_value;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      if (my_processor_h != null) begin
        my_processor_h = null;
      end
      my_processor_h = new();
      current_read_value <= 0;
    end else begin
      if (my_processor_h == null) begin
        my_processor_h = new();
      end
      my_processor_h.set_data(set_value_i);
      if (op_read_i) begin
        current_read_value <= my_processor_h.get_data();
      end else begin
        current_read_value <= my_processor_h.process_data(2);
      end
    end
  end
  assign read_value_o = current_read_value;
endmodule
module ParamLogic #(
  parameter DATA_WIDTH = 8,
  parameter NUM_STAGES = 4
) (
  input logic [DATA_WIDTH-1:0]  input_val,
  input logic                   control_bit,
  output logic [DATA_WIDTH-1:0] output_processed
);
  localparam MASK_VAL = (1 << (DATA_WIDTH / 2)) - 1;
  logic [DATA_WIDTH-1:0] temp_val_stage1;
  logic [DATA_WIDTH-1:0] temp_val_stage2;
  logic [DATA_WIDTH-1:0] temp_val_stage3;
  logic [DATA_WIDTH-1:0] pipeline_regs [NUM_STAGES-1:0];
  always_comb begin
    temp_val_stage1 = input_val ^ MASK_VAL;
    temp_val_stage2 = temp_val_stage1 << 1;
    temp_val_stage3 = temp_val_stage2 | {DATA_WIDTH{control_bit}};
    if (control_bit) begin
      output_processed = temp_val_stage3;
    end else begin
      output_processed = {{(DATA_WIDTH/2){1'b0}}, input_val[DATA_WIDTH-1:DATA_WIDTH/2]};
    end
  end
  genvar i;
  generate
    for (i = 0; i < NUM_STAGES; i++) begin : gen_pipe_logic
      logic dummy_q;
      always_ff @(posedge input_val[0]) begin
        dummy_q <= input_val[i % DATA_WIDTH];
      end
    end
  endgenerate
endmodule
module AssertCover (
  input logic clk,
  input logic reset_n,
  input logic req_i,
  input logic grant_i,
  input logic data_valid_i,
  output logic out_sig
);
  logic [7:0] data_val_internal;
  always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      out_sig <= 1'b0;
      data_val_internal <= '0;
    end else begin
      out_sig <= req_i & grant_i;
      data_val_internal <= data_valid_i ? 8'hAA : 8'hBB;
    end
  end
  assert property (@(posedge clk) disable iff (!reset_n) req_i |-> ##1 grant_i);
  assert property (@(posedge clk) (req_i && !grant_i) |-> data_val_internal == 8'hAA);
  cover property (@(posedge clk) req_i && grant_i);
  cover property (@(posedge clk) !req_i && grant_i);
  covergroup my_covergroup @(posedge clk);
    option.per_instance = 1;
    a_cp: coverpoint req_i;
    b_cp: coverpoint grant_i;
    cross_ab: cross a_cp, b_cp;
  endgroup
  my_covergroup cg_inst = new();
endmodule
module LoopGenerateLogic (
  input logic [7:0] input_vec [3:0],
  input logic       control_bit_i,
  output logic [7:0] output_agg,
  output logic [7:0] output_vec [3:0]
);
  logic [7:0] sum_temp;
  logic [7:0] element_processed [3:0];
  always_comb begin
    sum_temp = '0;
    for (int k = 0; k < 4; k++) begin
      if (control_bit_i) begin
        element_processed[k] = input_vec[k] + 1;
      end else begin
        element_processed[k] = input_vec[k] - 1;
      end
      sum_temp = sum_temp + element_processed[k];
    end
    output_agg = sum_temp;
    for (int k = 0; k < 4; k++) begin
      output_vec[k] = element_processed[k];
    end
  end
  genvar j;
  generate
    for (j = 0; j < 2; j++) begin : gen_half_logic
      logic [7:0] inner_logic_val;
      assign inner_logic_val = input_vec[j] ^ 8'hFF;
    end
  endgenerate
endmodule
