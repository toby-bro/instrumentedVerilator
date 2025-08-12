module BasicLogic (
  input logic           clk_i,
  input logic           rst_ni,
  input logic [7:0]     data_in_i,
  output logic [7:0]    data_out_o
);
  parameter WIDTH = 8;
  parameter START_VALUE = 8'hAA;
  logic [WIDTH-1:0] internal_reg;
  logic [WIDTH-1:0] comb_val;
  assign comb_val = data_in_i + START_VALUE;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      internal_reg <= 0;
    end else begin
      internal_reg <= comb_val;
    end
  end
  assign data_out_o = internal_reg;
endmodule
module DataTypeModule (
  input logic                 control_i,
  input logic [1:0]           state_sel_i,
  input byte                  val_byte_i,
  output logic [15:0]         output_word_o
);
  typedef enum {IDLE, CONFIG, RUNNING, STOPPED} FSM_STATE_E;
  FSM_STATE_E current_state;
  typedef struct packed {
    logic [7:0]   addr;
    logic [7:0]   data;
  } ConfigPacket_t;
  ConfigPacket_t config_reg;
  typedef union packed {
    logic [15:0]  word;
    struct packed {
      logic [7:0] lower;
      logic [7:0] upper;
    } halves;
  } WordUnion_t;
  WordUnion_t u_data;
  logic [3:0] lookup_table [4];
  int         internal_int_array [2][3];
  always_comb begin
    case (state_sel_i)
      2'b00: current_state = IDLE;
      2'b01: current_state = CONFIG;
      2'b10: current_state = RUNNING;
      default: current_state = STOPPED;
    endcase
    if (control_i) begin
      config_reg.addr = val_byte_i;
      config_reg.data = ~val_byte_i;
    end else begin
      config_reg.addr = 0;
      config_reg.data = 0;
    end
    u_data.word = {val_byte_i, val_byte_i};
    if (current_state == RUNNING) begin
      output_word_o = u_data.halves.lower + u_data.halves.upper;
    end else begin
      output_word_o = config_reg.addr + config_reg.data;
    end
    lookup_table[0] = 4'b0001;
    lookup_table[1] = 4'b0010;
    lookup_table[2] = 4'b0100;
    lookup_table[3] = 4'b1000;
    for (int i = 0; i < 2; i++) begin
      for (int j = 0; j < 3; j++) begin
        internal_int_array[i][j] = i * 10 + j;
      end
    end
  end
endmodule
module ProceduralLogic (
  input logic [15:0]    input_a_i,
  input logic [15:0]    input_b_i,
  input logic           operation_sel_i,
  output logic [15:0]   result_o
);
  logic [15:0] temp_result;
  function automatic logic [15:0] calculate_sum (
    input logic [15:0] arg1,
    input logic [15:0] arg2
  );
    return arg1 + arg2;
  endfunction
  task automatic perform_operation (
    input logic [15:0] in1,
    input logic [15:0] in2,
    input logic        op_select,
    output logic [15:0] out_val
  );
    if (op_select) begin
      out_val = in1 - in2;
    end else begin
      out_val = calculate_sum(in1, in2);
    end
  endtask
  always_comb begin
    perform_operation(input_a_i, input_b_i, operation_sel_i, temp_result);
    if (temp_result > 100) begin
      result_o = temp_result * 2;
    end else if (temp_result < 50) begin
      result_o = temp_result / 2;
    end else begin
      result_o = temp_result;
    end
    case (temp_result[1:0])
      2'b00: result_o = result_o + 1;
      2'b01: result_o = result_o + 2;
      2'b10: result_o = result_o + 3;
      default: result_o = result_o + 4;
    endcase
  end
endmodule
module ClassModule (
  input logic       init_en_i,
  input logic [7:0] data_in_i,
  output logic [7:0] proc_data_o,
  output logic      status_o
);
  class MyDataProcessor;
    rand bit [7:0] internal_data;
    local int processed_count;
    function new();
      processed_count = 0;
      internal_data = 0;
    endfunction
    function void process(bit [7:0] in_val);
      internal_data = in_val * 2;
      processed_count++;
    endfunction
    function bit [7:0] get_data();
      return internal_data;
    endfunction
    function bit get_status();
      return (processed_count > 0);
    endfunction
  endclass
  MyDataProcessor processor_h;
  always_comb begin
    if (init_en_i && processor_h == null) begin
      processor_h = new();
    end
    if (processor_h != null) begin
      processor_h.process(data_in_i);
      proc_data_o = processor_h.get_data();
      status_o = processor_h.get_status();
    end else begin
      proc_data_o = 0;
      status_o = 0;
    end
  end
endmodule
interface simple_interface;
  logic clk;
  logic rst_n;
  logic [15:0]  data;
  modport master (output data, input clk, input rst_n);
  modport slave (input data, input clk, input rst_n);
endinterface
module GenerateModule (
  input logic           clk_i,
  input logic           rst_ni,
  input logic [3:0]     sel_i,
  input logic [15:0]    val_in_i,
  output logic [15:0]   sum_o
);
  simple_interface if_inst ();
  assign if_inst.clk = clk_i;
  assign if_inst.rst_n = rst_ni;
  logic [15:0] selected_internal_value;
  logic [15:0] generated_data [4];
  generate
    genvar i;
    for (i = 0; i < 4; i++) begin : gen_calc_block
      assign generated_data[i] = val_in_i + (i * 100);
    end
  endgenerate
  always_comb begin
    selected_internal_value = val_in_i;
    if (sel_i < 4) begin
      selected_internal_value = generated_data[sel_i];
    end
  end
  generate
    if (1) begin : always_included_block
      assign if_inst.data = selected_internal_value + 1;
    end else begin : never_included_block
      logic [7:0] unused_var = 8'hAA;
    end
  endgenerate
  assign sum_o = if_inst.data;
endmodule
module AdvArrayCastModule (
  input logic         read_en_i,
  input logic [7:0]   key_in_i,
  input int           value_in_i,
  input real          real_val_i,
  output int          data_out_o,
  output logic [7:0]  key_out_o
);
  int assoc_map [byte];
  int data_queue [$];
  logic [31:0] combined_val;
  int          int_val_from_real;
  real         real_result;
  always_comb begin
    if (read_en_i) begin
      if (assoc_map.exists(key_in_i)) begin
        data_out_o = assoc_map[key_in_i];
      end else begin
        data_out_o = -1;
      end
      key_out_o = key_in_i;
    end else begin
      assoc_map[key_in_i] = value_in_i;
      data_out_o = 0;
      key_out_o = 0;
    end
    data_queue.push_back(value_in_i);
    if (data_queue.size() > 5) begin
      void'(data_queue.pop_front());
    end
    combined_val = 32'(value_in_i);
    int_val_from_real = int'(real_val_i);
    real_result = real'(value_in_i) * real_val_i;
    if (!read_en_i) begin
      data_out_o = value_in_i;
      key_out_o = 8'(value_in_i);
    end
  end
endmodule
module OperatorModule (
  input logic signed [31:0] input_sint_i,
  input logic [31:0]        input_uint_i,
  input logic [3:0]         control_opcode_i,
  output logic signed [31:0] result_sint_o,
  output logic [31:0]       result_uint_o
);
  localparam MAX_VAL = 100;
  localparam MIN_VAL = -50;
  logic signed [31:0] internal_signed;
  logic [31:0]        internal_unsigned;
  always_comb begin
    internal_signed = input_sint_i + input_uint_i;
    internal_unsigned = input_uint_i * 2 - 1;
    if (internal_signed > MAX_VAL) begin
      internal_signed = MAX_VAL;
    end else if (internal_signed < MIN_VAL) begin
      internal_signed = MIN_VAL;
    end
    if (control_opcode_i[0] && control_opcode_i[1]) begin
      internal_unsigned = internal_unsigned | 1;
    end else if (control_opcode_i[2] || control_opcode_i[3]) begin
      internal_unsigned = internal_unsigned & (~(1));
    end else begin
      internal_unsigned = internal_unsigned ^ 1;
    end
    result_sint_o = internal_signed;
    result_uint_o = internal_unsigned;
    case (control_opcode_i)
      4'b0001: begin
        result_sint_o = internal_signed << 2;
        result_uint_o = internal_unsigned >> 1;
      end
      4'b0010: begin
        result_sint_o = internal_signed >>> 1;
        result_uint_o = internal_unsigned <<< 2;
      end
      4'b0100: begin
        result_sint_o = ~internal_signed;
        result_uint_o = ~internal_unsigned;
      end
      4'b1000: begin
        result_sint_o = internal_signed & input_uint_i;
        result_uint_o = internal_unsigned | input_sint_i;
      end
      default: begin
      end
    endcase
    result_sint_o = (input_sint_i % 2 == 0) ? result_sint_o + 10 : result_sint_o - 10;
  end
endmodule
