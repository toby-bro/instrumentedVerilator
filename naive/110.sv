module BasicCombinational (
  input  logic        i_sel,
  input  logic [7:0]  i_data_a,
  input  logic [7:0]  i_data_b,
  output logic [7:0]  o_result,
  output logic        o_overflow
);
  logic [7:0] intermediate_sum;
  logic       carry_out;
  assign {carry_out, intermediate_sum} = i_data_a + i_data_b;
  always_comb begin
    if (i_sel) begin
      o_result = i_data_a & i_data_b;
    end else begin
      o_result = i_data_a | i_data_b;
    end
    o_overflow = carry_out;
  end
endmodule
module SimpleSequential (
  input  logic        i_clk,
  input  logic        i_reset_n,
  input  logic [15:0] i_data_in,
  output logic [15:0] o_data_out
);
  logic [15:0] q_reg;
  always_ff @(posedge i_clk or negedge i_reset_n) begin
    if (!i_reset_n) begin
      q_reg <= 16'h0000;
    end else begin
      q_reg <= i_data_in;
    end
  end
  assign o_data_out = q_reg;
endmodule
module EnumStructHandler (
  input  logic [1:0]  i_operation_code,
  input  logic [31:0] i_operand1,
  input  logic [31:0] i_operand2,
  output logic [31:0] o_result,
  output logic        o_error
);
  typedef enum logic [1:0] {
    ADD = 2'b00,
    SUB = 2'b01,
    MUL = 2'b10,
    DIV = 2'b11
  } operation_e;
  typedef struct packed {
    logic [31:0] val1;
    logic [31:0] val2;
  } operands_s;
  operation_e current_op;
  operands_s  current_operands;
  logic [31:0] temp_result;
  logic        is_error;
  assign current_op = operation_e'(i_operation_code);
  assign current_operands.val1 = i_operand1;
  assign current_operands.val2 = i_operand2;
  always_comb begin
    temp_result = 32'h0;
    is_error = 1'b0;
    case (current_op)
      ADD: begin
        temp_result = current_operands.val1 + current_operands.val2;
      end
      SUB: begin
        temp_result = current_operands.val1 - current_operands.val2;
      end
      MUL: begin
        temp_result = current_operands.val1 * current_operands.val2;
      end
      DIV: begin
        if (current_operands.val2 == 32'h0) begin
          is_error = 1'b1;
          temp_result = 32'hFFFFFFFF;
        end else begin
          temp_result = current_operands.val1 / current_operands.val2;
        end
      end
      default: begin
        is_error = 1'b1;
      end
    endcase
  end
  assign o_result = temp_result;
  assign o_error = is_error;
endmodule
module DataMemory (
  input  logic        i_clk,
  input  logic        i_wr_en,
  input  logic        i_rd_en,
  input  logic [7:0]  i_addr,
  input  logic [31:0] i_data_in,
  output logic [31:0] o_data_out
);
  logic [31:0] mem [255:0];
  logic [31:0] read_data_reg;
  always_ff @(posedge i_clk) begin
    if (i_wr_en) begin
      mem[i_addr] <= i_data_in;
    end
  end
  always_ff @(posedge i_clk) begin
    if (i_rd_en) begin
      read_data_reg <= mem[i_addr];
    end else begin
      read_data_reg <= 32'h0;
    end
  end
  assign o_data_out = read_data_reg;
endmodule
module ClassProcessor (
  input  logic        i_clk,
  input  logic        i_enable,
  input  int          i_input_val,
  output int          o_output_val
);
  class MyDataProcessor;
    int data;
    function new(int initial_data);
      this.data = initial_data;
    endfunction
    function int process_data(int multiplier);
      return data * multiplier;
    endfunction
  endclass
  MyDataProcessor processor_handle;
  int processed_value_internal;
  logic initialized_flag;
  always_ff @(posedge i_clk) begin
    if (!initialized_flag) begin
      processor_handle = new(i_input_val);
      initialized_flag = 1'b1;
    end else if (i_enable) begin
      if (processor_handle == null) begin
        processor_handle = new(i_input_val);
      end
      processed_value_internal = processor_handle.process_data(2);
      processor_handle.data = i_input_val;
    end else begin
      processed_value_internal = 0;
    end
  end
  assign o_output_val = processed_value_internal;
endmodule
module ParameterizedShifter #(
  parameter DATA_WIDTH = 8,
  parameter SHIFT_MAX   = 4
) (
  input  logic [DATA_WIDTH-1:0] i_data,
  input  logic [$clog2(SHIFT_MAX+1)-1:0] i_shift_amt,
  output logic [DATA_WIDTH-1:0] o_shifted_left,
  output logic [DATA_WIDTH-1:0] o_shifted_right
);
  logic [$clog2(SHIFT_MAX+1)-1:0] actual_shift_amt_var;
  assign actual_shift_amt_var = (i_shift_amt > SHIFT_MAX) ? SHIFT_MAX : i_shift_amt;
  assign o_shifted_left  = i_data <<< actual_shift_amt_var;
  assign o_shifted_right = i_data >>> actual_shift_amt_var;
endmodule
module MathUnit (
  input  logic [7:0] i_operand_a,
  input  logic [7:0] i_operand_b,
  input  logic [1:0] i_op_sel,
  output logic [15:0] o_result,
  output logic        o_carry,
  output logic        o_zero_flag
);
  function automatic logic [8:0] add_with_carry (input logic [7:0] op1, input logic [7:0] op2);
    return {1'b0, op1} + {1'b0, op2};
  endfunction
  task automatic calculate_and_flag (
    input  logic [7:0] op1,
    input  logic [7:0] op2,
    input  logic [1:0] op_type,
    output logic [15:0] result,
    output logic        carry,
    output logic        zero_flag
  );
    logic [8:0] add_res;
    result = 16'h0;
    carry = 1'b0;
    zero_flag = 1'b0;
    case (op_type)
      2'b00: begin
        add_res = add_with_carry(op1, op2);
        result = add_res[7:0];
        carry = add_res[8];
      end
      2'b01: begin
        result = op1 - op2;
      end
      2'b10: begin
        result = op1 * op2;
      end
      2'b11: begin
        if (op2 == 8'h0) begin
          result = 16'hFFFF;
        end else begin
          result = op1 / op2;
        end
      end
    endcase
    if (result == 16'h0) begin
      zero_flag = 1'b1;
    end
  endtask
  logic [15:0] internal_result;
  logic internal_carry;
  logic internal_zero_flag;
  always_comb begin
    calculate_and_flag(i_operand_a, i_operand_b, i_op_sel,
                       internal_result, internal_carry, internal_zero_flag);
  end
  assign o_result = internal_result;
  assign o_carry = internal_carry;
  assign o_zero_flag = internal_zero_flag;
endmodule
module ComplexDataArray (
  input  logic        i_clk,
  input  logic        i_write_en,
  input  logic [3:0]  i_addr,
  input  logic [7:0]  i_data_val,
  input  logic [7:0]  i_status_val,
  output logic [7:0]  o_data_out,
  output logic [7:0]  o_status_out
);
  typedef struct packed {
    logic [7:0] data;
    logic [7:0] status;
  } entry_s;
  entry_s entries [16];
  always_ff @(posedge i_clk) begin
    if (i_write_en) begin
      entries[i_addr].data   <= i_data_val;
      entries[i_addr].status <= i_status_val;
    end
  end
  assign o_data_out   = entries[i_addr].data;
  assign o_status_out = entries[i_addr].status;
endmodule
