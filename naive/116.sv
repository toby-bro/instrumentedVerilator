module CombinationalLogic (
  input logic [7:0] in_data,
  input bit [1:0] in_op_code,
  output logic [7:0] out_result,
  output bit out_overflow
);
  parameter DATA_WIDTH = 8;
  localparam MAX_VALUE = 2**DATA_WIDTH - 1;
  typedef enum logic [1:0] {
    OP_ADD = 2'b00,
    OP_SUB = 2'b01,
    OP_MUL = 2'b10,
    OP_DIV = 2'b11
  } operation_e;
  operation_e current_op;
  logic [DATA_WIDTH-1:0] temp_result;
  logic overflow_flag;
  always_comb begin
    temp_result = 0;
    overflow_flag = 1'b0;
    current_op = operation_e'(in_op_code);
    if (in_data == 8'hFF) begin
      temp_result = in_data + 1;
      overflow_flag = 1'b1;
    end else begin
      case (current_op)
        OP_ADD: begin
          temp_result = in_data + 5;
          if (in_data > (MAX_VALUE - 5))
            overflow_flag = 1'b1;
        end
        OP_SUB: begin
          temp_result = in_data - 2;
          if (in_data < 2)
            overflow_flag = 1'b1;
        end
        OP_MUL: begin
          temp_result = in_data * 3;
          if (in_data > (MAX_VALUE / 3))
            overflow_flag = 1'b1;
        end
        OP_DIV: begin
          if (in_data == 0) begin
            temp_result = 0;
            overflow_flag = 1'b1;
          end else begin
            temp_result = in_data / 2;
          end
        end
        default: begin
          temp_result = 0;
          overflow_flag = 1'b1;
        end
      endcase
    end
    out_result = temp_result;
    out_overflow = overflow_flag;
  end
endmodule
module SequentialProcessor (
  input logic clk,
  input logic rst_n,
  input logic [15:0] in_value,
  input bit enable_op,
  output logic [15:0] out_processed_value,
  output logic [7:0] out_status
);
  typedef struct packed {
    logic [7:0] command;
    logic [7:0] data;
  } instruction_s;
  typedef union packed {
    instruction_s instr;
    logic [15:0] raw_word;
  } word_u;
  instruction_s current_instr;
  word_u input_word_union;
  logic [15:0] register_a;
  logic [15:0] register_b [0:3];
  logic [7:0] status_flags;
  logic [1:0] counter;
  function automatic logic [15:0] process_instruction(instruction_s instr, logic [15:0] operand);
    logic [15:0] result_val;
    result_val = operand;
    case (instr.command)
      8'h01: result_val = operand + instr.data;
      8'h02: result_val = operand - instr.data;
      8'h03: result_val = operand * instr.data;
      8'h04: result_val = (instr.data != 0) ? (operand / instr.data) : 0;
      default: result_val = operand;
    endcase
    return result_val;
  endfunction
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      register_a <= 0;
      for (int i = 0; i < 4; i++) begin
        register_b[i] <= 0;
      end
      status_flags <= 0;
      counter <= 0;
      out_processed_value <= 0;
      out_status <= 0;
    end else if (enable_op) begin
      input_word_union.raw_word = in_value;
      current_instr = input_word_union.instr;
      register_a <= process_instruction(current_instr, register_a);
      register_b[counter] <= current_instr.data;
      counter <= (counter == 2'b11) ? 2'b00 : counter + 1'b1;
      if (register_a == 0) begin
        status_flags[0] <= 1;
      end else begin
        status_flags[0] <= 0;
      end
      out_processed_value <= register_a;
      out_status <= status_flags;
    end
  end
endmodule
class MyBaseClass;
  int m_data;
  function new(int val);
    this.m_data = val;
  endfunction
  virtual function int get_data();
    return this.m_data;
  endfunction
  function void set_data(int val);
    this.m_data = val;
  endfunction
endclass
class MyDerivedClass extends MyBaseClass;
  int m_offset;
  function new(int val, int offset);
    super.new(val);
    this.m_offset = offset;
  endfunction
  virtual function int get_data();
    return super.get_data() + this.m_offset;
  endfunction
endclass
module ClassHandler (
  input logic clk,
  input logic reset,
  input bit enable_class_op,
  input int input_val_class,
  input MyBaseClass my_object_in,
  output int output_val_class,
  output logic class_instantiated_flag
);
  MyBaseClass my_object_handle;
  int internal_result;
  always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
      my_object_handle = null;
      internal_result <= 0;
      class_instantiated_flag <= 1'b0;
    end else begin
      my_object_handle = my_object_in;
      if (enable_class_op && my_object_handle != null) begin
        my_object_handle.set_data(input_val_class);
        internal_result <= my_object_handle.get_data();
      end else if (my_object_handle != null) begin
        internal_result <= my_object_handle.get_data();
      end else begin
        internal_result <= 0;
      end
      class_instantiated_flag <= (my_object_handle != null);
    end
  end
  assign output_val_class = internal_result;
endmodule
module DataStructureProcessor (
  input logic clk,
  input logic rst_n,
  input byte data_in_byte,
  input bit push_en,
  input bit pop_en,
  input int addr_assoc_array,
  output byte data_out_byte,
  output bit queue_empty_flag,
  output int assoc_array_val_out
);
  byte my_queue[$];
  byte assoc_array_map[int];
  logic [7:0] loop_accum;
  string string_example;
  task automatic process_data;
    input byte in_b;
    output byte out_b;
    int k;
    begin
      out_b = in_b;
      assoc_array_map[10] = 25;
      assoc_array_map[addr_assoc_array] = in_b;
      loop_accum = 0;
      for (k=0; k<10; k++) begin
        loop_accum += k;
      end
      string_example = "Task processing data.";
    end
  endtask
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      data_out_byte <= 0;
      my_queue.delete();
      queue_empty_flag <= 1'b1;
      assoc_array_map.delete();
      assoc_array_val_out <= 0;
      loop_accum <= 0;
      string_example = "";
    end else begin
      process_data(data_in_byte, data_out_byte);
      if (push_en) begin
        my_queue.push_back(data_in_byte);
      end
      if (pop_en && my_queue.size() > 0) begin
        void'(my_queue.pop_front());
      end
      queue_empty_flag <= (my_queue.size() == 0);
      if (assoc_array_map.exists(addr_assoc_array)) begin
        assoc_array_val_out <= assoc_array_map[addr_assoc_array];
      end else begin
        assoc_array_val_out <= 0;
      end
    end
  end
endmodule
interface SimpleBus (input logic clk, input logic rst);
  logic [31:0] address;
  logic [31:0] data;
  logic write_en;
  logic read_en;
  logic ready;
  modport MASTER (output address, output data, output write_en, output read_en, input ready);
  modport SLAVE (input address, input data, input write_en, input read_en, output ready);
endinterface
module InterfaceUser (
  input logic clk_in,
  input logic rst_in,
  input logic [31:0] master_data_in,
  input bit master_write_req,
  output logic [31:0] slave_data_out,
  output bit master_ready_status
);
  SimpleBus bus_if_instance (.clk(clk_in), .rst(rst_in));
  always_comb begin
    bus_if_instance.MASTER.address = 32'hABCD_1234;
    bus_if_instance.MASTER.data = master_data_in;
    bus_if_instance.MASTER.write_en = master_write_req;
    bus_if_instance.MASTER.read_en = ~master_write_req;
    master_ready_status = bus_if_instance.MASTER.ready;
    bus_if_instance.SLAVE.ready = 1'b1;
    slave_data_out = bus_if_instance.SLAVE.data;
  end
endmodule
module AssertionChecker (
  input logic clk,
  input logic reset_n,
  input logic request,
  input logic grant,
  output logic error_flag
);
  logic latched_error_status;
  logic [1:0] grant_delay_counter;
  logic pending_request;
  property p_grant_follows_request;
    @(posedge clk) (request && reset_n) |-> ##[1:2] grant;
  endproperty
  a_grant_check: assert property (p_grant_follows_request);
  always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      latched_error_status <= 1'b0;
      grant_delay_counter <= 2'b00;
      pending_request <= 1'b0;
    end else begin
      if (request && !pending_request) begin
        pending_request <= 1'b1;
        grant_delay_counter <= 2'b00;
      end else if (pending_request) begin
        if (grant) begin
          pending_request <= 1'b0;
          latched_error_status <= 1'b0;
        end else if (grant_delay_counter == 2'b11) begin
          latched_error_status <= 1'b1;
          pending_request <= 1'b0;
        end else begin
          grant_delay_counter <= grant_delay_counter + 1'b1;
        end
      end else begin
        latched_error_status <= 1'b0;
      end
    end
  end
  assign error_flag = latched_error_status;
endmodule
module TypeCaster (
  input logic [31:0] in_raw_data,
  input bit cast_to_float_en,
  input bit static_cast_en,
  output int out_int_val,
  output real out_real_val
);
  typedef struct packed {
    logic [15:0] low;
    logic [15:0] high;
  } two_halves_s;
  function automatic int convert_to_int(two_halves_s val_s);
    return {val_s.high, val_s.low};
  endfunction
  function automatic real bitwise_cast_to_real(logic [31:0] bits);
    return $bitstoshortreal(bits);
  endfunction
  logic [31:0] temp_integer_value;
  real temp_real_value;
  two_halves_s split_data;
  always_comb begin
    split_data.low = in_raw_data[15:0];
    split_data.high = in_raw_data[31:16];
    if (static_cast_en) begin
      temp_integer_value = convert_to_int(split_data);
    end else begin
      temp_integer_value = in_raw_data;
    end
    if (cast_to_float_en) begin
      temp_real_value = bitwise_cast_to_real(in_raw_data);
    end else begin
      temp_real_value = 0.0;
    end
    out_int_val = temp_integer_value;
    out_real_val = temp_real_value;
  end
endmodule
