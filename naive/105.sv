module SimpleArithLogic (
  input logic [7:0] in_a,
  input logic [7:0] in_b,
  input bit sel_op,
  output logic [7:0] out_result
);
  parameter ADD_OP = 1'b0;
  parameter SUB_OP = 1'b1;
  localparam MAX_VAL = 255;
  logic [7:0] intermediate_val;
  always_comb begin
    if (sel_op == ADD_OP) begin
      intermediate_val = in_a + in_b;
      if (intermediate_val > MAX_VAL) begin
        intermediate_val = MAX_VAL;
      end
    end else if (sel_op == SUB_OP) begin
      if (in_a > in_b) begin
        intermediate_val = in_a - in_b;
      end else begin
        intermediate_val = 0;
      end
    end else begin
      intermediate_val = 0;
    end
  end
  assign out_result = intermediate_val;
endmodule
module BasicFSM (
  input logic clk,
  input logic rst_n,
  input bit start_signal,
  output bit done_signal,
  output logic [1:0] current_state_out
);
  typedef enum logic [1:0] {
    STATE_IDLE,
    STATE_PROCESS,
    STATE_DONE
  } fsm_state_e;
  fsm_state_e current_state_q, next_state_n;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      current_state_q <= STATE_IDLE;
    end else begin
      current_state_q <= next_state_n;
    end
  end
  always_comb begin
    next_state_n = current_state_q;
    done_signal = 1'b0;
    case (current_state_q)
      STATE_IDLE: begin
        if (start_signal) begin
          next_state_n = STATE_PROCESS;
        end
      end
      STATE_PROCESS: begin
        next_state_n = STATE_DONE;
      end
      STATE_DONE: begin
        done_signal = 1'b1;
        if (!start_signal) begin
          next_state_n = STATE_IDLE;
        end
      end
      default: begin
        next_state_n = STATE_IDLE;
      end
    endcase
  end
  assign current_state_out = current_state_q;
endmodule
module ClassUsageExample (
  input logic clk,
  input logic rst_n,
  input int input_param,
  output int output_result
);
  class MyProcessor;
    local int internal_counter;
    function new();
      internal_counter = 100;
    endfunction
    function int process_value(int val);
      internal_counter = internal_counter + 1;
      return val * 2 + internal_counter;
    endfunction
  endclass
  MyProcessor proc_instance;
  int current_processed_val;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      proc_instance = new();
      current_processed_val <= 0;
    end else begin
      if (proc_instance == null) begin
        proc_instance = new();
      end
      current_processed_val <= proc_instance.process_value(input_param);
    end
  end
  assign output_result = current_processed_val;
endmodule
module MemoryAccessUnit (
  input logic clk,
  input logic rst_n,
  input logic [3:0] addr,
  input logic write_en,
  input logic [7:0] data_in,
  output logic [7:0] data_out
);
  logic [7:0] mem_array [0:15];
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      for (int i = 0; i < 16; i++) begin
        mem_array[i] <= 8'h00;
      end
    end else begin
      if (write_en) begin
        mem_array[addr] <= data_in;
      end
    end
  end
  assign data_out = mem_array[addr];
endmodule
module FuncTaskExecutor (
  input int val1,
  input int val2,
  input logic [1:0] mode,
  output int processed_val
);
  localparam ADD_MODE = 2'b00;
  localparam SUB_MODE = 2'b01;
  localparam MULT_MODE = 2'b10;
  function automatic int my_adder (int a, int b);
    return a + b;
  endfunction
  function automatic int my_subtractor (int a, int b);
    return a - b;
  endfunction
  task automatic my_multiplier (input int a, input int b, output int result);
    result = a * b;
  endtask
  logic [31:0] intermediate_result;
  always_comb begin
    case (mode)
      ADD_MODE: intermediate_result = my_adder(val1, val2);
      SUB_MODE: intermediate_result = my_subtractor(val1, val2);
      MULT_MODE: begin
        my_multiplier(val1, val2, intermediate_result);
      end
      default: intermediate_result = 0;
    endcase
  end
  assign processed_val = intermediate_result;
endmodule
module ConfigurableLogic (
  input logic [15:0] input_val,
  input bit config_enable,
  output logic [15:0] output_val
);
  logic [15:0] intermediate_val;
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : BIT_OP
      assign intermediate_val[i] = config_enable ? ~input_val[i] : input_val[i];
    end
  endgenerate
  assign output_val = intermediate_val;
endmodule
module DataPacketProcessor (
  input logic [31:0] packet_in,
  output logic [7:0] header_out,
  output logic [7:0] payload_len_out,
  output logic [15:0] data_out
);
  typedef struct packed {
    logic [7:0] header;
    logic [7:0] payload_length;
    logic [15:0] data_field;
  } packet_s;
  typedef union packed {
    packet_s  fields;
    logic [31:0] raw;
  } packet_u;
  packet_u current_packet;
  always_comb begin
    current_packet.raw = packet_in;
    header_out = current_packet.fields.header;
    payload_len_out = current_packet.fields.payload_length;
    data_out = current_packet.fields.data_field;
  end
endmodule
interface SimpleBus (
  input logic clk,
  input logic rst_n
);
  logic [7:0] addr;
  logic [7:0] data_in;
  logic [7:0] data_out;
  logic wr_en;
  logic rd_en;
  logic valid;
  modport Slave (
    input clk,
    input rst_n,
    input addr,
    input data_in,
    input wr_en,
    input rd_en,
    output data_out,
    output valid
  );
  modport Master (
    input clk,
    input rst_n,
    output addr,
    output data_in,
    input data_out,
    output wr_en,
    output rd_en,
    output valid
  );
endinterface
module BusUserSlaveSimplified (
  input logic clk,
  input logic rst_n,
  input logic [3:0] addr,
  input logic write_en,
  input logic read_en,
  input logic [7:0] data_in_bus,
  input logic [7:0] config_register_value,
  output logic [7:0] data_out_bus,
  output logic valid_out_bus,
  output logic [7:0] read_data_output
);
  logic [7:0] internal_register;
  logic valid_signal;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      internal_register <= 8'h00;
      valid_signal <= 1'b0;
    end else begin
      valid_signal <= 1'b0;
      if (write_en) begin
        if (addr == 4'h0) begin
          internal_register <= data_in_bus;
          valid_signal <= 1'b1;
        end
      end
    end
  end
  always_comb begin
    data_out_bus = 8'hXX;
    valid_out_bus = valid_signal;
    if (read_en) begin
      if (addr == 4'h0) begin
        data_out_bus = internal_register;
      end else if (addr == 4'h1) begin
        data_out_bus = config_register_value;
      end else begin
        data_out_bus = 8'hFF;
      end
      valid_out_bus = 1'b1;
    end
  end
  assign read_data_output = internal_register;
endmodule
