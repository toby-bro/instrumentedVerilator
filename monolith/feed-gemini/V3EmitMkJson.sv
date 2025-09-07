package common_types_pkg;
  typedef enum logic [1:0] {
    STATE_IDLE = 2'b00,
    STATE_READ = 2'b01,
    STATE_WRITE = 2'b10,
    STATE_ERROR = 2'b11
  } fsm_state_e;
  typedef struct packed {
    logic [7:0] data;
    logic [3:0] addr;
    logic       valid;
  } packet_s;
  typedef union packed {
    int         ival;
    logic [31:0] bits;
  } my_union_t;
  class MySimpleClass;
    int data_member;
    function new(int init_val);
      data_member = init_val;
    endfunction
    function int get_data();
      return data_member;
    endfunction
  endclass
endpackage
interface data_interface(input logic clk);
  logic [15:0] request_data;
  logic [7:0]  response_data;
  logic        request_valid;
  logic        response_ready;
  modport master (output request_data, output request_valid, input response_data, input response_ready, input clk);
  modport slave  (input request_data, input request_valid, output response_data, output response_ready, input clk);
endinterface
module data_processor #(
  parameter DATA_WIDTH = 16,
  parameter ADDR_WIDTH = 8
) (
  input  logic [DATA_WIDTH-1:0] in_data,
  input  logic [ADDR_WIDTH-1:0] in_addr,
  output logic [DATA_WIDTH-1:0] out_data
);
  import common_types_pkg::*;
  localparam MAX_VAL = (1 << DATA_WIDTH) - 1;
  fsm_state_e current_state;
  packet_s rx_packet;
  always_comb begin
    MySimpleClass my_instance;
    my_instance = new(in_data[7:0]);
    if (in_data > MAX_VAL / 2) begin
      out_data = my_instance.get_data() + in_addr;
      current_state = STATE_READ;
    end else begin
      out_data = in_data;
      current_state = STATE_IDLE;
    end
    rx_packet.data = in_data[7:0];
    rx_packet.addr = in_addr[3:0];
    rx_packet.valid = (in_data != 0);
  end
  function automatic logic [DATA_WIDTH-1:0] calculate_checksum(logic [DATA_WIDTH-1:0] value);
    logic [DATA_WIDTH-1:0] sum = 0;
    for (int i = 0; i < DATA_WIDTH; i++) begin
      sum = sum + value[i];
    end
    return sum;
  endfunction
  logic [DATA_WIDTH-1:0] checksum_val;
  assign checksum_val = calculate_checksum(in_data);
endmodule
module sequential_controller (
  input  logic clk,
  input  logic reset_n,
  input  logic start_op,
  output logic op_done,
  input  data_interface.master bus_if
);
  import common_types_pkg::*;
  logic [7:0] counter;
  logic       register_enable;
  my_union_t u_val;
  logic        master_rx_response_ready;
  logic [7:0]  master_rx_response_data;
  always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      counter <= 8'h00;
      op_done <= 1'b0;
    end else begin
      if (start_op) begin
        counter <= counter + 1;
        if (counter == 8'hFF) begin
          op_done <= 1'b1;
        end else begin
          op_done <= 1'b0;
        end
      end else begin
        op_done <= 1'b0;
      end
    end
  end
  generate
    if (8'hFF > 100) begin : gen_large_counter
      always_comb begin
        register_enable = (counter > 10);
      end
    end else begin : gen_small_counter
      always_comb begin
        register_enable = (counter > 5);
      end
    end
  endgenerate
  genvar i;
  for (i = 0; i < 4; i = i + 1) begin : gen_reg_array
    logic [3:0] my_reg;
    always_ff @(posedge clk) begin
      if (register_enable) begin
        my_reg <= bus_if.request_data[4*i +: 4]; 
      end
    end
  end
  always_comb begin
    u_val.ival = counter;
    bus_if.request_data = u_val.bits[15:0];
    bus_if.request_valid = start_op;
    master_rx_response_ready = bus_if.response_ready;
    master_rx_response_data = bus_if.response_data;
  end
  assert property (@(posedge clk) (start_op |-> counter != 0))
    else $error("Counter started with 0 when start_op is high");
endmodule
module memory_block (
  input  logic clk,
  input  logic wr_en,
  input  logic rd_en,
  input  logic [7:0] addr,
  input  logic [15:0] din,
  output logic [15:0] dout
);
  localparam MEM_DEPTH = 256;
  logic [15:0] mem [MEM_DEPTH-1:0];
  initial begin
    for (int i=0; i<MEM_DEPTH; i++) begin
      mem[i] = 16'hDEAD;
    end
  end
  task automatic write_mem(logic [7:0] address, logic [15:0] data);
    mem[address] = data;
  endtask
  task automatic read_mem(logic [7:0] address, output logic [15:0] data_out);
    data_out = mem[address];
  endtask
  always_ff @(posedge clk) begin
    if (wr_en) begin
      write_mem(addr, din);
    end
    if (rd_en) begin
      read_mem(addr, dout);
    end else begin
      dout <= 16'h0000;
    end
  end
  logic [15:0] latched_data;
  always_latch begin
    if (wr_en && addr == 8'h01) begin
      latched_data = din;
    end
  end
endmodule
module system_top_wrapper #(
  parameter TOP_ID = 32'hFEEDFACE
) (
  input  logic clk,
  input  logic reset_n,
  input  logic [15:0] main_input_data,
  input  logic [7:0]  main_input_addr,
  output logic [15:0] main_output_data,
  output logic        main_op_done
);
  import common_types_pkg::*;
  MySimpleClass top_level_class_instance;
  data_interface bus_if(.clk(clk));
  data_processor #(
    .DATA_WIDTH(16),
    .ADDR_WIDTH(8)
  ) u_data_processor (
    .in_data (main_input_data),
    .in_addr (main_input_addr),
    .out_data(main_output_data)
  );
  sequential_controller u_sequential_controller (
    .clk        (clk),
    .reset_n    (reset_n),
    .start_op   (main_input_data[0]),
    .op_done    (main_op_done),
    .bus_if     (bus_if)
  );
  memory_block u_memory_block (
    .clk    (clk),
    .wr_en  (main_input_data[1]),
    .rd_en  (main_input_data[2]),
    .addr   (main_input_addr),
    .din    (main_output_data), 
    .dout   (bus_if.response_data) 
  );
  always_comb begin
    top_level_class_instance = new(TOP_ID[7:0]);
  end
  fsm_state_e current_fsm_state;
  always_comb begin
    case (main_input_data[1:0])
      2'b00: current_fsm_state = STATE_IDLE;
      2'b01: current_fsm_state = STATE_READ;
      2'b10: current_fsm_state = STATE_WRITE;
      default: current_fsm_state = STATE_ERROR;
    endcase
  end
  logic slave_ready_status;
  assign slave_ready_status = bus_if.response_ready;
endmodule
