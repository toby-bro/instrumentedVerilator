package common_types_pkg;
  typedef enum logic [1:0] {
    OP_ADD = 2'b00,
    OP_SUB = 2'b01,
    OP_AND = 2'b10,
    OP_OR   = 2'b11
  } alu_op_e;
  typedef struct packed {
    logic [7:0] data;
    bit         valid;
  } packet_t;
  typedef struct {
    int    id;
    string name;
    real   value;
  } item_info_t;
  class FifoItem;
    int addr;
    logic [15:0] payload;
    function new(int a, logic [15:0] p);
      this.addr = a;
      this.payload = p;
    endfunction
    function void update_payload(logic [15:0] new_p);
      this.payload = new_p;
    endfunction
  endclass
endpackage
interface fifo_interface (input bit clk, input bit rst);
  import common_types_pkg::*;
  logic                 wr_en;
  logic                 rd_en;
  logic [15:0]          wr_data;
  logic [15:0]          rd_data;
  logic                 full;
  logic                 empty;
  logic [3:0]           fill_level;
  modport controller (
    output wr_en,
    output rd_en,
    output wr_data,
    input  rd_data,
    input  full,
    input  empty,
    input  fill_level,
    input  clk,
    input  rst
  );
  modport memory (
    input  wr_en,
    input  rd_en,
    input  wr_data,
    output rd_data,
    output full,
    output empty,
    output fill_level,
    input  clk,
    input  rst
  );
endinterface
module SimpleALU #(
  parameter DATA_WIDTH = 8
) (
  input  logic [DATA_WIDTH-1:0] a_i,
  input  logic [DATA_WIDTH-1:0] b_i,
  input  common_types_pkg::alu_op_e op_i,
  output logic [DATA_WIDTH-1:0] result_o,
  output bit                     zero_o
);
  logic [DATA_WIDTH-1:0] alu_result;
  bit                    is_zero;
  always_comb begin
    alu_result = '0;
    is_zero    = 1'b0;
    case (op_i)
      common_types_pkg::OP_ADD: alu_result = a_i + b_i;
      common_types_pkg::OP_SUB: alu_result = a_i - b_i;
      common_types_pkg::OP_AND: alu_result = a_i & b_i;
      common_types_pkg::OP_OR:  alu_result = a_i | b_i;
      default:                  alu_result = 'x;
    endcase
    if (alu_result == '0) begin
      is_zero = 1'b1;
    end else begin
      is_zero = 1'b0;
    end
  end
  assign result_o = alu_result;
  assign zero_o   = is_zero;
endmodule
module DataProcessor (
  input  bit                      clk,
  input  bit                      rst_n,
  input  common_types_pkg::packet_t input_packet_i,
  output common_types_pkg::packet_t processed_packet_o,
  output common_types_pkg::item_info_t output_info_o,
  input  int                      max_elements_i,
  output int                      processed_count_o
);
  import common_types_pkg::*;
  localparam MAX_PKTS = 4;
  packet_t packet_buffer [MAX_PKTS];
  int current_idx;
  int processed_cnt_reg;
  item_info_t local_info;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      for (int i = 0; i < MAX_PKTS; i++) begin
        packet_buffer[i] = '{data: '0, valid: 1'b0};
      end
      current_idx       <= 0;
      processed_cnt_reg <= 0;
      local_info        <= '{id: 0, name: "", value: 0.0};
    end else begin
      if (input_packet_i.valid) begin
        if (current_idx < MAX_PKTS) begin
          packet_buffer[current_idx] <= input_packet_i;
          current_idx                <= current_idx + 1;
          processed_cnt_reg          <= processed_cnt_reg + 1;
          local_info.id              <= local_info.id + 1;
          local_info.name            = "Processed";
          local_info.value           = $itor(input_packet_i.data) * 2.5;
        end
      end
      if (processed_cnt_reg > max_elements_i) begin
        processed_cnt_reg <= 0;
      end
    end
  end
  assign processed_packet_o = packet_buffer[0];
  assign output_info_o      = local_info;
  assign processed_count_o  = processed_cnt_reg;
endmodule
module CompleteFifo (
  input  bit             clk,
  input  bit             rst,
  input  logic [15:0]    data_to_write_i,
  input  bit             request_write_i,
  input  bit             request_read_i,
  output logic [15:0]    data_read_o,
  output bit             fifo_op_done_o
);
  fifo_interface fifo_bus (.clk(clk), .rst(rst));
  localparam FIFO_DEPTH = 8;
  localparam ADDR_WIDTH = $clog2(FIFO_DEPTH);
  logic [15:0] fifo_mem [FIFO_DEPTH-1:0];
  logic [ADDR_WIDTH-1:0] wr_ptr_q, rd_ptr_q;
  logic [ADDR_WIDTH:0]   fill_count_q;
  logic fifo_full_internal;
  logic fifo_empty_internal;
  typedef enum logic [1:0] {
    STATE_IDLE,
    STATE_WRITE,
    STATE_READ,
    STATE_ERROR
  } fsm_state_e;
  fsm_state_e current_state, next_state;
  logic       op_done_reg;
  assign fifo_bus.rd_data    = fifo_mem[rd_ptr_q];
  assign fifo_bus.full       = fifo_full_internal;
  assign fifo_bus.empty      = fifo_empty_internal;
  assign fifo_bus.fill_level = fill_count_q[3:0];
  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      wr_ptr_q     <= '0;
      rd_ptr_q     <= '0;
      fill_count_q <= '0;
      current_state <= STATE_IDLE;
    end else begin
      if (fifo_bus.wr_en && !fifo_full_internal) begin
        fifo_mem[wr_ptr_q] <= fifo_bus.wr_data;
        wr_ptr_q           <= wr_ptr_q + 1;
        fill_count_q       <= fill_count_q + 1;
      end
      if (fifo_bus.rd_en && !fifo_empty_internal) begin
        rd_ptr_q     <= rd_ptr_q + 1;
        fill_count_q <= fill_count_q - 1;
      end
      current_state <= next_state;
    end
  end
  assign fifo_full_internal = (fill_count_q == FIFO_DEPTH);
  assign fifo_empty_internal = (fill_count_q == 0);
  function automatic fsm_state_e calculate_next_state(fsm_state_e current, bit req_wr, bit req_rd, bit full, bit empty);
    fsm_state_e func_next_state;
    case (current)
      STATE_IDLE: begin
        if (req_wr && !full) func_next_state = STATE_WRITE;
        else if (req_rd && !empty) func_next_state = STATE_READ;
        else func_next_state = STATE_IDLE;
      end
      STATE_WRITE: begin
        if (full) func_next_state = STATE_ERROR;
        else func_next_state = STATE_IDLE;
      end
      STATE_READ: begin
        if (empty) func_next_state = STATE_ERROR;
        else func_next_state = STATE_IDLE;
      end
      STATE_ERROR: func_next_state = STATE_IDLE;
      default:     func_next_state = STATE_IDLE;
    endcase
    return func_next_state;
  endfunction
  task automatic do_fifo_op(fsm_state_e state, input logic [15:0] write_data);
    fifo_bus.wr_en   = 1'b0;
    fifo_bus.rd_en   = 1'b0;
    fifo_bus.wr_data = '0;
    op_done_reg      = 1'b0;
    case (state)
      STATE_WRITE: begin
        fifo_bus.wr_en   = 1'b1;
        fifo_bus.wr_data = write_data;
        op_done_reg      = 1'b1;
      end
      STATE_READ: begin
        fifo_bus.rd_en   = 1'b1;
        op_done_reg      = 1'b1;
      end
      default: begin
      end
    endcase
  endtask
  always_comb begin
    next_state = calculate_next_state(current_state, request_write_i, request_read_i, fifo_bus.full, fifo_bus.empty);
    do_fifo_op(current_state, data_to_write_i);
  end
  assign data_read_o    = fifo_bus.rd_data;
  assign fifo_op_done_o = op_done_reg;
endmodule
module ComplexRegisters (
  input  bit                           clk,
  input  bit                           rst,
  input  int                           address_i,
  input  logic [31:0]                  write_data_i,
  input  bit                           write_en_i,
  output logic [31:0]                  read_data_o,
  output common_types_pkg::FifoItem    fifo_item_o
);
  import common_types_pkg::*;
  logic [31:0] register_map [int];
  FifoItem fifo_items_queue [];
  FifoItem current_fifo_item_comb;
  logic [31:0] local_read_data;
  FifoItem local_fifo_item;
  always_comb begin
    current_fifo_item_comb = null;
    if (address_i inside {100, 200, 300}) begin
      current_fifo_item_comb = new(address_i, write_data_i[15:0]);
      current_fifo_item_comb.update_payload(write_data_i[31:16]);
    end
    if (register_map.exists(address_i)) begin
      local_read_data = register_map[address_i];
    end else begin
      local_read_data = '0;
    end
    if (fifo_items_queue.size() > 0) begin
      local_fifo_item = fifo_items_queue[0];
    end else begin
      local_fifo_item = current_fifo_item_comb;
    end
  end
  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      foreach (register_map[idx]) begin
        register_map.delete(idx);
      end
      fifo_items_queue = new[0];
    end else begin
      if (write_en_i) begin
        register_map[address_i] = write_data_i;
      end
      if (current_fifo_item_comb != null) begin
        int q_current_size;
        q_current_size = fifo_items_queue.size();
        fifo_items_queue = new[q_current_size + 1](fifo_items_queue);
        fifo_items_queue[q_current_size] = current_fifo_item_comb;
      end
    end
  end
  assign read_data_o = local_read_data;
  assign fifo_item_o = local_fifo_item;
endmodule
module VectorMultiplier #(
  parameter VECTOR_SIZE = 4,
  parameter DATA_WIDTH  = 8
) (
  input  logic signed [DATA_WIDTH-1:0]  vector_a_i [VECTOR_SIZE],
  input  logic signed [DATA_WIDTH-1:0]  vector_b_i [VECTOR_SIZE],
  output logic signed [2*DATA_WIDTH-1:0] result_vector_o [VECTOR_SIZE],
  output logic signed [2*DATA_WIDTH-1:0] dot_product_o
);
  logic signed [2*DATA_WIDTH-1:0] product_temp [VECTOR_SIZE];
  logic signed [2*DATA_WIDTH-1:0] dot_prod_reg;
  function automatic logic signed [2*DATA_WIDTH-1:0] element_multiply (
    logic signed [DATA_WIDTH-1:0] val_a,
    logic signed [DATA_WIDTH-1:0] val_b
  );
    return val_a * val_b;
  endfunction
  task automatic accumulate_dot_product (
    input logic signed [2*DATA_WIDTH-1:0] products [VECTOR_SIZE],
    output logic signed [2*DATA_WIDTH-1:0] final_dot_product
  );
    logic signed [2*DATA_WIDTH-1:0] sum;
    sum = '0;
    foreach (products[i]) begin
      sum += products[i];
    end
    final_dot_product = sum;
  endtask
  always_comb begin
    for (int i = 0; i < VECTOR_SIZE; i++) begin
      product_temp[i] = element_multiply(vector_a_i[i], vector_b_i[i]);
    end
    accumulate_dot_product(product_temp, dot_prod_reg);
  end
  assign result_vector_o = product_temp;
  assign dot_product_o   = dot_prod_reg;
endmodule
