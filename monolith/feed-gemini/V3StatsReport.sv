package pkg_common_types;
  class base_agent_c;
    local int m_id;
    protected int m_data;
    function new(int id);
      m_id = id;
      m_data = 0;
    endfunction
    virtual function void process_cmd(logic [7:0] cmd, logic [7:0] val);
      m_data = val;
      if (cmd == 8'h01) m_data = m_data + 1;
      else m_data = m_data - 1;
    endfunction
    virtual function int get_result();
      return m_data;
    endfunction
  endclass
  class derived_agent1_c extends base_agent_c;
    function new(int id);
      super.new(id);
    endfunction
    virtual function void process_cmd(logic [7:0] cmd, logic [7:0] val);
      super.process_cmd(cmd, val);
      if (cmd == 8'h02) m_data = m_data * 2;
    endfunction
  endclass
  class derived_agent2_c extends base_agent_c;
    function new(int id);
      super.new(id);
    endfunction
    virtual function void process_cmd(logic [7:0] cmd, logic [7:0] val);
      super.process_cmd(cmd, val);
      if (cmd == 8'h03) m_data = m_data / 2;
    endfunction
  endclass
  class generic_processor_c #(type T = int);
    T value;
    function new(T initial_value);
      value = initial_value;
    endfunction
    function T modify(T input_val);
      return input_val + value;
    endfunction
  endclass
  typedef enum logic [1:0] {
    STATE_IDLE,
    STATE_ACTIVE,
    STATE_PAUSED,
    STATE_DONE
  } fsm_state_e;
  typedef struct packed {
    logic [7:0] data;
    logic [1:0] id;
    bit         valid;
  } packet_t;
  parameter int MAX_DEPTH = 8;
endpackage
module mod_data_types #(
  parameter int WIDTH = 16,
  parameter logic [3:0] START_VAL = 4'hA
) (
  input logic [WIDTH-1:0] in_data,
  output logic [WIDTH-1:0] out_data
);
  import pkg_common_types::*;
  logic [7:0] byte_var;
  int integer_var;
  real real_var;
  time time_var;
  string string_var = "HelloVerilator";
  byte signed_byte_var;
  logic [WIDTH-1:0] packed_array [4];
  logic unpacked_array [2][8];
  bit [3:0] fixed_size_array [3];
  int dynamic_array[];
  logic [15:0] dynamic_packed_array[][];
  bit [7:0] assoc_array_idx [string];
  int assoc_array_key [MAX_DEPTH];
  fsm_state_e current_state;
  fsm_state_e next_state;
  packet_t pkt_in;
  packet_t pkt_out;
  typedef union packed {
    logic [31:0] u_dword;
    struct packed {
      logic [15:0] u_word_h;
      logic [15:0] u_word_l;
    } s_words;
    logic [0:3][7:0] u_bytes;
  } my_union_t;
  my_union_t u_var;
  logic [WIDTH-1:0] data_wire;
  localparam int ADJUSTMENT_FACTOR = 10;
  always_comb begin
    byte_var = in_data[7:0];
    integer_var = in_data + ADJUSTMENT_FACTOR;
    real_var = $bitstoreal(in_data);
    time_var = $time;
    current_state = fsm_state_e'(in_data[1:0]);
    next_state = (current_state == STATE_DONE) ? STATE_IDLE : fsm_state_e'(current_state + 1);
    pkt_in.data = in_data[15:8];
    pkt_in.id = in_data[1:0];
    pkt_in.valid = in_data[0];
    pkt_out = pkt_in;
    data_wire = in_data;
    for (int i = 0; i < 4; i++) begin
      packed_array[i] = in_data + i;
    end
    unpacked_array[0][0] = in_data[0];
    if (in_data[2:0] > 0) begin
      dynamic_array = new[in_data[2:0]];
      dynamic_array[0] = integer_var;
    end else begin
      dynamic_array = new[1];
      dynamic_array[0] = 0;
    end
    assoc_array_idx["key1"] = in_data[7:0];
    assoc_array_key[MAX_DEPTH-1] = integer_var;
    u_var.u_dword = {in_data, in_data};
    if (u_var.s_words.u_word_h == 0) begin
      u_var.u_bytes[0] = 8'hFF;
    end
    out_data = data_wire + packed_array[0][WIDTH-1:0] + {{(WIDTH-2){1'b0}}, next_state};
  end
endmodule
module mod_procedural_logic (
  input logic clk,
  input logic rst_n,
  input logic [7:0] data_in,
  output logic [7:0] data_out,
  output logic [3:0] counter_out,
  output logic state_active
);
  import pkg_common_types::*;
  logic [7:0] reg_data;
  logic [3:0] counter;
  fsm_state_e current_fsm_state;
  function automatic logic [7:0] add_one(input logic [7:0] val);
    add_one = val + 8'h1;
  endfunction
  task automatic do_count(input int limit);
    for (int i = 0; i < limit; i++) begin
      counter = counter + 1;
    end
  endtask
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      reg_data <= 8'h00;
      counter <= 4'h0;
      current_fsm_state <= STATE_IDLE;
    end else begin
      reg_data <= add_one(data_in);
      do_count(1);
      case (current_fsm_state)
        STATE_IDLE: begin
          if (data_in > 0) current_fsm_state <= STATE_ACTIVE;
        end
        STATE_ACTIVE: begin
          if (counter >= 4'hF) current_fsm_state <= STATE_DONE;
          else current_fsm_state <= STATE_PAUSED;
        end
        STATE_PAUSED: begin
          current_fsm_state <= STATE_ACTIVE;
        end
        STATE_DONE: begin
          current_fsm_state <= STATE_IDLE;
        end
      endcase
    end
  end
  always_comb begin
    data_out = reg_data;
    state_active = (current_fsm_state == STATE_ACTIVE);
    if (data_in[0]) begin
      data_out = data_out | 8'hFF;
    end else begin
      data_out = data_out & 8'h00;
    end
  end
  logic [7:0] sum_bits;
  always_comb begin
    sum_bits = 0;
    for (int i = 0; i < 8; i++) begin
      if (data_in[i]) sum_bits = sum_bits + 1;
    end
  end
  assign counter_out = counter;
endmodule
module mod_parameterized_hierarchy #(
  parameter int NUM_STAGES = 3,
  parameter int DATA_BITS = 4
) (
  input logic [DATA_BITS-1:0] in_val,
  output logic [DATA_BITS-1:0] out_val
);
  logic [DATA_BITS-1:0] stage_data [NUM_STAGES];
  generate
    for (genvar i = 0; i < NUM_STAGES; i++) begin : gen_stage_inst
      if (i == 0) begin : first_stage
        assign stage_data[i] = in_val + 1;
      end else if (i == NUM_STAGES - 1) begin : last_stage
        assign stage_data[i] = stage_data[i-1] + 1;
      end else begin : middle_stage
        assign stage_data[i] = stage_data[i-1] + 2;
      end
    end
  endgenerate
  assign out_val = stage_data[NUM_STAGES-1];
endmodule
module mod_sv_classes (
  input logic clk,
  input logic rst_n,
  input logic [7:0] command_in,
  input logic [7:0] data_value,
  output logic [7:0] result_out
);
  import pkg_common_types::*;
  base_agent_c agent_h;
  derived_agent1_c agent1_h;
  derived_agent2_c agent2_h;
  generic_processor_c #(.T(logic [15:0])) proc_16bit_h;
  generic_processor_c #(.T(int)) proc_int_h;
  logic [7:0] local_result;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      agent1_h = new(1);
      agent2_h = new(2);
      proc_16bit_h = new(16'hAAAA);
      proc_int_h = new(100);
      agent_h = agent1_h;
      local_result <= 0;
    end else begin
      if (command_in == 8'h01) begin
        agent_h = agent1_h;
        agent_h.process_cmd(command_in, data_value);
        local_result <= agent_h.get_result()[7:0];
      end else if (command_in == 8'h02) begin
        agent_h = agent2_h;
        agent_h.process_cmd(command_in, data_value);
        local_result <= agent_h.get_result()[7:0];
      end else if (command_in == 8'h05) begin
        logic [15:0] processed_val;
        processed_val = proc_16bit_h.modify({8'h00, data_value});
        local_result <= processed_val[7:0];
      end else if (command_in == 8'h06) begin
        int processed_val_int;
        processed_val_int = proc_int_h.modify(data_value);
        local_result <= processed_val_int[7:0];
      end
    end
  end
  assign result_out = local_result;
endmodule
interface axi_lite_if (input logic clk, input logic rst_n);
  logic [31:0] awaddr;
  logic        awvalid;
  logic        awready;
  logic [31:0] wdata;
  logic [3:0]  wstrb;
  logic        wvalid;
  logic        wready;
  logic [1:0]  bresp;
  logic        bvalid;
  logic        bready;
  logic [31:0] araddr;
  logic        arvalid;
  logic        arready;
  logic [31:0] rdata;
  logic [1:0]  rresp;
  logic        rvalid;
  logic        rready;
  modport master (
    output awaddr, awvalid, wdata, wstrb, wvalid, araddr, arvalid, bready, rready,
    input awready, wready, bresp, bvalid, rdata, rresp, rvalid, clk, rst_n
  );
  modport slave (
    input awaddr, awvalid, wdata, wstrb, wvalid, araddr, arvalid, bready, rready,
    output awready, wready, bresp, bvalid, rdata, rresp, rvalid, clk, rst_n
  );
endinterface
module mod_interface_master (
  input logic clk,
  input logic rst_n,
  input logic [31:0] master_awaddr,
  output logic [31:0] master_rdata
);
  axi_lite_if axi_if (.clk(clk), .rst_n(rst_n));
  assign axi_if.awaddr = master_awaddr;
  assign axi_if.awvalid = 1'b1;
  assign axi_if.wdata = 32'hDEADBEEF;
  assign axi_if.wstrb = 4'hF;
  assign axi_if.wvalid = 1'b1;
  assign axi_if.araddr = master_awaddr;
  assign axi_if.arvalid = 1'b1;
  assign axi_if.bready = 1'b1;
  assign axi_if.rready = 1'b1;
  assign master_rdata = axi_if.rdata;
endmodule
module mod_interface_slave (
  input logic clk,
  input logic rst_n,
  input logic [31:0] slave_in_data,
  output logic slave_status
);
  axi_lite_if axi_if (.clk(clk), .rst_n(rst_n));
  logic [31:0] reg_data_slave;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      reg_data_slave <= 32'h0;
      axi_if.awready <= 1'b0;
      axi_if.wready <= 1'b0;
      axi_if.bvalid <= 1'b0;
      axi_if.bresp <= 2'b00;
      axi_if.arready <= 1'b0;
      axi_if.rvalid <= 1'b0;
      axi_if.rdata <= 32'h0;
      axi_if.rresp <= 2'b00;
    end else begin
      axi_if.awready <= axi_if.awvalid;
      axi_if.wready <= axi_if.wvalid;
      axi_if.arready <= axi_if.arvalid;
      if (axi_if.awvalid && axi_if.awready) begin
      end
      if (axi_if.wvalid && axi_if.wready) begin
        reg_data_slave <= axi_if.wdata;
        axi_if.bvalid <= 1'b1;
        axi_if.bresp <= 2'b00;
      end else begin
        axi_if.bvalid <= 1'b0;
      end
      if (axi_if.arvalid && axi_if.arready) begin
        axi_if.rvalid <= 1'b1;
        axi_if.rdata <= reg_data_slave;
        axi_if.rresp <= 2'b00;
      end else begin
        axi_if.rvalid <= 1'b0;
      end
    end
  end
  assign slave_status = (reg_data_slave == slave_in_data);
endmodule
module mod_assertions (
  input logic clk,
  input logic rst_n,
  input logic condition_a,
  input logic condition_b,
  output logic result_ok
);
  logic [1:0] state_reg;
  localparam S_IDLE = 2'b00;
  localparam S_STATE1 = 2'b01;
  localparam S_STATE2 = 2'b10;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      state_reg <= S_IDLE;
    end else begin
      case (state_reg)
        S_IDLE: if (condition_a) state_reg <= S_STATE1;
        S_STATE1: if (condition_b) state_reg <= S_STATE2;
                  else state_reg <= S_IDLE;
        S_STATE2: state_reg <= S_IDLE;
      endcase
    end
  end
  assert (condition_a || condition_b) else begin
    logic dummy_error_flag;
    dummy_error_flag = 1'b1;
  end
  property p_state_progression;
    @(posedge clk) (state_reg == S_IDLE) |=> (state_reg == S_STATE1);
  endproperty
  assert property (p_state_progression);
  property p_result_always_high;
    @(posedge clk) (state_reg == S_STATE2) |=> (result_ok == 1'b1);
  endproperty
  assert property (p_result_always_high);
  assume property (@(posedge clk) (condition_a && condition_b) |-> ##[1:2] (state_reg == S_STATE2));
  cover property (@(posedge clk) (state_reg == S_STATE1 && condition_b));
  assign result_ok = (state_reg == S_STATE2);
endmodule
module mod_enums_structs_typedefs #(
  parameter int MEM_SIZE = 16,
  parameter int ADDR_WIDTH = 4
) (
  input logic clk,
  input logic [ADDR_WIDTH-1:0] addr_in,
  input logic [7:0] data_wr,
  input logic write_en,
  output logic [7:0] data_rd
);
  import pkg_common_types::*;
  typedef struct packed {
    logic [7:0] version;
    logic [15:0] build_id;
    struct packed {
      logic [31:0] crc;
      logic [1:0] status;
    } hw_info;
  } device_info_t;
  device_info_t device_config;
  packet_t packet_buffer [MEM_SIZE];
  typedef enum logic [2:0] {
    MODE_NORMAL,
    MODE_DEBUG,
    MODE_ERROR,
    MODE_INIT
  } op_mode_e;
  op_mode_e current_op_mode;
  logic [7:0] internal_memory [MEM_SIZE];
  always_ff @(posedge clk) begin
    if (write_en) begin
      internal_memory[addr_in] <= data_wr;
      packet_buffer[addr_in].data <= data_wr;
      packet_buffer[addr_in].valid <= 1'b1;
      packet_buffer[addr_in].id <= addr_in[1:0];
    end
  end
  always_comb begin
    data_rd = internal_memory[addr_in];
    current_op_mode = MODE_NORMAL;
    if (packet_buffer[addr_in].valid && packet_buffer[addr_in].data == 8'hFF) begin
      current_op_mode = MODE_ERROR;
    end else if (addr_in >= MEM_SIZE/2) begin
      current_op_mode = MODE_DEBUG;
    end
    device_config.version = 8'h01;
    device_config.build_id = 16'h1234;
    device_config.hw_info.crc = 32'hCAFE_BABE;
    device_config.hw_info.status = (current_op_mode == MODE_ERROR) ? 2'b10 : 2'b00;
  end
endmodule
