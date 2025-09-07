package my_types_pkg;
  typedef enum logic [1:0] {
    STATE_IDLE,
    STATE_ACTIVE,
    STATE_DONE
  } fsm_state_e;
  typedef struct packed {
    logic [7:0] data_byte;
    bit         valid;
  } my_packet_t;
  parameter PKG_MAX_COUNT = 16;
  function automatic int add_one(int val);
    return val + 1;
  endfunction
  task automatic print_val(input int val);
  endtask
endpackage
module CombinationalProcessor #(
  parameter DATA_WIDTH = 8,
  parameter THRESHOLD = 10
) (
  input logic [DATA_WIDTH-1:0] in_data,
  input logic                  in_enable,
  output logic [DATA_WIDTH-1:0] out_result,
  output logic                  out_valid
);
  localparam LOCAL_OFFSET = 2;
  logic [DATA_WIDTH-1:0] temp_data;
  always_comb begin
    temp_data = in_data;
    if (in_enable) begin
      out_result = temp_data + LOCAL_OFFSET;
      out_valid  = (out_result > THRESHOLD);
    end else begin
      out_result = '0;
      out_valid  = 1'b0;
    end
  end
endmodule
module SequentialController (
  input  logic        clk,
  input  logic        rst_n,
  input  logic [7:0]  start_val,
  output logic [15:0] current_count,
  output logic        done_flag
);
  import my_types_pkg::*;
  fsm_state_e current_state, next_state;
  logic [15:0] counter_reg;
  logic [7:0]  data_mem [0:7];
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      current_state <= STATE_IDLE;
      counter_reg   <= '0;
      done_flag     <= 1'b0;
      foreach(data_mem[i]) data_mem[i] <= '0;
    end else begin
      current_state <= next_state;
      counter_reg   <= counter_reg + 1;
      if (current_state == STATE_ACTIVE && counter_reg == PKG_MAX_COUNT) begin
        done_flag <= 1'b1;
      end else begin
        done_flag <= 1'b0;
      end
      data_mem[add_one(start_val % 8)] <= start_val;
    end
  end
  always_comb begin
    next_state = current_state;
    case (current_state)
      STATE_IDLE:
        if (start_val != 0) next_state = STATE_ACTIVE;
      STATE_ACTIVE:
        if (counter_reg >= PKG_MAX_COUNT) next_state = STATE_DONE;
      STATE_DONE:
        next_state = STATE_IDLE;
      default:
        next_state = STATE_IDLE;
    endcase
    current_count = counter_reg;
  end
endmodule
interface AxiStream_if #(parameter DATA_W = 32) (input logic clk, input logic rst_n);
  logic [DATA_W-1:0] tdata;
  logic              tvalid;
  logic              tready;
  logic [7:0]        tuser;
  modport MASTER (
    output tdata,
    output tvalid,
    output tuser,
    input  tready
  );
  modport SLAVE (
    input  tdata,
    input  tvalid,
    input  tuser,
    output tready
  );
endinterface
module StreamSource (
  AxiStream_if.MASTER axi_if
);
  logic [31:0]  data_out;
  logic [7:0]   user_out;
  logic         valid_out;
  assign axi_if.tdata  = data_out;
  assign axi_if.tvalid = valid_out;
  assign axi_if.tuser  = user_out;
  always_comb begin
    data_out  = 32'hFEEDFACE;
    user_out  = 8'hAA;
    valid_out = 1'b1;
  end
endmodule
class MyDataPacket;
  rand bit [15:0] header;
  rand byte      payload_length;
  rand my_types_pkg::my_packet_t payload_data;
  constraint payload_c { payload_length inside {[1:255]}; }
  function new();
  endfunction
  function bit [15:0] get_header();
    return header;
  endfunction
  function byte get_payload_length();
    return payload_length;
  endfunction
endclass
module PacketGenerator (
  input  logic        clk,
  input  logic        rst_n,
  input  logic        gen_en,
  output logic [15:0] out_header,
  output byte         out_len,
  output logic [7:0]  out_data_byte,
  output bit          out_valid_bit
);
  MyDataPacket pkt;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      pkt           = null;
      out_header    <= '0;
      out_len       <= '0;
      out_data_byte <= '0;
      out_valid_bit <= 1'b0;
    end else begin
      if (gen_en && pkt == null) begin
        pkt = new();
      end
      if (pkt != null && gen_en) begin
        if (pkt.randomize() with { header inside {[16'h1000:16'hFFFF]}; }) begin
          out_header    <= pkt.get_header();
          out_len       <= pkt.get_payload_length();
          out_data_byte <= pkt.payload_data.data_byte;
          out_valid_bit <= pkt.payload_data.valid;
        end else begin
          out_header    <= '0;
          out_len       <= '0;
          out_data_byte <= '0;
          out_valid_bit <= 1'b0;
        end
      end else if (!gen_en && pkt != null) begin
        pkt = null;
        out_header    <= '0;
        out_len       <= '0;
        out_data_byte <= '0;
        out_valid_bit <= 1'b0;
      end
    end
  end
endmodule
module TopDesign (
  input  logic        sys_clk,
  input  logic        sys_rst_n,
  input  logic [7:0]  data_in_val,
  input  logic [31:0] stream_in_val,
  input  logic        stream_valid_in,
  input  logic        gen_pkt_en,
  output logic [15:0] final_count,
  output logic        overall_done,
  output logic [31:0] stream_out_data,
  output logic        stream_out_valid
);
  parameter CORE_DATA_W = 16;
  parameter CORE_THRESHOLD = 50;
  logic [CORE_DATA_W-1:0] proc_result;
  logic                   proc_valid;
  CombinationalProcessor #(
    .DATA_WIDTH (CORE_DATA_W),
    .THRESHOLD  (CORE_THRESHOLD)
  ) comb_inst (
    .in_data    (data_in_val),
    .in_enable  (1'b1),
    .out_result (proc_result),
    .out_valid  (proc_valid)
  );
  logic [15:0] seq_count;
  logic        seq_done;
  SequentialController seq_inst (
    .clk           (sys_clk),
    .rst_n         (sys_rst_n),
    .start_val     (data_in_val),
    .current_count (seq_count),
    .done_flag     (seq_done)
  );
  assign final_count = seq_count;
  assign overall_done = seq_done && proc_valid;
  logic [15:0] pkt_header;
  byte         pkt_len;
  logic [7:0]  pkt_data_byte;
  bit          pkt_valid_bit;
  PacketGenerator pkt_gen_inst (
    .clk           (sys_clk),
    .rst_n         (sys_rst_n),
    .gen_en        (gen_pkt_en),
    .out_header    (pkt_header),
    .out_len       (pkt_len),
    .out_data_byte (pkt_data_byte),
    .out_valid_bit (pkt_valid_bit)
  );
  AxiStream_if #(32) axi_stream_i (.clk(sys_clk), .rst_n(sys_rst_n));
  StreamSource stream_src_inst (
    .axi_if (axi_stream_i.MASTER)
  );
  assign stream_out_data  = axi_stream_i.tdata;
  assign stream_out_valid = axi_stream_i.tvalid && axi_stream_i.tready;
  always_comb begin
    axi_stream_i.tready = stream_valid_in;
  end
  genvar i;
  generate
    if (CORE_DATA_W > 8) begin : wide_data_path
      logic [CORE_DATA_W-1:0] wide_intermediate_signal;
      assign wide_intermediate_signal = proc_result * 2;
    end else begin : narrow_data_path
      logic [7:0] narrow_intermediate_signal;
      assign narrow_intermediate_signal = proc_result [7:0];
    end
    for (i = 0; i < 2; i++) begin : loop_processors
      logic [CORE_DATA_W-1:0] loop_data_in = data_in_val + i;
      logic [CORE_DATA_W-1:0] loop_result;
      logic                   loop_valid;
      CombinationalProcessor #(
        .DATA_WIDTH (CORE_DATA_W),
        .THRESHOLD  (CORE_THRESHOLD + i)
      ) loop_comb_inst (
        .in_data    (loop_data_in),
        .in_enable  (1'b1),
        .out_result (loop_result),
        .out_valid  (loop_valid)
      );
    end
  endgenerate
endmodule
