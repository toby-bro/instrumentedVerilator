class MyErrorGuard;
  bit error;
  function new();
    error = 0;
  endfunction
  function bit isError(input bit hard, input bit supp);
    if (hard) return 1;
    return (~supp);
  endfunction
endclass
module mod_enum(input logic [3:0] sel, output logic [7:0] code);
  typedef enum logic [3:0] {
    EC_MIN     = 4'd0,
    EC_ERROR   = 4'd1,
    EC_FATAL   = 4'd2,
    EC_WARNING = 4'd3,
    EC_INFO    = 4'd4
  } ErrorCode_t;
  ErrorCode_t ec;
  function logic [7:0] ascii(input ErrorCode_t c);
    case (c)
      EC_MIN:     ascii = "0";
      EC_ERROR:   ascii = "E";
      EC_FATAL:   ascii = "F";
      EC_WARNING: ascii = "W";
      EC_INFO:    ascii = "I";
      default:    ascii = "?";
    endcase
  endfunction
  always_comb begin
    ec   = ErrorCode_t'(sel);
    code = ascii(ec);
  end
endmodule
module mod_class(input logic hard, input logic supp, output logic err);
  always_comb begin
    MyErrorGuard c = new();
    err = c.isError(hard, supp);
  end
endmodule
module mod_assertion(input logic clk, input logic rst_n, input logic [7:0] data, output logic [7:0] out);
  logic [7:0] mem [0:15];
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
      out <= 8'd0;
    else
      out <= mem[data];
  end
  assert property (@(posedge clk) disable iff (!rst_n) (data < 8'hFF));
endmodule
module mod_dynamic(input logic [3:0] idx, input logic [7:0] val, output logic [7:0] out);
  logic [7:0] dyn_array [];
  logic [7:0] queue_q [$];
  logic [7:0] assoc_array [int];
  initial begin
    dyn_array = new[4];
    dyn_array[0] = 8'd1; dyn_array[1] = 8'd2;
    dyn_array[2] = 8'd3; dyn_array[3] = 8'd4;
    queue_q.push_back(8'd5);
    queue_q.push_front(8'd6);
    assoc_array[10] = 8'd7;
  end
  always_comb begin
    if (idx < dyn_array.size())
      out = dyn_array[idx];
    else if (queue_q.size() > 0)
      out = queue_q.pop_back();
    else
      out = assoc_array.exists(10) ? assoc_array[10] : val;
  end
endmodule
module mod_coverage(input logic clk, input logic sig, output logic cover_hit, output logic o_sig);
  logic other_sig;
  covergroup cg @(posedge clk);
    coverpoint sig;
    coverpoint other_sig;
    cross sig, other_sig;
  endgroup
  cg cg_inst = new();
  always_ff @(posedge clk) begin
    other_sig   <= ~sig;
    cg_inst.sample();
    cover_hit   <= sig && other_sig;
    o_sig       <= other_sig;
  end
endmodule
module mod_union_struct(input logic [15:0] in, output logic [7:0] low, output logic [15:0] high_ext);
  typedef struct packed {
    logic [7:0] high;
    logic [7:0] low8;
  } pair_t;
  typedef union packed {
    logic [15:0] word;
    pair_t       p;
  } u_t;
  u_t u;
  always_comb begin
    u.word      = in;
    low         = u.p.low8;
    high_ext    = {8'hFF, u.p.high};
  end
endmodule
module mod_generate #(parameter N = 4) (input logic [N-1:0] in, output logic [N-1:0] out);
  genvar i;
  generate
    for (i = 0; i < N; i = i + 1) begin : gen_loop
      assign out[i] = in[N-1-i];
    end
  endgenerate
endmodule
interface my_if(input logic clk);
  logic sig;
  clocking cb @(posedge clk);
    input  sig;
    output sig;
  endclocking
  modport mp (input sig, output sig);
endinterface
module mod_if(input logic clk, my_if.mp intf, output logic sampled);
  always_ff @(posedge clk) begin
    sampled <= intf.sig;
  end
endmodule
module mod_event(input logic clk, input logic trigger, output logic done);
  event ev;
  always_ff @(posedge clk) begin
    if (trigger) -> ev;
  end
  always @(ev) begin
    done = 1'b1;
  end
endmodule
module mod_mailbox(input logic clk, input logic req, input logic [7:0] data_in, output logic [7:0] data_out);
  mailbox mbx;
  initial mbx = new();
  always_ff @(posedge clk) begin
    if (req) mbx.put(data_in);
    if (mbx.num() > 0)
      mbx.get(data_out);
    else
      data_out <= 8'd0;
  end
endmodule
