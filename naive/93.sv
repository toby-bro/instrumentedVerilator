interface simple_if(input logic clk, input logic rst);
  logic req;
  logic ack;
endinterface
module comb_logic(input logic a, b, output logic y);
  always_comb begin
    if (a && !b)
      y = a ^ b;
    else
      y = ~(a | b);
  end
endmodule
module seq_ff(input logic clk, reset, input logic d, output logic q);
  always_ff @(posedge clk or posedge reset) begin
    if (reset)
      q <= 1'b0;
    else
      q <= d;
  end
endmodule
module mem_block(input logic clk, input logic write_enable, input logic [7:0] wdata, input logic [3:0] addr, output logic [7:0] rdata);
  reg [7:0] mem [0:15];
  always_ff @(posedge clk) begin
    if (write_enable)
      mem[addr] <= wdata;
  end
  assign rdata = mem[addr];
endmodule
module generate_block#(parameter WIDTH = 8, parameter DEPTH = 4)(input logic [WIDTH-1:0] in, output logic [WIDTH-1:0] out);
  genvar i;
  generate
    for (i = 0; i < WIDTH; i = i + 1) begin : gen_loop
      assign out[i] = in[i] ^ in[WIDTH-1-i];
    end
  endgenerate
endmodule
typedef enum logic [1:0] {IDLE = 2'b00, BUSY = 2'b01, DONE = 2'b10} state_t;
module enum_module(input logic clk, input logic start, output state_t status);
  state_t current;
  always_ff @(posedge clk) begin
    case (current)
      IDLE: if (start) current <= BUSY;
      BUSY: current <= DONE;
      DONE: current <= IDLE;
      default: current <= IDLE;
    endcase
  end
  assign status = current;
endmodule
typedef struct packed { logic a; logic [3:0] b; } my_struct_t;
typedef union packed { logic [4:0] u; my_struct_t s; } my_union_t;
module struct_union(input logic sel, input logic [3:0] din, output logic dout);
  my_struct_t st;
  my_union_t un;
  always_comb begin
    st.a = sel;
    st.b = din;
    un.s = st;
    dout = un.u[0];
  end
endmodule
interface simple_intf(input logic clk);
  logic sig;
  modport slave(input sig);
  modport master(output sig);
endinterface
module intf_mod(input logic en, output logic o);
  simple_intf i();
  simple_intf.master m = i;
  assign m.sig = en;
  assign o = m.sig;
endmodule
module class_module(input logic clk, input logic rst, input logic in, output logic out);
  class pkt;
    rand bit [7:0] data;
    function void set_data(bit [7:0] v); this.data = v; endfunction
  endclass
  pkt p;
  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      p = new();
      p.set_data(8'hFF);
      out <= 1'b0;
    end else begin
      out <= in ^ p.data[0];
    end
  end
endmodule
module cov_assert(input logic clk, input logic a, input logic b, output logic z);
  logic temp;
  always_comb temp = a & b;
  property p1;
    @(posedge clk) temp |-> ((!a) || b);
  endproperty
  assert property (p1);
  covergroup cg @(posedge z);
    coverpoint a;
    coverpoint b;
  endgroup
  cg cg_inst;
  assign z = temp;
endmodule
