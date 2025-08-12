interface simple_if(input logic clk);
  wire a;
  modport master(inout a);
endinterface
module param_module #(parameter WIDTH = 8) (
  input  logic [WIDTH-1:0] in,
  output logic [WIDTH-1:0] out
);
  assign out = in;
endmodule
module gen_module (
  input  logic       sel,
  input  logic [3:0] din,
  output logic [3:0] dout
);
  genvar i;
  generate
    for (i = 0; i < 4; i = i + 1) begin : genblk
      assign dout[i] = sel ? din[i] : ~din[i];
    end
  endgenerate
endmodule
module interface_use (
  input  logic      clk,
  input  logic      din,
  output logic      dout
);
  simple_if iface(clk);
  assign iface.a = din;
  assign dout    = iface.a;
endmodule
module struct_union_module (
  input  logic [7:0] in,
  output logic [7:0] out
);
  typedef struct packed { logic [3:0] lo; logic [3:0] hi; } half_t;
  typedef union packed { logic [15:0] bits; logic signed [15:0] si; } data_u;
  function automatic half_t split(input logic [7:0] x);
    half_t tmp;
    tmp.lo = x[3:0];
    tmp.hi = x[7:4];
    return tmp;
  endfunction
  assign out = {split(in).hi, split(in).lo};
endmodule
module enum_module (
  input  logic sel,
  output logic [1:0] code
);
  typedef enum logic [1:0] {IDLE=2'b00, BUSY=2'b01, DONE=2'b10, ERROR=2'b11} state_t;
  state_t st;
  always_comb begin
    case (sel)
      1'b0: st = BUSY;
      default: st = DONE;
    endcase
    code = st;
  end
endmodule
module class_module (
  input  logic [3:0] a,
  input  logic [3:0] b,
  output logic [7:0] sum
);
  class Adder;
    function logic [7:0] add(input logic [3:0] x, input logic [3:0] y);
      return x + y;
    endfunction
  endclass
  Adder c;
  always_comb begin
    c = new();
    sum = c.add(a, b);
  end
endmodule
module assertion_module (
  input  logic clk,
  input  logic en,
  input  logic [7:0] data_in,
  output logic [7:0] data_out
);
  always_ff @(posedge clk) begin
    if (en) data_out <= data_in;
  end
  property p_no_zero;
    @(posedge clk) disable iff(!en) data_in != 8'h00;
  endproperty
  assert_p: assert property (p_no_zero);
endmodule
module function_module (
  input  logic [15:0] x,
  output logic [15:0] y
);
  function automatic logic [15:0] rev(input logic [15:0] val);
    integer i;
    rev = '0;
    for (i = 0; i < 16; i = i + 1)
      rev[i] = val[15-i];
  endfunction
  assign y = rev(x);
endmodule
module parameter_default_module #(
  parameter integer DEPTH = 16,
  parameter integer WIDTH = 4
) (
  input  logic [WIDTH-1:0] in,
  output logic [WIDTH-1:0] out
);
  reg [WIDTH-1:0] mem [0:DEPTH-1];
  always_comb begin
    out = mem[in];
  end
endmodule
