class Packet;
  rand bit [7:0] header;
  function new();
  endfunction
  function bit [7:0] process(bit [7:0] d);
    return d ^ header;
  endfunction
endclass
module mod_params #(parameter N = 8)(input logic [N-1:0] in, output logic [N-1:0] out);
  localparam M = N * 2;
  wire [M-1:0] w;
  genvar i;
  generate
    for (i = 0; i < N; i = i + 1) begin
      assign w[i] = in[i];
    end
  endgenerate
  assign out = w[N-1:0];
endmodule
module mod_ff(input logic clk, input logic rst, input logic d, output logic q);
  always_ff @(posedge clk or posedge rst) begin
    if (rst)
      q <= 1'b0;
    else
      q <= d;
  end
endmodule
module mod_struct_union(input logic [7:0] a, output logic [7:0] u_out);
  typedef struct packed { logic [3:0] hi; logic [3:0] lo; } half_t;
  typedef union packed { logic [7:0] full; half_t parts; } data_u;
  data_u u;
  always_comb begin
    u.parts.hi = a[7:4];
    u.parts.lo = a[3:0];
    u_out = u.full;
  end
endmodule
module mod_enum(input logic [1:0] sel, output logic [7:0] data);
  typedef enum logic [1:0] { CMD_READ = 2'b00, CMD_WRITE = 2'b01, CMD_IDLE = 2'b10 } cmd_e;
  cmd_e cmd;
  always_comb begin
    case (sel)
      CMD_READ:  data = 8'hA5;
      CMD_WRITE: data = 8'h5A;
      default:   data = 8'hFF;
    endcase
  end
endmodule
module mod_function(input logic [3:0] a, input logic [3:0] b, output logic [4:0] sum);
  function automatic logic [4:0] add5(input logic [3:0] x, input logic [3:0] y);
    add5 = x + y;
  endfunction
  always_comb sum = add5(a, b);
endmodule
module mod_assert(input logic clk, input logic en, output logic ok);
  always_ff @(posedge clk) begin
    ok <= en;
  end
  property p_check;
    @(posedge clk) en |-> ok;
  endproperty
  assert property (p_check);
endmodule
module mod_class(input logic [7:0] x, output logic [7:0] y);
  Packet pkt;
  always_comb begin
    pkt = new();
    pkt.header = 8'hFF;
    y = pkt.process(x);
  end
endmodule
module mod_multidim(input logic [3:0] a [0:1], output logic [3:0] b [0:1]);
  integer i;
  always_comb begin
    for (i = 0; i < 2; i = i + 1)
      b[i] = a[1 - i];
  end
endmodule
module mod_array_gen #(parameter WIDTH = 4, LEN = 4)(input logic [WIDTH-1:0] din [0:LEN-1], output logic [WIDTH-1:0] dout [0:LEN-1]);
  genvar j;
  generate
    for (j = 0; j < LEN; j = j + 1) begin : genblk
      assign dout[j] = din[j] + j;
    end
  endgenerate
endmodule
