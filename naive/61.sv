module simple_assign(input logic a, b, output logic y);
  assign y = a & b;
endmodule
module func_module(input logic [3:0] a, b, output logic [4:0] sum);
  function logic [4:0] add_f(input logic [3:0] x, y);
    add_f = x + y;
  endfunction
  always_comb begin
    sum = add_f(a, b);
  end
endmodule
module seq_module(input logic clk, rst, input logic [7:0] d, output logic [7:0] q);
  always_ff @(posedge clk or posedge rst) begin
    if (rst)
      q <= '0;
    else begin
      integer i;
      for (i = 0; i < 8; i = i + 1)
        q[i] <= d[i];
    end
  end
endmodule
module latch_module(input logic en, d, output logic q);
  always_latch begin
    if (en)
      q = d;
  end
endmodule
module param_module#(parameter int WIDTH = 8)
  (input logic [WIDTH-1:0] in, output logic [WIDTH-1:0] out);
  localparam int HALF = WIDTH / 2;
  generate
    if (HALF > 0) begin : gen_half
      assign out = {in[HALF-1:0], in[WIDTH-1:HALF]};
    end else begin : gen_zero
      assign out = in;
    end
  endgenerate
endmodule
module struct_module(input logic clk, enable, output logic [15:0] packed_out);
  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } packed_struct_t;
  packed_struct_t ps;
  always_ff @(posedge clk) begin
    if (enable) begin
      ps.hi <= packed_out[15:8];
      ps.lo <= packed_out[7:0];
    end
  end
  assign packed_out = {ps.hi, ps.lo};
endmodule
module union_module(input logic sel, input logic [7:0] data, output logic [3:0] lo4, hi4);
  typedef union packed {
    logic [7:0] u_byte;
    struct packed { logic [3:0] nib1; logic [3:0] nib0; } n;
  } u_t;
  u_t u;
  always_comb begin
    u.u_byte = data;
    lo4 = u.n.nib0;
    hi4 = u.n.nib1;
  end
endmodule
module enum_case(input logic [1:0] sel, output logic val);
  typedef enum logic [1:0] { IDLE = 2'b00, BUSY = 2'b01, DONE = 2'b10 } state_t;
  always_comb begin
    case (sel)
      IDLE: val = 0;
      BUSY: val = 1;
      DONE: val = 1;
      default: val = 0;
    endcase
  end
endmodule
module class_module(input logic clk, trigger, output logic done);
  class worker;
    function new(); endfunction
    function void work(); endfunction
  endclass
  logic done_reg;
  always_ff @(posedge clk) begin
    if (trigger) begin
      static worker w = new();
      w.work();
      done_reg <= 1;
    end else
      done_reg <= 0;
  end
  assign done = done_reg;
endmodule
module mem_module(input logic clk, we, input logic [3:0] addr, input logic [7:0] din, output logic [7:0] dout);
  logic [7:0] mem [0:15];
  always_ff @(posedge clk) begin
    if (we)
      mem[addr] <= din;
  end
  assign dout = mem[addr];
endmodule
