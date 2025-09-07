package my_pkg;
  typedef enum logic [1:0] { RED = 2'b00, GREEN = 2'b01, BLUE = 2'b10 } color_t;
  typedef struct packed { logic [7:0] a; logic [7:0] b; } duo_t;
endpackage
interface simple_if;
  logic sig;
  modport master (input sig);
  modport slave  (output sig);
endinterface
module gen_mod #(parameter int N = 4) (
  input  logic [N-1:0] din,
  output logic [N-1:0] dout
);
  genvar i;
  generate
    for (i = 0; i < N; i = i + 1) begin : gen_loop
      assign dout[i] = ~din[i];
    end
  endgenerate
endmodule
module struct_enum_mod (
  input  logic        clk,
  input  logic [7:0]  in,
  output logic [7:0]  out
);
  import my_pkg::*;
  always_ff @(posedge clk) begin
    duo_t st;
    color_t c;
    st.a = in;
    st.b = ~in;
    case (in[1:0])
      2'b00: c = RED;
      2'b01: c = GREEN;
      default: c = BLUE;
    endcase
    out = (c == BLUE) ? st.b : st.a;
  end
endmodule
module func_task_mod (
  input  logic clk,
  input  logic a,
  output logic b
);
  function logic invert(input logic x);
    invert = ~x;
  endfunction
  task copy_bit(input logic src, output logic dst);
    dst = src;
  endtask
  class cbit;
    rand logic val;
    function new(); endfunction
  endclass
  always_ff @(posedge clk) begin
    logic tmp;
    cbit obj;
    tmp = invert(a);
    copy_bit(tmp, b);
    obj = new();
    obj.randomize();
    b = b ^ obj.val;
  end
endmodule
module interface_mod (
  input  logic clk,
  simple_if.master master_if,
  output logic out
);
  always_ff @(posedge clk) begin
    out = master_if.sig;
  end
endmodule
module assertion_mod (
  input  logic clk,
  input  logic req,
  input  logic ack,
  output logic grant
);
  always_ff @(posedge clk) begin
    grant <= ~grant;
  end
  property p_req_to_grant;
    @(posedge clk) req |=> grant;
  endproperty
  assert property (p_req_to_grant);
endmodule
module covergroup_mod (
  input  logic clk,
  input  logic sig,
  output logic out
);
  covergroup cg @(posedge clk);
    coverpoint sig;
  endgroup
  cg cg_inst = new();
  always_ff @(posedge clk) begin
    out <= sig;
    cg_inst.sample();
  end
endmodule
module dpi_mod (
  input  logic clk,
  input  int   a,
  output int   b
);
  import "DPI-C" function int c_func(input int x);
  always_ff @(posedge clk) begin
    b <= c_func(a);
  end
endmodule
module random_mod (
  input  logic clk,
  output int   rnd
);
  class RandC;
    rand logic [3:0] v;
    function new(); endfunction
  endclass
  always_ff @(posedge clk) begin
    RandC obj;
    obj = new();
    obj.randomize();
    rnd <= obj.v;
  end
endmodule
