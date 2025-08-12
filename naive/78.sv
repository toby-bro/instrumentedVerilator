interface simple_if(input logic clk);
  logic data;
  modport master (input clk, input data);
endinterface
module enum_mod(input logic [1:0] in, output logic out);
  typedef enum logic [1:0] {IDLE=2'b00, BUSY=2'b01, DONE=2'b10} state_t;
  state_t state;
  always_comb begin
    case (in)
      IDLE: state = BUSY;
      BUSY: state = DONE;
      DONE: state = IDLE;
      default: state = IDLE;
    endcase
    out = (state == DONE);
  end
endmodule
module struct_mod(input logic [7:0] in, output logic [3:0] out);
  typedef struct packed { logic [3:0] hi; logic [3:0] lo; } nibble_t;
  nibble_t n;
  always_comb begin
    n = '{hi: in[7:4], lo: in[3:0]};
    out = n.hi ^ n.lo;
  end
endmodule
module union_mod(input logic [7:0] in, output logic [7:0] out);
  typedef union packed { logic [7:0] full; struct packed { logic [3:0] hi; logic [3:0] lo; } half; } u_t;
  u_t u;
  always_comb begin
    u.full = in;
    out = {u.half.lo, u.half.hi};
  end
endmodule
module param_mod #(parameter int W = 8)(input logic [W-1:0] in, output logic parity);
  localparam int HALF = W/2;
  logic [HALF-1:0] lo, hi;
  always_comb begin
    hi = in[W-1:HALF];
    lo = in[HALF-1:0];
    parity = ^{hi, lo};
  end
endmodule
module generate_mod #(parameter bit EN = 1)(input logic [3:0] din, output logic [3:0] dout);
  genvar i;
  generate
    for (i = 0; i < 4; i = i + 1) begin : gen_loop
      if (EN) assign dout[i] = ~din[i];
      else    assign dout[i] =  din[i];
    end
  endgenerate
endmodule
module func_mod(input logic [7:0] a, input logic [7:0] b, output logic [7:0] sum);
  function logic [7:0] add8(input logic [7:0] x, input logic [7:0] y);
    add8 = x + y;
  endfunction
  assign sum = add8(a, b);
endmodule
module seq_assert_mod(input logic clk, input logic rst, input logic in, output logic err);
  property p_edge;
    @(posedge clk) disable iff (rst) in |-> ##1 in;
  endproperty
  logic assertion_pass;
  always_ff @(posedge clk) begin
    assert property (p_edge) else assertion_pass <= 1'b0;
    err <= ~assertion_pass;
  end
endmodule
module class_inst_mod(input logic clk, input logic [3:0] in, output logic [3:0] out);
  class simple_c;
    rand logic [3:0] v;
    function logic [3:0] proc(input logic [3:0] x);
      proc = x ^ v;
    endfunction
    constraint c1 { v < 8; }
  endclass
  simple_c obj;
  always_ff @(posedge clk) begin
    obj = new();
    if (obj.randomize()) out <= obj.proc(in);
    else                 out <= in;
  end
endmodule
module rand_class_mod(input logic start, input logic [7:0] seed, output logic [7:0] rnd);
  class rng_c;
    rand bit [7:0] r;
    constraint c_range { r inside {[0:100]}; }
    function void seed_set(input bit [7:0] s);
    begin end
    endfunction
  endclass
  rng_c rng;
  always_comb begin
    rng = new();
    rng.seed_set(seed);
    if (start && rng.randomize()) rnd = rng.r;
    else                         rnd = seed;
  end
endmodule
module covergroup_mod(input logic clk, input logic [1:0] sig, output logic covered);
  covergroup cg @(posedge clk);
    coverpoint sig {
      bins low   = {2'b00};
      bins mid   = {2'b01, 2'b10};
      bins high  = {2'b11};
    }
  endgroup
  cg cg_inst = new();
  always_ff @(posedge clk) begin
    cg_inst.sample();
    covered <= 1'b1;
  end
endmodule
module interface_user_mod(input logic clk, input logic a, output logic b);
  simple_if if_inst(.clk(clk));
  always_comb begin
    b = if_inst.data & a;
  end
endmodule
