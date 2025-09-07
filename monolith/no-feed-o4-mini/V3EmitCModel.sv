module comb_mod(input logic a, input logic b, output logic y);
  assign y = a & b;
endmodule
module ff_mod(input logic clk, input logic rst, input logic d, output logic q);
  always_ff @(posedge clk or posedge rst)
    if (rst) q <= 1'b0;
    else     q <= d;
endmodule
module case_mod(input logic [1:0] sel, input logic [3:0] inbus, output logic [3:0] outbus);
  always_comb
    case (sel)
      2'd0:   outbus = inbus;
      2'd1:   outbus = inbus << 1;
      2'd2:   outbus = inbus >> 1;
      default: outbus = inbus ^ 4'hF;
    endcase
endmodule
module struct_mod(input logic [7:0] data_in, output logic [7:0] data_out);
  typedef struct packed { logic [3:0] high; logic [3:0] low; } nibble_t;
  nibble_t n;
  always_comb begin
    n.high    = data_in[7:4];
    n.low     = data_in[3:0];
    data_out  = {n.low, n.high};
  end
endmodule
module union_mod(input logic [7:0] byte_in, output logic [7:0] byte_out);
  union packed {
    logic [7:0]                    b;
    struct packed { logic [3:0] h; logic [3:0] l; } s;
  } u;
  always_comb begin
    u.b      = byte_in;
    u.s.h    = u.s.l + 1;
    byte_out = u.b;
  end
endmodule
module gen_mod #(parameter int MAX = 4) (
  input  logic [MAX-1:0] data,
  input  logic           en,
  output logic [MAX-1:0] outp
);
  genvar i;
  generate
    for (i = 0; i < MAX; i = i + 1) begin : genblk
      assign outp[i] = data[i] & en;
    end
  endgenerate
endmodule
module array_mod(
  input  logic        clk,
  input  logic [1:0]  addr,
  input  logic [7:0]  din,
  output logic [7:0]  dout
);
  logic [3:0][7:0] mem;
  always_ff @(posedge clk) begin
    mem[addr] <= din;
  end
  always_comb begin
    dout = mem[addr];
  end
endmodule
module class_mod(input logic clk, output logic done);
  class cproc;
    int a;
    function void init(int v);
      a = v;
    endfunction
    function int get();
      return a;
    endfunction
  endclass
  cproc proc;
  always_ff @(posedge clk) begin
    proc = new;
    proc.init(5);
    done <= (proc.get() == 5);
  end
endmodule
module dpi_mod(input logic [31:0] invar, output logic [31:0] outvar);
  import "DPI-C" function void dpi_func(input int a, output int b);
  always_comb begin
    int tmp;
    dpi_func(invar, tmp);
    outvar = tmp;
  end
endmodule
module rand_mod(input bit clk, input bit start, output bit valid);
  class rand_class;
    rand bit [3:0] r;
    constraint c { r inside {[1:10]}; }
    function void gen();
      assert(this.randomize());
    endfunction
  endclass
  rand_class rc;
  always_ff @(posedge clk) begin
    if (start) begin
      rc = new;
      rc.gen();
      valid <= (rc.r != 0);
    end
  end
endmodule
module cover_mod(input logic clk, input logic [1:0] a);
  covergroup cg @(posedge clk);
    coverpoint a {
      bins low  = {0};
      bins high = {[1:3]};
    }
  endgroup
  cg cg_inst = new();
endmodule
module clkblk_mod(input logic clk, input logic d, output logic q);
  clocking cb @(posedge clk);
    input d;
  endclocking
  always @(cb) begin
    q <= cb.d;
  end
endmodule
module tfunc_mod(input logic [3:0] a, output logic [3:0] f, output logic [3:0] t);
  function logic [3:0] func(input logic [3:0] x);
    return x + 1;
  endfunction
  task tsk(input logic [3:0] x, output logic [3:0] y);
    y = x - 1;
  endtask
  always_comb begin
    f = func(a);
    t = '0;
    tsk(a, t);
  end
endmodule
module ifgen_mod #(parameter FLAG = 1) (
  input  logic [3:0] in,
  output logic       out
);
  generate
    if (FLAG) begin
      assign out = |in;
    end else begin
      assign out = &in;
    end
  endgenerate
endmodule
