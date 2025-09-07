typedef union packed {
  logic [15:0] u8;
  logic [15:0] u16;
} union_t;
module submod(input logic clk, input logic rst, output logic sub_out);
  assign sub_out = clk & rst;
endmodule
module mod_cells(input logic clk, input logic rst, output logic done);
  submod inst1(.clk(clk), .rst(rst), .sub_out(done));
endmodule
module mod_design(input logic in1, input logic in2, output logic out1);
  logic a;
  logic [3:0] bus;
  logic signed [7:0] signed_bus;
  logic temp;
  always_comb begin
    a = in1 | in2;
    bus = {4{in1}};
    signed_bus = in2 ? 8'shFF : 8'sh00;
    temp = a & bus[0];
    out1 = temp;
  end
endmodule
module mod_params #(parameter int P1 = 8, parameter bit [3:0] P2 = 4'd3) (input logic clk, output logic [P1-1:0] out);
  assign out = clk ? {P1{1'b1}} : {P1{1'b0}};
endmodule
module mod_methods(input logic a, input logic b, output logic r);
  function logic myfunc(input logic x, input logic y);
    myfunc = x ^ y;
  endfunction
  function automatic int cover_func(input logic en, output int cnt);
    if (en) cnt = 1; else cnt = 0;
    return cnt;
  endfunction
  always_comb begin
    logic [31:0] cov;
    r = myfunc(a, b);
    cov = cover_func(r, cov);
  end
endmodule
module mod_enums(input logic [1:0] sel, output logic [7:0] val);
  typedef enum logic [1:0] { S0 = 2'd0, S1 = 2'd1, S2 = 2'd2, S3 = 2'd3 } states_t;
  states_t state;
  always_comb begin
    state = states_t'(sel);
    case (state)
      S0: val = 8'hAA;
      S1: val = 8'hBB;
      S2: val = 8'hCC;
      default: val = 8'hFF;
    endcase
  end
endmodule
module mod_structs(input logic clk, output logic [31:0] packed_val);
  typedef struct {
    bit a;
    int b;
  } unpacked_s;
  typedef struct packed {
    logic [7:0] f1;
    logic [15:0] f2;
  } packed_s;
  typedef struct {
    bit [3:0] arr[2];
  } packed_arr_s;
  typedef struct {
    logic [7:0] dyn_arr[];
  } dyn_s;
  typedef struct {
    int assoc[string];
  } assoc_s;
  unpacked_s us;
  packed_s ps;
  packed_arr_s pas;
  dyn_s ds;
  assoc_s as;
  class rand_cls;
    rand bit [3:0] crand;
    rand int signed sval;
    constraint c1 { crand inside {[4:8]}; }
  endclass
  rand_cls rc;
  always_ff @(posedge clk) begin
    rc = new();
    ds.dyn_arr = new[4];
    ds.dyn_arr[0] = 8'hFF;
    as.assoc["key"] = 123;
  end
  always_comb begin
    packed_val = {ps.f1, ps.f2};
  end
endmodule
module mod_union(input logic a, output union_t out_union);
  union_t u;
  always_comb begin
    u.u16 = a ? 16'h1234 : 16'hABCD;
    out_union = u;
  end
endmodule
module mod_arrays(input logic clk, output logic [7:0] outq);
  logic [7:0] q[$];
  logic [7:0] arr_dyn[];
  logic [7:0] arr_assoc[string];
  always_ff @(posedge clk) begin
    q.push_back(clk ? 8'h1 : 8'h2);
    arr_dyn = new[4];
    arr_dyn[0] = 8'hFF;
    arr_assoc["k"] = 8'hAA;
    outq = q[0];
  end
endmodule
module mod_gen(input logic a, output logic [3:0] out [3:0]);
  genvar i;
  generate
    for (i = 0; i < 4; i = i + 1) begin : gen_blk
      assign out[i] = i;
    end
  endgenerate
endmodule
module mod_dpi(input logic [15:0] d, output logic [15:0] r);
  import "DPI-C" function int dpi_in(int v);
  import "DPI-C" function void dpi_ex(int v, int u);
  integer tmp;
  always_comb begin
    tmp = dpi_in(d);
    dpi_ex(tmp, tmp);
    r = tmp;
  end
endmodule
module mod_tasks(input logic a, input logic b, output logic r);
  function automatic logic task_func(input logic x, input logic y);
    task_func = x & y;
  endfunction
  task automatic tsk(input logic [3:0] in1, output logic [3:0] out1);
    out1 = in1 + 1;
  endtask
  always_comb begin
    logic [3:0] tmp;
    tsk({3'b101, a}, tmp);
    r = task_func(tmp[0], b);
  end
endmodule
module mod_classcover(input logic clk, output logic [3:0] o);
  class myclass;
    rand bit [3:0] a;
    constraint c { a < 8; }
  endclass
  import "DPI-C" function int dpi_cl(int v);
  myclass inst;
  always_ff @(posedge clk) begin
    inst = new();
    inst.randomize();
    o = inst.a;
  end
endmodule
