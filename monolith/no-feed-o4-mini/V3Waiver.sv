module enum_struct(input logic [1:0] in, output logic [1:0] out);
  typedef enum logic [1:0] {A=2'b00, B=2'b01, C=2'b10, D=2'b11} myEnum_t;
  typedef struct packed { logic [3:0] a; integer b; } myStruct_t;
  myEnum_t e_var;
  myStruct_t s_var;
  always_comb begin
    s_var.a = in;
    s_var.b = in;
    e_var   = myEnum_t'(in);
    case (e_var)
      A: out = s_var.a;
      B: out = s_var.b[1:0];
      C: out = 2'b10;
      default: out = 2'b11;
    endcase
  end
endmodule
module param_cst
  #(parameter int P = 3, parameter string S = "hello")
  (input bit clk, input bit rst, output logic [P:0] out);
  localparam int LP = P * 2;
  assign out = rst ? {LP{1'b1}} : {P+1{clk}};
endmodule
module func_task(input logic [7:0] a, input logic [7:0] b, output logic [7:0] sum, output logic [7:0] diff);
  function automatic logic [7:0] add(input logic [7:0] x, input logic [7:0] y);
    add = x + y;
  endfunction
  task automatic sub(input logic [7:0] x, input logic [7:0] y, output logic [7:0] z);
    z = x - y;
  endtask
  always_comb begin
    sum  = add(a, b);
    sub(a, b, diff);
  end
endmodule
module gen_if_loop(input logic clk, output logic [3:0] result);
  genvar i;
  generate
    if (1) begin : gen1
      logic [3:0] tmp;
      for (i = 0; i < 4; i = i + 1) begin : gen2
        assign tmp[i] = clk ^ i[0];
      end
      assign result = tmp;
    end else begin : gen3
      assign result = 4'hF;
    end
  endgenerate
endmodule
module class_module(input logic clk, input logic [3:0] in, output logic [3:0] out);
  class C;
    rand bit [3:0] val;
    function void do_it(input bit [3:0] x);
      this.val = x;
    endfunction
  endclass
  C c_inst;
  always_ff @(posedge clk) begin
    c_inst = new;
    c_inst.do_it(in);
    out <= c_inst.val;
  end
endmodule
module iface_modport(input logic sig, output logic flag_out);
  interface I(input logic s);
    logic flag;
    modport M (input s, output flag);
  endinterface
  I intf(sig);
  always_comb begin
    intf.flag = sig;
    flag_out    = intf.flag;
  end
endmodule
package my_pkg;
  function int mul(input int a, input int b);
    return a * b;
  endfunction
endpackage
module pkg_use(input logic [3:0] a, input logic [3:0] b, output logic [7:0] mul_out);
  always_comb begin
    mul_out = my_pkg::mul(a, b);
  end
endmodule
module cover_assert(input logic clk, output logic flag);
  covergroup cg @(posedge clk);
    coverpoint flag { bins zero = {1'b0}; bins one = {1'b1}; }
  endgroup
  cg cg_inst = new;
  always_ff @(posedge clk) begin
    flag       <= ~flag;
    cg_inst.sample();
  end
endmodule
module assertions(input logic clk, input logic reset, output logic pass);
  property p1 @(posedge clk) disable iff(reset) (reset == 0) |-> ##1 clk;
  assert property (p1) else pass <= 1'b0;
  always_ff @(posedge clk or posedge reset) begin
    if (reset) pass <= 1'b1;
  end
endmodule
module dyn_q_str(input logic valid, output logic ready);
  string        str_arr [];
  int           dyn_arr [];
  int           queue_arr[$];
  int           assoc_arr[string];
  mailbox       mb = new();
  event         ev;
  always_comb begin
    if (valid) begin
      str_arr.push_back("world");
      dyn_arr.push_back(valid);
      queue_arr.push_back(valid);
      assoc_arr["key"] = valid;
      mb.put(dyn_arr.size());
      ->ev;
      ready = 1;
    end else begin
      ready = 0;
    end
  end
endmodule
package pkg_extra;
  typedef union packed { logic [7:0] byte; logic [1:0] nibble[4]; } utype_t;
  typedef struct { string name; int id; } stype_t;
endpackage
module pkg_extra_use(input logic [7:0] in, output logic [7:0] out);
  pkg_extra::utype_t uvar;
  pkg_extra::stype_t svar;
  always_comb begin
    uvar.byte = in;
    svar.name = "id";
    svar.id   = in[3:0];
    out       = uvar.byte + svar.id;
  end
endmodule
