class MyClass;
  rand bit [3:0] data;
  function new(bit [3:0] init);
    data = init;
  endfunction
  function void incr();
    data++;
  endfunction
endclass
interface SimpleIf(input logic clk);
  logic a;
  logic b;
endinterface
module reg_ff(input logic clk, input logic rst, input logic d, output logic q);
  always_ff @(posedge clk or posedge rst) begin
    if (rst) q <= 1'b0;
    else     q <= d;
  end
endmodule
module comb_logic(input logic [3:0] a, input logic [3:0] b, output logic [4:0] sum, output logic gt);
  always_comb begin
    sum = a + b;
    gt  = (a > b);
  end
endmodule
module param_gen #(parameter WIDTH = 8, parameter N = 4)
  (input  logic [WIDTH-1:0] in,
   output logic [WIDTH-1:0] out);
  genvar i;
  generate
    for (i = 0; i < N; i = i + 1) begin : GEN_LOOP
      assign out[i] = in[i];
    end
    for (i = N; i < WIDTH; i = i + 1) begin : GEN_ZERO
      assign out[i] = 1'b0;
    end
  endgenerate
endmodule
module interface_mod(input logic clk, output logic out_flag);
  SimpleIf if_inst(.clk(clk));
  logic temp;
  always_ff @(posedge clk) begin
    temp <= if_inst.a & if_inst.b;
  end
  assign if_inst.b  = temp;
  assign out_flag   = temp;
endmodule
module class_mod(input logic [3:0] in, output logic [3:0] out);
  always_comb begin : CLASS_CB
    automatic MyClass c = new(in);
    c.incr();
    out = c.data;
  end
endmodule
module func_task_mod(input logic [3:0] x, output logic [7:0] y);
  function automatic logic [7:0] mult2(input logic [3:0] v);
    return v << 1;
  endfunction
  always_comb begin
    y = mult2(x);
  end
endmodule
module struct_mod(input logic [1:0] idx, input logic [7:0] val, output logic [7:0] out);
  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;
  pair_t arr [0:3];
  always_comb begin
    arr[idx].a = val;
    arr[idx].b = val + 8'h1;
    out = arr[idx].a + arr[idx].b;
  end
endmodule
module assertion_mod(input logic [3:0] in, output logic valid);
  always_comb begin
    valid = 1'b1;
    assert (in != 4'b0000) else valid = 1'b0;
  end
endmodule
