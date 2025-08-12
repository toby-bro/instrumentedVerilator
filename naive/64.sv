class MyClass;
  int val;
  function new(int v = 0);
    val = v;
  endfunction
  function int inc();
    inc = ++val;
  endfunction
endclass
typedef enum logic [1:0] {S0 = 2'b00, S1 = 2'b01, S2 = 2'b10, S3 = 2'b11} state_t;
typedef struct { logic [3:0] a; logic [3:0] b; state_t st; } my_struct_t;
module simple_ff(input  logic clk, rst, d, output logic q);
  always_ff @(posedge clk or posedge rst) begin
    if (rst)
      q <= 1'b0;
    else
      q <= d;
  end
endmodule
module comb_add(input  logic [3:0] a, b, output logic [4:0] sum);
  assign sum = a + b;
endmodule
module param_mac #(
  parameter int WIDTH = 8
)(
  input  logic [WIDTH-1:0] x, y,
  output logic [2*WIDTH-1:0] product
);
  genvar i;
  generate
    for (i = 0; i < WIDTH; i = i + 1) begin : bit_and
      assign product[i] = x[i] & y[i];
    end
  endgenerate
endmodule
module struct_logic(
  input  logic [3:0] in1, in2,
  input  state_t      sel,
  output logic [3:0] out
);
  function my_struct_t pack();
    my_struct_t s;
    s.a = in1;
    s.b = in2;
    s.st = sel;
    return s;
  endfunction
  my_struct_t tmp;
  always_comb begin
    tmp = pack();
    case (tmp.st)
      S0: out = tmp.a;
      S1: out = tmp.b;
      default: out = tmp.a ^ tmp.b;
    endcase
  end
endmodule
module class_inst(
  input  logic clk, rst,
  output logic [7:0] out
);
  MyClass obj;
  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      obj = new(0);
      out <= 0;
    end else begin
      out <= obj.inc();
    end
  end
endmodule
module fn_logic(
  input  logic [7:0] a, b,
  output logic [7:0] y
);
  function logic [7:0] combine(logic [7:0] p, logic [7:0] q);
    combine = p ^ q;
  endfunction
  assign y = combine(a, b);
endmodule
module dynamic_array_inst(
  input  logic clk, rst,
  output int    sum
);
  int arr[];
  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      arr = new[4];
      sum <= 0;
    end else begin
      sum <= 0;
      for (int i = 0; i < 4; i++) begin
        arr[i] = i;
        sum <= sum + arr[i];
      end
    end
  end
endmodule
