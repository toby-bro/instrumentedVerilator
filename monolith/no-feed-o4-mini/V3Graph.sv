module bitwise_ops(input wire [3:0] a, b, output wire [3:0] y_and, y_or, y_xor, y_not);
  assign y_and = a & b;
  assign y_or  = a | b;
  assign y_xor = a ^ b;
  assign y_not = ~a;
endmodule
module arithmetic_ops(input logic signed [7:0] a, b, output logic signed [7:0] sum, diff, prod, divi);
  assign sum  = a + b;
  assign diff = a - b;
  assign prod = a * b;
  assign divi = a / b;
endmodule
module mux_4to1(input wire [1:0] sel, input wire [7:0] in0, in1, in2, in3, output wire [7:0] out);
  assign out = (sel == 2'b00) ? in0 :
               (sel == 2'b01) ? in1 :
               (sel == 2'b10) ? in2 :
                               in3;
endmodule
module case_mux(input logic [1:0] sel, input logic [3:0] in, output logic [3:0] out);
  always_comb begin
    case (sel)
      2'b00: out = in;
      2'b01: out = in + 1;
      2'b10: out = in - 1;
      default: out = 4'hF;
    endcase
  end
endmodule
module generate_assign #(parameter N = 4) (input logic [N-1:0] data_in, output logic [N-1:0] data_out);
  genvar i;
  generate
    for (i = 0; i < N; i = i + 1) begin : gen_loop
      assign data_out[i] = data_in[i];
    end
  endgenerate
endmodule
module nested_generate #(parameter WIDTH = 8, parameter DEPTH = 2) (input logic [WIDTH-1:0] din, output logic [WIDTH-1:0] dout);
  genvar j;
  generate
    for (j = 0; j < DEPTH; j = j + 1) begin : depth_loop
      genvar k;
      for (k = 0; k < WIDTH; k = k + 1) begin : width_loop
        assign dout[k] = din[k] ^ (j != 0);
      end
    end
  endgenerate
endmodule
module function_example(input wire [3:0] a, b, output wire [3:0] out);
  function automatic [3:0] f(input [3:0] x, input [3:0] y);
    begin
      f = (x & y) ^ ~(x | y);
    end
  endfunction
  assign out = f(a, b);
endmodule
module multidim_array(input logic [7:0] a [0:1][0:1], output logic [7:0] sum0, sum1);
  assign sum0 = a[0][0] + a[0][1];
  assign sum1 = a[1][0] + a[1][1];
endmodule
module assoc_array_example(input logic [3:0] idx, input logic [7:0] in_val, output logic [7:0] out_val);
  logic [7:0] arr[int];
  always_comb begin
    arr[1]    = 8'hA1;
    arr[2]    = 8'hB2;
    arr[idx]  = in_val;
    out_val   = arr[idx];
  end
endmodule
module queue_example(input logic clk, input logic rst, input logic [7:0] din, output logic [7:0] dout);
  logic [7:0] q[$];
  logic [7:0] head;
  always_ff @(posedge clk) begin
    if (rst) begin
      q.delete();
      head = 8'h00;
    end else begin
      q.push_back(din);
      head = q.pop_front();
    end
  end
  assign dout = head;
endmodule
module random_class_example(input logic clk, input logic rst, output logic [7:0] out_rand);
  class RandC;
    rand bit [7:0] data;
    function new();
      data = 8'h00;
    endfunction
    function void post_randomize();
      data = data + 1;
    endfunction
  endclass
  RandC rc;
  always_ff @(posedge clk) begin
    if (rst) begin
      rc = new();
    end else begin
      rc.randomize();
      out_rand = rc.data;
    end
  end
endmodule
module param_if #(parameter EN = 1) (input logic in_sig, output logic out_sig);
  generate
    if (EN) begin
      assign out_sig = in_sig;
    end else begin
      assign out_sig = ~in_sig;
    end
  endgenerate
endmodule
module latch_example(input logic en, input logic d, output logic q);
  always_latch begin
    if (en)
      q = d;
    else
      q = q;
  end
endmodule
