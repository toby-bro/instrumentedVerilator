package pkg1;
  typedef struct packed { logic [1:0] a; logic b; } my_t;
endpackage
interface if1(input logic clk);
  logic [3:0] data;
  modport mp (input clk, input data);
endinterface
class cls1;
  int data;
  function new(int d); data = d; endfunction
  function int get(); return data; endfunction
endclass
module simple(input logic [3:0] a, output logic [3:0] b);
  assign b = a + 1;
endmodule
module proc_mod(input logic clk, input logic rst, output logic [3:0] cnt);
  always_ff @(posedge clk or posedge rst) begin
    if (rst) cnt <= 0;
    else cnt <= cnt + 1;
  end
endmodule
module case_mod(input logic [1:0] sel, input logic x, input logic y, output logic z);
  always_comb begin
    unique case (sel)
      2'b00: z = x & y;
      2'b01: z = x | y;
      2'b1?: z = x ^ y;
      default: z = 1'b0;
    endcase
  end
endmodule
module gen_loop #(parameter int N = 4) (input logic [N-1:0] in, output logic [N-1:0] out);
  genvar i;
  generate
    for (i = 0; i < N; i++) begin
      assign out[i] = in[N-1-i];
    end
  endgenerate
endmodule
module gen_if #(parameter ENABLE = 1) (input logic a, output logic b);
  generate
    if (ENABLE) begin
      assign b = a;
    end else begin
      assign b = ~a;
    end
  endgenerate
endmodule
module use_pkg_mod(input pkg1::my_t in, output pkg1::my_t out);
  assign out = in;
endmodule
module use_if_mod(if1.mp port, output logic [3:0] out);
  always_comb out = port.data;
endmodule
module func_task(input logic a, output logic f);
  function logic myfunc(input logic x);
    return ~x;
  endfunction
  task mytask(output logic y);
    y = myfunc(a);
  endtask
  always_comb begin
    mytask(f);
  end
endmodule
module multi_array(input logic [3:0] a, output logic [3:0] b);
  logic [7:0] arr [0:1];
  assign arr[0] = {4'b1010, a};
  assign b = arr[0][3:0];
endmodule
module multi_dim(input logic [3:0] idx, output logic [7:0] val);
  logic [7:0] mem [0:15];
  assign val = mem[idx];
endmodule
module localparam_mod(input logic a, output logic b);
  localparam int P = 5;
  assign b = a ^ P[0];
endmodule
module class_inst(input logic clk, output logic ready);
  cls1 c;
  always_ff @(posedge clk) begin
    if (!c) c = new(8);
    ready <= (c.get() == 8);
  end
endmodule
